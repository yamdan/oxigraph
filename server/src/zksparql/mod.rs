mod builder;
mod context;
mod error;
mod nymizer;
mod parser;

use crate::{
    bad_request, base_url, query_results_content_negotiation,
    zksparql::{
        builder::{
            build_disclosed_subjects, build_extended_fetch_query, build_extended_prove_query,
            get_verifiable_credential, pseudonymize_metadata_and_proofs, TriplePatternWithGraphVar,
        },
        error::ZkSparqlError,
        nymizer::Pseudonymizer,
        parser::parse_zk_query,
    },
    HttpError, ReadForWrite,
};

use oxhttp::model::{Request, Response};
use oxigraph::{
    sparql::{QueryResults, QuerySolutionIter},
    store::Store,
};
use oxrdf::{Literal, Variable};
use rdf_proofs::{
    error::DeriveProofError,
    prover::{derive_proof, VcWithDisclosed},
};
use sparesults::QueryResultsSerializer;
use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};
use url::form_urlencoded;

const SUBJECT_GRAPH_SUFFIX: &str = ".subject";
const VC_VARIABLE_PREFIX: &str = "__vc";
const VP_VARIABLE: &str = "__vp";
const NYM_IRI_PREFIX: &str = "urn:nym:";
const CRYPTOSUITE_FOR_VP: &str = "bbs-term-proof-2023";

pub(crate) fn configure_and_evaluate_zksparql_query(
    store: &Store,
    encoded: &[&[u8]],
    mut query: Option<String>,
    request: &Request,
    proof_required: bool,
) -> Result<Response, HttpError> {
    for encoded in encoded {
        for (k, v) in form_urlencoded::parse(encoded) {
            if let "query" = k.as_ref() {
                if query.is_some() {
                    return Err(bad_request("Multiple query parameters provided"));
                }
                query = Some(v.into_owned())
            }
        }
    }
    let query = query.ok_or_else(|| bad_request("You should set the 'query' parameter"))?;
    let extended_results = if proof_required {
        evaluate_zksparql_prove(store, &query, request)
    } else {
        evaluate_zksparql_fetch(store, &query, request)
    };
    match extended_results? {
        QueryResults::Solutions(solutions) => {
            let format = query_results_content_negotiation(request)?;
            ReadForWrite::build_response(
                move |w| {
                    Ok((
                        QueryResultsSerializer::from_format(format)
                            .solutions_writer(w, solutions.variables().to_vec())?,
                        solutions,
                    ))
                },
                |(mut writer, mut solutions)| {
                    Ok(if let Some(solution) = solutions.next() {
                        writer.write(&solution?)?;
                        Some((writer, solutions))
                    } else {
                        writer.finish()?;
                        None
                    })
                },
                format.media_type(),
            )
        }
        _ => Err(bad_request("invalid query")),
    }
}

/// Evaluate a zk-SPARQL query on the Fetch endpoint
fn evaluate_zksparql_fetch(
    store: &Store,
    query: &str,
    request: &Request,
) -> Result<QueryResults, ZkSparqlError> {
    // 1. parse a zk-SPARQL query
    let parsed_zk_query = parse_zk_query(query, Some(&base_url(request)))?;
    println!("parsed_zk_query:\n{:#?}\n", parsed_zk_query);

    // 2. build an extended SELECT query to identify credentials to be disclosed
    let extended_query = build_extended_fetch_query(&parsed_zk_query)?;
    println!("extended fetch query:\n{:#?}\n", extended_query);
    println!("extended fetch query (SPARQL):\n{}\n", extended_query);

    // 3. execute the extended SELECT query to get extended fetch solutions
    store
        .query(extended_query)
        .map_err(ZkSparqlError::SparqlEvaluationError)
}

/// Evaluate a zk-SPARQL query on the Prove endpoint
fn evaluate_zksparql_prove(
    store: &Store,
    query: &str,
    request: &Request,
) -> Result<QueryResults, ZkSparqlError> {
    // 1. parse a zk-SPARQL query
    let parsed_zk_query = parse_zk_query(query, Some(&base_url(request)))?;
    println!("parsed_zk_query:\n{:#?}\n", parsed_zk_query);

    // 2. build an extended prove query to construct disclosed quads from credentials
    let (extended_query, extended_triple_patterns) = build_extended_prove_query(&parsed_zk_query)?;
    println!("extended prove query:\n{:#?}\n", extended_query);
    println!("extended prove query (SPARQL):\n{}\n", extended_query);

    // 3. execute the extended prove query to get extended prove solutions
    let extended_results = store.query(extended_query)?;
    let extended_solutions = match extended_results {
        QueryResults::Solutions(solutions) => solutions,
        _ => return Err(ZkSparqlError::ExtendedQueryFailed),
    };

    // 4. identify variables to be disclosed
    let mut disclosed_variables = parsed_zk_query.disclosed_variables;
    println!("disclosed variables:\n{:#?}\n", disclosed_variables);

    // 5. identify variables appearing as predicates in the given pattern
    let predicate_variables = extended_triple_patterns
        .iter()
        .filter_map(|TriplePatternWithGraphVar { triple_pattern, .. }| {
            match &triple_pattern.predicate {
                spargebra::term::NamedNodePattern::Variable(v) => Some(v),
                spargebra::term::NamedNodePattern::NamedNode(_) => None,
            }
        })
        .collect::<HashSet<_>>();
    println!("predicate_variables:\n{:#?}\n", predicate_variables);

    // 6. pseudonymize the solutions
    let mut nymizer = Pseudonymizer::default();
    let mut pseudonymized_solutions = nymizer.pseudonymize_solutions(
        extended_solutions,
        &disclosed_variables,
        &predicate_variables,
    )?;
    println!("pseudonymous solutions:\n{:#?}\n", pseudonymized_solutions);

    // 7. build disclosed subjects by assigning pseudonymous solutions to extended prove patterns
    let disclosed_subjects =
        build_disclosed_subjects(&pseudonymized_solutions, &extended_triple_patterns)?;
    println!("disclosed subjects:\n{:#?}\n", disclosed_subjects);

    // 8. get associated VCs
    let vcs = disclosed_subjects
        .keys()
        .map(|vc_graph_name| {
            Ok((
                vc_graph_name.clone(),
                get_verifiable_credential(vc_graph_name, store)?,
            ))
        })
        .collect::<Result<HashMap<_, _>, ZkSparqlError>>()?;

    // 9. pseudonymize VCs
    let mut disclosed_vcs = vcs
        .iter()
        .map(|(vc_graph_name, vc)| {
            Ok((
                vc_graph_name.clone(),
                pseudonymize_metadata_and_proofs(vc_graph_name, vc, store, &mut nymizer)?,
            ))
        })
        .collect::<Result<HashMap<_, _>, ZkSparqlError>>()?;
    println!("disclosed_vcs:\n{:#?}\n", disclosed_vcs);

    // 10. add disclosed subjects into pseudonymized VCs to get disclosed VCs
    for (vc_graph_name, quads) in disclosed_subjects {
        disclosed_vcs
            .entry(vc_graph_name)
            .and_modify(|vc| vc.subject = quads.into_iter().collect());
    }

    // 11. get deanonymization map
    let deanon_map = nymizer.get_deanon_map();

    // 12. build VP
    let vc_with_disclosed = vcs
        .iter()
        .map(|(vc_graph_name, vc)| {
            let disclosed_vc =
                disclosed_vcs
                    .get(vc_graph_name)
                    .ok_or(DeriveProofError::InternalError(
                        "VC and Disclosed VCs are unmatched".to_string(),
                    ))?;
            Ok(VcWithDisclosed::new(vc.into(), disclosed_vc.into()))
        })
        .collect::<Result<Vec<_>, ZkSparqlError>>()?;
    let vp = derive_proof(&vc_with_disclosed, &deanon_map)?;

    // 13. add VP to the solution
    disclosed_variables.push(Variable::new(VP_VARIABLE)?);
    for solution in &mut pseudonymized_solutions {
        solution.insert(
            Variable::new(VP_VARIABLE)?,
            Literal::new_simple_literal(
                vp.iter()
                    .map(|quad| quad.to_string() + " .\n")
                    .reduce(|l, r| format!("{}{}", l, r))
                    .unwrap_or("".to_string()),
            )
            .into(),
        );
    }

    // 14. return query results
    Ok(QueryResults::Solutions(QuerySolutionIter::new(
        Rc::new(disclosed_variables.clone()),
        Box::new(pseudonymized_solutions.into_iter().map(move |m| {
            Ok(disclosed_variables
                .iter()
                .map(|v| m.get(v).cloned())
                .collect::<Vec<_>>())
        })),
    )))
}
