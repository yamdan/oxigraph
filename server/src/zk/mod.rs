mod builder;
mod context;
mod error;
mod nymizer;
mod parser;
mod sig;

use crate::{
    bad_request, base_url, query_results_content_negotiation,
    zk::{
        builder::{
            build_disclosed_subjects, build_extended_fetch_query, build_extended_prove_query,
            deskolemize_deanon_map, deskolemize_vc_map, get_verifiable_credential,
            pseudonymize_metadata_and_proofs,
        },
        error::ZkSparqlError,
        nymizer::Pseudonymizer,
        parser::parse_zk_query,
        sig::derive_proof,
    },
    HttpError, ReadForWrite,
};

use oxhttp::model::{Request, Response};
use oxigraph::{
    sparql::{QueryResults, QuerySolutionIter},
    store::Store,
};
use sparesults::QueryResultsSerializer;
use std::{collections::HashMap, rc::Rc};
use url::form_urlencoded;

const SKOLEM_IRI_PREFIX: &str = "urn:bnid:";
const SUBJECT_GRAPH_SUFFIX: &str = ".subject";
const PROOF_GRAPH_SUFFIX: &str = ".proof";
const VC_VARIABLE_PREFIX: &str = "__vc";
const PSEUDONYMOUS_IRI_PREFIX: &str = "urn:bnid:";
// const PSEUDONYMOUS_VAR_PREFIX: &str = "urn:var:";
const PSEUDONYM_ALPHABETS: [char; 62] = [
    '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i',
    'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z', 'A', 'B',
    'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U',
    'V', 'W', 'X', 'Y', 'Z',
];
const CRYPTOSUITE_FOR_VP: &str = "bbsterm-2023";

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

    let disclosed_variables = parsed_zk_query.disclosed_variables;
    println!("disclosed variables:\n{:#?}\n", disclosed_variables);

    // 4. pseudonymize the extended prove solutions
    let mut nymizer = Pseudonymizer::default();
    let pseudonymized_solutions =
        nymizer.pseudonymize_solutions(extended_solutions, &disclosed_variables)?;
    println!("pseudonymous solutions:\n{:#?}\n", pseudonymized_solutions);

    // 5. build disclosed subjects by assigning pseudonymous solutions to extended prove patterns
    let disclosed_subjects =
        build_disclosed_subjects(&pseudonymized_solutions, &extended_triple_patterns)?;
    println!("disclosed subjects:\n{:#?}\n", disclosed_subjects);

    // 6. get associated VCs
    let vcs: HashMap<_, _> = disclosed_subjects
        .keys()
        .map(|cred_graph_id| {
            Ok((
                cred_graph_id.clone(),
                get_verifiable_credential(cred_graph_id, store)?,
            ))
        })
        .collect::<Result<_, ZkSparqlError>>()?;

    // 7. pseudonymize VCs
    let mut disclosed_vcs: HashMap<_, _> = vcs
        .iter()
        .map(|(cred_graph_id, vc)| {
            Ok((
                cred_graph_id.clone(),
                pseudonymize_metadata_and_proofs(cred_graph_id, vc, store, &mut nymizer)?,
            ))
        })
        .collect::<Result<_, ZkSparqlError>>()?;

    // 8. add disclosed subjects into pseudonymized VCs to get disclosed VCs
    for (graph_name, quads) in disclosed_subjects {
        disclosed_vcs
            .entry(graph_name)
            .and_modify(|vc| vc.subject = quads);
    }

    // 9. get deanonymization map
    let deanon_map = nymizer.get_deanon_map();

    // 10. build VP
    let _vp = derive_proof(
        &deskolemize_vc_map(&vcs)?,
        &deskolemize_vc_map(&disclosed_vcs)?,
        &deskolemize_deanon_map(&deanon_map)?,
    );

    // x. return query results
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
