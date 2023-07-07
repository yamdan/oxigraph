mod builder;
mod context;
mod error;
mod nymizer;
mod parser;

use crate::{
    bad_request, base_url, query_results_content_negotiation,
    zk::{
        builder::{
            build_disclosed_subjects, build_extended_fetch_query, build_extended_prove_query,
            build_vp_metadata, deskolemize, get_proof_values, get_verifiable_credential,
            pseudonymize_metadata_and_proofs,
        },
        context::PROOF_VALUE,
        error::ZkSparqlError,
        nymizer::Pseudonymizer,
        parser::parse_zk_query,
    },
    HttpError, ReadForWrite,
};

use oxhttp::model::{Request, Response};
use oxigraph::{sparql::QueryResults, store::Store};
use oxrdf::{Dataset, NamedNode};
use rdf_canon::{issue, relabel};
use sparesults::QueryResultsSerializer;
use std::collections::{HashMap, HashSet};
use url::form_urlencoded;

const SKOLEM_IRI_PREFIX: &str = "urn:bnid:";
const SUBJECT_GRAPH_SUFFIX: &str = ".subject";
const PROOF_GRAPH_SUFFIX: &str = ".proof";
const VC_VARIABLE_PREFIX: &str = "__vc";
const PSEUDONYMOUS_IRI_PREFIX: &str = "urn:bnid:";
const PSEUDONYMOUS_VAR_PREFIX: &str = "urn:var:";
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
    if proof_required {
        evaluate_zksparql_prove(store, &query, request).map_err(std::convert::Into::into)
    } else {
        let extended_results = evaluate_zksparql_fetch(store, &query, request)
            .map_err(std::convert::Into::<HttpError>::into)?;
        match extended_results {
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
) -> Result<Response, ZkSparqlError> {
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

    // 4. pseudonymize the extended prove solutions
    let mut nymizer = Pseudonymizer::default();
    let pseudonymized_solutions =
        nymizer.pseudonymize_solutions(extended_solutions, &parsed_zk_query.disclosed_variables)?;
    println!("pseudonymous solutions:\n{:#?}\n", pseudonymized_solutions);

    // 5. build disclosed subjects by assigning pseudonymous solutions to extended prove patterns
    let mut disclosed_subjects =
        build_disclosed_subjects(&pseudonymized_solutions, &extended_triple_patterns)?;

    // 6. get associated VCs
    let cred_graph_ids: HashSet<_> = disclosed_subjects
        .iter()
        .map(|quad| quad.graph_name.clone())
        .collect();
    let vcs: HashMap<_, _> = cred_graph_ids
        .iter()
        .map(|cred_graph_id| {
            Ok((
                cred_graph_id.clone(),
                get_verifiable_credential(cred_graph_id, store)?,
            ))
        })
        .collect::<Result<_, ZkSparqlError>>()?;

    // 7. pseudonymize VCs
    let pseudonymized_vcs: HashMap<_, _> = vcs
        .iter()
        .map(|(cred_graph_id, vc)| {
            Ok((
                cred_graph_id.clone(),
                pseudonymize_metadata_and_proofs(cred_graph_id, vc, store, &mut nymizer)?,
            ))
        })
        .collect::<Result<_, ZkSparqlError>>()?;
    println!("pseudonymized_vcs:\n{:#?}\n", pseudonymized_vcs);

    // 8. build disclosed dataset and proofs
    let mut disclosed_dataset: Vec<_> = pseudonymized_vcs
        .values()
        .map(|pseudonymized_vc| {
            let mut proof: Vec<_> = pseudonymized_vc
                .proof
                .clone()
                .into_iter()
                .filter(|quad| quad.predicate != PROOF_VALUE)
                .collect();
            proof.extend(pseudonymized_vc.metadata.clone());
            Ok(proof)
        })
        .collect::<Result<Vec<_>, ZkSparqlError>>()
        .map(|v| v.into_iter().flatten().collect())?;
    disclosed_dataset.append(&mut disclosed_subjects);

    // 9. get proof values
    let proof_values = get_proof_values(&cred_graph_ids, store)?;
    println!("proof values:\n{:#?}\n", proof_values);

    // 10. get deanonymization map
    let deanon_map = nymizer.get_deanon_map();
    println!("deanon map:\n{:#?}\n", deanon_map);

    // 11. build VP
    let verification_method = NamedNode::new_unchecked("https://example.org/holder#key1"); // TODO: replace with the real holder's public key
    let mut vp_metadata = build_vp_metadata(&cred_graph_ids, &verification_method)?;
    disclosed_dataset.append(&mut vp_metadata);
    println!(
        "disclosed dataset:\n{}\n",
        disclosed_dataset
            .iter()
            .map(std::string::ToString::to_string)
            .reduce(|l, r| format!("{}\n{}", l, r))
            .unwrap_or(String::new())
    );

    // 12. deskolemize VP
    let vp: Vec<_> = disclosed_dataset
        .into_iter()
        .map(|quad| deskolemize(&quad))
        .collect::<Result<_, _>>()?;
    println!(
        "vp:\n{}\n",
        vp.iter()
            .map(std::string::ToString::to_string)
            .reduce(|l, r| format!("{}\n{}", l, r))
            .unwrap_or(String::new())
    );

    // 13. canonicalize VP
    let vp_dataset = Dataset::from_iter(vp);
    let issued_identifiers_map = issue(&vp_dataset)?;
    let canonicalized_dataset = relabel(&vp_dataset, &issued_identifiers_map)?;
    println!("issued identifiers map:\n{:#?}\n", issued_identifiers_map);
    println!(
        "canonicalized dataset:\n{}\n",
        canonicalized_dataset
            .iter()
            .map(|q| q.to_string())
            .reduce(|l, r| format!("{}\n{}", l, r))
            .unwrap_or(String::new())
    );

    // x. return query results
    todo!()
    // let format = query_results_content_negotiation(request)?;
    // ReadForWrite::build_response(
    //     move |w| {
    //         Ok((
    //             QueryResultsSerializer::from_format(format)
    //                 .solutions_writer(w, extended_solutions.variables().to_vec())?,
    //             extended_solutions,
    //         ))
    //     },
    //     |(mut writer, mut solutions)| {
    //         Ok(if let Some(solution) = solutions.next() {
    //             writer.write(&solution?)?;
    //             Some((writer, solutions))
    //         } else {
    //             writer.finish()?;
    //             None
    //         })
    //     },
    //     format.media_type(),
    // )
}
