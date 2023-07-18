use super::{
    builder::VerifiableCredential,
    context::{
        ASSERTION_METHOD, CREATED, CRYPTOSUITE, DATA_INTEGRITY_PROOF, FILTER, PROOF, PROOF_PURPOSE,
        PROOF_VALUE, RDF_TYPE, VERIFIABLE_CREDENTIAL, VERIFIABLE_PRESENTATION_TYPE,
        VERIFICATION_METHOD,
    },
    CRYPTOSUITE_FOR_VP,
};

use chrono::offset::Utc;
use oxiri::IriParseError;
use oxrdf::{
    vocab::xsd, BlankNode, BlankNodeIdParseError, Dataset, GraphName, Literal, NamedNode, Quad,
    Subject, Term, Triple,
};
use rdf_canon::{canon::serialize, issue_quads, relabel_quads, CanonicalizationError};
use std::collections::{BTreeMap, HashMap, HashSet};

// TODO: fix name
#[derive(Debug)]
pub enum DeriveProofError {
    CanonicalizationError(CanonicalizationError),
    InvalidVCPairs,
    IriParseError(IriParseError),
    VCWithoutProofValue,
    VCWithInvalidProofValue,
    BlankNodeIdParseError(BlankNodeIdParseError),
    DeAnonymizationError,
    InvalidVP,
    InternalError(String),
}

impl From<IriParseError> for DeriveProofError {
    fn from(e: IriParseError) -> Self {
        Self::IriParseError(e)
    }
}

impl From<CanonicalizationError> for DeriveProofError {
    fn from(e: CanonicalizationError) -> Self {
        Self::CanonicalizationError(e)
    }
}

impl From<BlankNodeIdParseError> for DeriveProofError {
    fn from(e: BlankNodeIdParseError) -> Self {
        Self::BlankNodeIdParseError(e)
    }
}

pub fn derive_proof(
    vcs: &HashMap<GraphName, VerifiableCredential>,
    disclosed_vcs: &HashMap<GraphName, VerifiableCredential>,
    deanon_map: &HashMap<BlankNode, Term>,
) -> Result<Vec<Quad>, DeriveProofError> {
    let vc_keys: HashSet<_> = vcs.keys().collect();
    let disclosed_vc_keys: HashSet<_> = disclosed_vcs.keys().collect();
    if vc_keys != disclosed_vc_keys {
        return Err(DeriveProofError::InvalidVCPairs);
    }

    // extract proof values from VC
    let proof_values: Vec<_> = vcs
        .iter()
        .map(|(_, vc)| {
            let v = &vc
                .proof
                .iter()
                .find(|&q| q.predicate == PROOF_VALUE)
                .ok_or(DeriveProofError::VCWithoutProofValue)?
                .object;
            match v {
                Term::Literal(literal) => Ok(literal.value()),
                _ => Err(DeriveProofError::VCWithInvalidProofValue),
            }
        })
        .collect::<Result<_, _>>()?;
    println!("proof values:\n{:#?}\n", proof_values);

    // remove proof values from disclosed VCs
    let mut vc_quads: Vec<Vec<Quad>> = disclosed_vcs.iter().map(|(_, vc)| vc.into()).collect();
    for vc_quad in &mut vc_quads {
        vc_quad.retain(|q| q.predicate != PROOF_VALUE)
    }

    // build VP without proof
    let verification_method = NamedNode::new_unchecked("https://example.org/holder#key1"); // TODO: replace with the real holder's public key
    let mut vp = build_vp(&vc_keys, &verification_method)?;
    vp.extend(vc_quads.into_iter().flatten());
    println!(
        "vp:\n{}\n",
        vp.iter()
            .map(std::string::ToString::to_string)
            .reduce(|l, r| format!("{}\n{}", l, r))
            .unwrap_or(String::new())
    );

    // canonicalize VP
    let issued_identifiers_map = issue_quads(&vp)?;
    let canonicalized_vp = relabel_quads(&vp, &issued_identifiers_map)?;
    println!("issued identifiers map:\n{:#?}\n", issued_identifiers_map);
    println!("deanon map:\n{:#?}\n", deanon_map);
    println!(
        "canonicalized vp:\n{}\n",
        serialize(&Dataset::from_iter(&canonicalized_vp))
    );

    // construct extended deanonymization map
    let extended_deanon_map: HashMap<_, _> = issued_identifiers_map
        .into_iter()
        .map(|(bnid, cnid)| {
            let bnode = BlankNode::new(bnid)?;
            if let Some(v) = deanon_map.get(&bnode) {
                Ok((BlankNode::new(cnid)?, v.clone()))
            } else {
                Ok((BlankNode::new(cnid)?, bnode.into()))
            }
        })
        .collect::<Result<_, DeriveProofError>>()?;
    println!("extended deanon map:\n{:?}\n", extended_deanon_map);

    // split canonicalized VP into graphs and sort them
    let mut vp_graphs: BTreeMap<String, Vec<Triple>> = BTreeMap::new();
    for quad in &canonicalized_vp {
        vp_graphs
            .entry(quad.graph_name.to_string())
            .or_default()
            .push(Triple::new(
                quad.subject.clone(),
                quad.predicate.clone(),
                quad.object.clone(),
            ));
    }
    for (_, triples) in &mut vp_graphs {
        triples.sort_by_cached_key(|t| t.to_string());
    }
    println!("vp graphs:");
    for g in vp_graphs.keys() {
        println!(
            "{}:\n{}\n",
            g,
            vp_graphs
                .get(g)
                .unwrap()
                .iter()
                .map(|t| format!("{} .\n", t.to_string()))
                .reduce(|l, r| format!("{}{}", l, r))
                .unwrap()
        );
    }

    // process VP metadata (default graph)
    let vp_metadata = vp_graphs
        .remove("DEFAULT")
        .ok_or(DeriveProofError::InternalError(
            "VP graphs must have default graph".to_owned(),
        ))?;

    // extract VC graphs
    let mut vc_graphs = remove_graphs(&mut vp_graphs, &vp_metadata, VERIFIABLE_CREDENTIAL)?;
    println!("VC graphs:\n{:#?}\n", vc_graphs);

    // extract VC proof graphs
    let mut vc_proof_graphs = vc_graphs
        .iter()
        .map(|vc| remove_graph(&mut vp_graphs, vc, PROOF))
        .collect::<Result<Vec<_>, _>>()?;
    println!("VC proof graphs:\n{:#?}\n", vc_proof_graphs);

    // extract VP proof graph
    let vp_proof_graph = remove_graph(&mut vp_graphs, &vp_metadata, PROOF)?;
    println!("VP proof graph:\n{:#?}\n", vp_proof_graph);

    // extract filter graphs if any
    let filter_graphs = remove_graphs(&mut vp_graphs, &vp_proof_graph, FILTER)?;
    println!("filter graphs:\n{:#?}\n", filter_graphs);

    // check that `vp_graphs` is empty
    if !vp_graphs.is_empty() {
        return Err(DeriveProofError::InvalidVP);
    }

    // deanonymize each VC graphs, keeping their orders
    for vc_graph in &mut vc_graphs {
        for triple in vc_graph {
            deanonymize_subject(&extended_deanon_map, &mut triple.subject)?;
            deanonymize_term(&extended_deanon_map, &mut triple.object)?;
        }
    }
    println!("deanonymized vc graphs:");
    for vc_graph in vc_graphs {
        println!(
            "{}\n",
            vc_graph
                .iter()
                .map(|t| format!("{} .\n", t.to_string()))
                .reduce(|l, r| format!("{}{}", l, r))
                .unwrap()
        );
    }

    // deanonymize each VC proof graphs, keeping their orders
    for vc_proof_graph in &mut vc_proof_graphs {
        for triple in vc_proof_graph {
            deanonymize_subject(&extended_deanon_map, &mut triple.subject)?;
            deanonymize_term(&extended_deanon_map, &mut triple.object)?;
        }
    }
    println!("deanonymized vc proof graphs:");
    for vc_proof_graph in vc_proof_graphs {
        println!(
            "{}\n",
            vc_proof_graph
                .iter()
                .map(|t| format!("{} .\n", t.to_string()))
                .reduce(|l, r| format!("{}{}", l, r))
                .unwrap()
        );
    }

    // TODO: calculate index mapping

    // TODO: derive proof value

    Ok(canonicalized_vp)
}

// function to remove from the VP the multiple graphs that are reachable from `source` via `link`
fn remove_graphs(
    vp_graphs: &mut BTreeMap<String, Vec<Triple>>,
    source: &Vec<Triple>,
    link: &str,
) -> Result<Vec<Vec<Triple>>, DeriveProofError> {
    source
        .iter()
        .filter(|triple| triple.predicate == link)
        .map(|triple| {
            Ok(vp_graphs
                .remove(&triple.object.to_string())
                .ok_or(DeriveProofError::InvalidVP)?)
        })
        .collect::<Result<Vec<_>, DeriveProofError>>()
}

// function to remove from the VP the single graph that is reachable from `source` via `link`
fn remove_graph(
    vp_graphs: &mut BTreeMap<String, Vec<Triple>>,
    source: &Vec<Triple>,
    link: &str,
) -> Result<Vec<Triple>, DeriveProofError> {
    let mut graphs = remove_graphs(vp_graphs, source, link)?;
    match graphs.pop() {
        Some(graph) => {
            if graphs.is_empty() {
                Ok(graph)
            } else {
                Err(DeriveProofError::InvalidVP)
            }
        }
        None => Err(DeriveProofError::InvalidVP),
    }
}

fn deanonymize_subject(
    deanon_map: &HashMap<BlankNode, Term>,
    subject: &mut Subject,
) -> Result<(), DeriveProofError> {
    match subject {
        Subject::BlankNode(bnode) => {
            if let Some(v) = deanon_map.get(bnode) {
                match v {
                    Term::NamedNode(n) => *subject = Subject::NamedNode(n.clone()),
                    Term::BlankNode(n) => *subject = Subject::BlankNode(n.clone()),
                    _ => return Err(DeriveProofError::DeAnonymizationError),
                }
            }
        }
        Subject::NamedNode(_) => (),
        Subject::Triple(_) => return Err(DeriveProofError::DeAnonymizationError),
    };
    Ok(())
}

fn deanonymize_term(
    deanon_map: &HashMap<BlankNode, Term>,
    term: &mut Term,
) -> Result<(), DeriveProofError> {
    match term {
        Term::BlankNode(bnode) => {
            if let Some(v) = deanon_map.get(bnode) {
                match v {
                    Term::NamedNode(_) | Term::BlankNode(_) | Term::Literal(_) => *term = v.clone(),
                    _ => return Err(DeriveProofError::DeAnonymizationError),
                }
            }
        }
        Term::NamedNode(_) | Term::Literal(_) => (),
        Term::Triple(_) => return Err(DeriveProofError::DeAnonymizationError),
    };
    Ok(())
}

fn build_vp(
    cred_graph_ids: &HashSet<&GraphName>,
    verification_method: &NamedNode,
) -> Result<Vec<Quad>, DeriveProofError> {
    let vp_id = BlankNode::default();
    let vp_proof_id = BlankNode::default();
    let vp_proof_graph_id = BlankNode::default();
    let mut vp = vec![
        Quad::new(
            vp_id.clone(),
            NamedNode::new(RDF_TYPE)?,
            NamedNode::new(VERIFIABLE_PRESENTATION_TYPE)?,
            GraphName::DefaultGraph,
        ),
        Quad::new(
            vp_id.clone(),
            NamedNode::new(PROOF)?,
            vp_proof_graph_id.clone(),
            GraphName::DefaultGraph,
        ),
    ];
    let vcs: Vec<_> = cred_graph_ids
        .iter()
        .map(|cred_graph_id| {
            let cred_graph_id = match cred_graph_id {
                GraphName::NamedNode(n) => Ok(Term::NamedNode(n.clone())),
                GraphName::BlankNode(n) => Ok(Term::BlankNode(n.clone())),
                GraphName::DefaultGraph => Err(DeriveProofError::InternalError(
                    "stored VC must not in the default graph".to_owned(),
                )),
            }?;
            Ok(Quad::new(
                vp_id.clone(),
                NamedNode::new(VERIFIABLE_CREDENTIAL)?,
                cred_graph_id,
                GraphName::DefaultGraph,
            ))
        })
        .collect::<Result<_, DeriveProofError>>()?;
    let vp_proof = vec![
        Quad::new(
            vp_proof_id.clone(),
            NamedNode::new(RDF_TYPE)?,
            NamedNode::new(DATA_INTEGRITY_PROOF)?,
            vp_proof_graph_id.clone(),
        ),
        Quad::new(
            vp_proof_id.clone(),
            NamedNode::new(CRYPTOSUITE)?,
            Literal::new_simple_literal(CRYPTOSUITE_FOR_VP),
            vp_proof_graph_id.clone(),
        ),
        Quad::new(
            vp_proof_id.clone(),
            NamedNode::new(PROOF_PURPOSE)?,
            NamedNode::new(ASSERTION_METHOD)?,
            vp_proof_graph_id.clone(),
        ),
        Quad::new(
            vp_proof_id.clone(),
            NamedNode::new(VERIFICATION_METHOD)?,
            verification_method.clone(),
            vp_proof_graph_id.clone(),
        ),
        Quad::new(
            vp_proof_id,
            NamedNode::new(CREATED)?,
            Literal::new_typed_literal(format!("{:?}", Utc::now()), xsd::DATE_TIME),
            vp_proof_graph_id,
        ),
    ];
    vp.extend(vcs);
    vp.extend(vp_proof);
    Ok(vp)
}
