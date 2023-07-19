use super::{
    context::{
        ASSERTION_METHOD, CREATED, CRYPTOSUITE, DATA_INTEGRITY_PROOF, FILTER, PROOF, PROOF_PURPOSE,
        PROOF_VALUE, VERIFIABLE_CREDENTIAL, VERIFIABLE_CREDENTIAL_TYPE,
        VERIFIABLE_PRESENTATION_TYPE, VERIFICATION_METHOD,
    },
    CRYPTOSUITE_FOR_VP,
};

use chrono::offset::Utc;
use oxiri::IriParseError;
use oxrdf::{
    vocab::{rdf::TYPE, xsd},
    BlankNode, BlankNodeIdParseError, BlankNodeRef, Dataset, GraphName, Literal, NamedNode,
    NamedNodeRef, Quad, Subject, Term, Triple,
};
use rdf_canon::{canon::serialize, issue_quads, relabel_quads, CanonicalizationError};
use std::collections::{BTreeMap, HashMap};

// TODO: fix name
#[derive(Debug)]
pub enum DeriveProofError {
    CanonicalizationError(CanonicalizationError),
    InvalidVCPairs,
    IriParseError(IriParseError),
    VCWithoutProofValue,
    VCWithoutVCType,
    VCWithInvalidProofValue,
    InvalidVCGraphName,
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

pub struct VcWithDisclosed {
    vc: Vec<Quad>,
    disclosed_vc: Vec<Quad>,
}

impl VcWithDisclosed {
    pub fn new(vc: Vec<Quad>, disclosed_vc: Vec<Quad>) -> Self {
        Self { vc, disclosed_vc }
    }
}

pub fn derive_proof(
    vcs: &Vec<VcWithDisclosed>,
    deanon_map: &HashMap<BlankNode, Term>,
) -> Result<Vec<Quad>, DeriveProofError> {
    // VCs must not be empty
    if vcs.is_empty() {
        return Err(DeriveProofError::InvalidVCPairs);
    }

    // TODO:
    // each disclosed VCs must be the derived subset of corresponding VCs via deanon map

    // extract proof values from VC
    let proof_values = vcs
        .iter()
        .map(|vc| {
            let v = &vc
                .vc
                .iter()
                .find(|&q| q.predicate == PROOF_VALUE)
                .ok_or(DeriveProofError::VCWithoutProofValue)?
                .object;
            match v {
                Term::Literal(literal) => Ok(literal.value()),
                _ => Err(DeriveProofError::VCWithInvalidProofValue),
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    println!("proof values:\n{:#?}\n", proof_values);

    // remove `proofValue`s from disclosed VCs
    let mut disclosed_vc_quads: Vec<Vec<Quad>> =
        vcs.iter().map(|vc| vc.disclosed_vc.clone()).collect();
    for disclosed_vc_quad in &mut disclosed_vc_quads {
        disclosed_vc_quad.retain(|q| q.predicate != PROOF_VALUE)
    }

    // construct VC graph keys
    let disclosed_vc_graph_names = vcs
        .iter()
        .map(|vc| {
            let g = &vc
                .disclosed_vc
                .iter()
                .find(|&q| q.predicate == TYPE && q.object == VERIFIABLE_CREDENTIAL_TYPE.into())
                .ok_or(DeriveProofError::VCWithoutVCType)?
                .graph_name;
            match g {
                GraphName::BlankNode(n) => Ok(n.as_ref()),
                _ => Err(DeriveProofError::InvalidVCGraphName),
            }
        })
        .collect::<Result<Vec<_>, _>>()?;

    // build VP without proof
    let verification_method = NamedNode::new_unchecked("https://example.org/holder#key1"); // TODO: replace with the real holder's public key
    let mut vp = build_vp(&disclosed_vc_graph_names, &verification_method)?;
    vp.extend(disclosed_vc_quads.into_iter().flatten());
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
    println!(
        "VP metadata:\n{}\n",
        vp_metadata
            .iter()
            .map(|t| format!("{} .\n", t.to_string()))
            .reduce(|l, r| format!("{}{}", l, r))
            .unwrap()
    );

    // extract VC graphs
    let mut vc_graphs = remove_graphs(&mut vp_graphs, &vp_metadata, VERIFIABLE_CREDENTIAL)?;
    println!("VC graphs:");
    for vc_graph in &vc_graphs {
        println!(
            "{}",
            vc_graph
                .iter()
                .map(|t| format!("{} .\n", t.to_string()))
                .reduce(|l, r| format!("{}{}", l, r))
                .unwrap()
        );
    }

    // extract VC proof graphs
    let mut vc_proof_graphs = vc_graphs
        .iter()
        .map(|vc| remove_graph(&mut vp_graphs, vc, PROOF))
        .collect::<Result<Vec<_>, _>>()?;
    println!("VC proof graphs:");
    for vc_proof_graph in &vc_proof_graphs {
        println!(
            "{}",
            vc_proof_graph
                .iter()
                .map(|t| format!("{} .\n", t.to_string()))
                .reduce(|l, r| format!("{}{}", l, r))
                .unwrap()
        );
    }

    // extract VP proof graph
    let vp_proof_graph = remove_graph(&mut vp_graphs, &vp_metadata, PROOF)?;
    println!(
        "VP proof graph:\n{}\n",
        vp_proof_graph
            .iter()
            .map(|t| format!("{} .\n", t.to_string()))
            .reduce(|l, r| format!("{}{}", l, r))
            .unwrap()
    );

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
    println!("deanonymized VC graphs:");
    for vc_graph in &vc_graphs {
        println!(
            "{}",
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
    println!("deanonymized VC proof graphs:");
    for vc_proof_graph in &vc_proof_graphs {
        println!(
            "{}",
            vc_proof_graph
                .iter()
                .map(|t| format!("{} .\n", t.to_string()))
                .reduce(|l, r| format!("{}{}", l, r))
                .unwrap()
        );
    }

    // TODO: calculate index mapping

    // TODO: calculate reveal index

    // TODO: calculate meta statements

    // TODO: derive proof value

    Ok(canonicalized_vp)
}

// function to remove from the VP the multiple graphs that are reachable from `source` via `link`
fn remove_graphs(
    vp_graphs: &mut BTreeMap<String, Vec<Triple>>,
    source: &Vec<Triple>,
    link: NamedNodeRef,
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
    link: NamedNodeRef,
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
    vc_graph_names: &Vec<BlankNodeRef>,
    verification_method: &NamedNode,
) -> Result<Vec<Quad>, DeriveProofError> {
    let vp_id = BlankNode::default();
    let vp_proof_id = BlankNode::default();
    let vp_proof_graph_id = BlankNode::default();
    let mut vp = vec![
        Quad::new(
            vp_id.clone(),
            TYPE,
            VERIFIABLE_PRESENTATION_TYPE,
            GraphName::DefaultGraph,
        ),
        Quad::new(
            vp_id.clone(),
            PROOF,
            vp_proof_graph_id.clone(),
            GraphName::DefaultGraph,
        ),
    ];
    let vcs = vc_graph_names
        .iter()
        .map(|vc_graph_name| {
            Ok(Quad::new(
                vp_id.clone(),
                VERIFIABLE_CREDENTIAL,
                *vc_graph_name,
                GraphName::DefaultGraph,
            ))
        })
        .collect::<Result<Vec<_>, DeriveProofError>>()?;
    let vp_proof = vec![
        Quad::new(
            vp_proof_id.clone(),
            TYPE,
            DATA_INTEGRITY_PROOF,
            vp_proof_graph_id.clone(),
        ),
        Quad::new(
            vp_proof_id.clone(),
            CRYPTOSUITE,
            Literal::new_simple_literal(CRYPTOSUITE_FOR_VP),
            vp_proof_graph_id.clone(),
        ),
        Quad::new(
            vp_proof_id.clone(),
            PROOF_PURPOSE,
            ASSERTION_METHOD,
            vp_proof_graph_id.clone(),
        ),
        Quad::new(
            vp_proof_id.clone(),
            VERIFICATION_METHOD,
            verification_method.clone(),
            vp_proof_graph_id.clone(),
        ),
        Quad::new(
            vp_proof_id,
            CREATED,
            Literal::new_typed_literal(format!("{:?}", Utc::now()), xsd::DATE_TIME),
            vp_proof_graph_id,
        ),
    ];
    vp.extend(vcs);
    vp.extend(vp_proof);
    Ok(vp)
}
