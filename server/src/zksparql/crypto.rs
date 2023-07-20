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
    BlankNode, BlankNodeIdParseError, Dataset, Graph, GraphNameRef, LiteralRef, NamedNode,
    NamedNodeRef, Quad, QuadRef, Subject, Term, TermRef, Triple,
};
use rdf_canon::{canon::serialize, issue, relabel, CanonicalizationError};
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

pub struct VerifiableCredential {
    document: Graph,
    proof: Graph,
}

impl VerifiableCredential {
    pub fn new(document: Graph, proof: Graph) -> Self {
        Self { document, proof }
    }
}

pub struct VcWithDisclosed {
    vc: VerifiableCredential,
    disclosed: VerifiableCredential,
}

impl VcWithDisclosed {
    pub fn new(vc: VerifiableCredential, disclosed: VerifiableCredential) -> Self {
        Self { vc, disclosed }
    }

    pub fn to_string(&self) -> String {
        format!(
            "vc:\n{}vc_proof:\n{}\ndisclosed_vc:\n{}disclosed_vc_proof:\n{}\n",
            &self
                .vc
                .document
                .iter()
                .map(|q| format!("{} .\n", q.to_string()))
                .collect::<String>(),
            &self
                .vc
                .proof
                .iter()
                .map(|q| format!("{} .\n", q.to_string()))
                .collect::<String>(),
            &self
                .disclosed
                .document
                .iter()
                .map(|q| format!("{} .\n", q.to_string()))
                .collect::<String>(),
            &self
                .disclosed
                .proof
                .iter()
                .map(|q| format!("{} .\n", q.to_string()))
                .collect::<String>()
        )
    }
}

pub fn derive_proof(
    vcs: &Vec<VcWithDisclosed>,
    deanon_map: &HashMap<BlankNode, Term>,
) -> Result<Dataset, DeriveProofError> {
    println!("*** start derive_proof ***");

    for vc in vcs {
        println!("{}", vc.to_string());
    }
    println!("deanon map:\n{:#?}\n", deanon_map);

    // check: VCs must not be empty
    if vcs.is_empty() {
        return Err(DeriveProofError::InvalidVCPairs);
    }

    // TODO:
    // check: each disclosed VCs must be the derived subset of corresponding VCs via deanon map

    // TODO:
    // check: verify VCs

    // extract proof values from VC
    let proof_values = vcs
        .iter()
        .map(|vc_with_disclosed| {
            let v = &vc_with_disclosed
                .vc
                .proof
                .triples_for_predicate(PROOF_VALUE)
                .next()
                .ok_or(DeriveProofError::VCWithoutProofValue)?
                .object;
            match v {
                TermRef::Literal(literal) => Ok(literal.value()),
                _ => Err(DeriveProofError::VCWithInvalidProofValue),
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    println!("proof values:\n{:#?}\n", proof_values);

    // remove `proofValue`s from disclosed VCs
    let disclosed_vcs: Vec<_> = vcs
        .iter()
        .map(|vc_with_disclosed| {
            let disclosed_document = &vc_with_disclosed.disclosed.document;
            let disclosed_proof = &vc_with_disclosed.disclosed.proof;
            VerifiableCredential {
                document: Graph::from_iter(disclosed_document),
                proof: Graph::from_iter(
                    disclosed_proof
                        .iter()
                        .filter(|t| t.predicate != PROOF_VALUE),
                ),
            }
        })
        .collect();

    // build VP without proof
    let verification_method = NamedNode::new_unchecked("https://example.org/holder#key1"); // TODO: replace with the real holder's public key
    let vp = build_vp(&disclosed_vcs, &verification_method)?;
    println!("vp:\n{}\n", vp.to_string());

    // canonicalize VP
    let issued_identifiers_map = issue(&vp)?;
    let canonicalized_vp = relabel(&vp, &issued_identifiers_map)?;
    println!("issued identifiers map:\n{:#?}\n", issued_identifiers_map);
    println!("canonicalized vp:\n{}\n", serialize(&canonicalized_vp));

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
    vcs: &Vec<VerifiableCredential>,
    verification_method: &NamedNode,
) -> Result<Dataset, DeriveProofError> {
    let vp_id = BlankNode::default();
    let vp_proof_id = BlankNode::default();
    let vp_proof_graph_id = BlankNode::default();
    let mut vp = Dataset::default();
    vp.insert(QuadRef::new(
        &vp_id,
        TYPE,
        VERIFIABLE_PRESENTATION_TYPE,
        GraphNameRef::DefaultGraph,
    ));
    vp.insert(QuadRef::new(
        &vp_id,
        PROOF,
        &vp_proof_graph_id,
        GraphNameRef::DefaultGraph,
    ));
    vp.insert(QuadRef::new(
        &vp_proof_id,
        TYPE,
        DATA_INTEGRITY_PROOF,
        &vp_proof_graph_id,
    ));
    vp.insert(QuadRef::new(
        &vp_proof_id,
        CRYPTOSUITE,
        LiteralRef::new_simple_literal(CRYPTOSUITE_FOR_VP),
        &vp_proof_graph_id,
    ));
    vp.insert(QuadRef::new(
        &vp_proof_id,
        PROOF_PURPOSE,
        ASSERTION_METHOD,
        &vp_proof_graph_id,
    ));
    vp.insert(QuadRef::new(
        &vp_proof_id,
        VERIFICATION_METHOD,
        verification_method,
        &vp_proof_graph_id,
    ));
    vp.insert(QuadRef::new(
        &vp_proof_id,
        CREATED,
        LiteralRef::new_typed_literal(&format!("{:?}", Utc::now()), xsd::DATE_TIME),
        &vp_proof_graph_id,
    ));

    let vc_quads = vcs
        .iter()
        .map(|vc| {
            let vc_graph_name = BlankNode::default();
            let vc_proof_graph_name = BlankNode::default();
            let vc_document_id = vc
                .document
                .subject_for_predicate_object(TYPE, VERIFIABLE_CREDENTIAL_TYPE)
                .ok_or(DeriveProofError::VCWithoutVCType)?;
            let mut document: Vec<Quad> = vc
                .document
                .iter()
                .map(|t| t.into_owned().in_graph(vc_graph_name.clone()))
                .collect();
            document.push(Quad::new(
                vc_document_id,
                PROOF,
                vc_proof_graph_name.clone(),
                vc_graph_name.clone(),
            ));
            let mut proof: Vec<Quad> = vc
                .proof
                .iter()
                .map(|t| t.into_owned().in_graph(vc_proof_graph_name.clone()))
                .collect();
            document.append(&mut proof);
            Ok((vc_graph_name, document))
        })
        .collect::<Result<Vec<_>, DeriveProofError>>()?;

    for (vc_graph_name, vc_quad) in vc_quads {
        vp.insert(QuadRef::new(
            &vp_id,
            VERIFIABLE_CREDENTIAL,
            &vc_graph_name,
            GraphNameRef::DefaultGraph,
        ));
        vp.extend(vc_quad);
    }
    Ok(vp)
}
