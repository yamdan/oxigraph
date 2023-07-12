use crate::zk::context::PROOF_VALUE;

use super::{
    builder::VerifiableCredential,
    context::{
        ASSERTION_METHOD, CREATED, CRYPTOSUITE, DATA_INTEGRITY_PROOF, PROOF, PROOF_PURPOSE,
        RDF_TYPE, VERIFIABLE_CREDENTIAL, VERIFIABLE_PRESENTATION_TYPE, VERIFICATION_METHOD,
    },
    CRYPTOSUITE_FOR_VP,
};

use chrono::offset::Utc;
use oxiri::IriParseError;
use oxrdf::{
    vocab::xsd, BlankNode, BlankNodeIdParseError, Dataset, GraphName, Literal, NamedNode, Quad,
    Term,
};
use rdf_canon::{canon::serialize, issue_quads, relabel_quads, CanonicalizationError};
use std::collections::{HashMap, HashSet};

// TODO: fix name
#[derive(Debug)]
pub enum DeriveProofError {
    CanonicalizationError(CanonicalizationError),
    InvalidVCPairs,
    IriParseError(IriParseError),
    VCWithoutProofValue,
    VCWithInvalidProofValue,
    BlankNodeIdParseError(BlankNodeIdParseError),
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
                Ok((cnid, v.clone()))
            } else {
                Ok((cnid, bnode.into()))
            }
        })
        .collect::<Result<_, DeriveProofError>>()?;
    println!("extended deanon map:\n{:?}\n", extended_deanon_map);

    // TODO: calculate index mapping

    // TODO: derive proof value

    Ok(canonicalized_vp)
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
