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
use oxrdf::{vocab::xsd, BlankNode, Dataset, GraphName, Literal, NamedNode, Quad, Term};
use rdf_canon::{canon::serialize, issue_quads, relabel_quads, CanonicalizationError};
use std::collections::{HashMap, HashSet};

// TODO: fix name
#[derive(Debug)]
pub enum DeriveProofError {
    CanonicalizationError(CanonicalizationError),
    InvalidVCPairs,
    IriParseError(IriParseError),
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

    // build VP
    let verification_method = NamedNode::new_unchecked("https://example.org/holder#key1"); // TODO: replace with the real holder's public key
    let mut vp = build_vp_metadata(&vc_keys, &verification_method)?;
    let vc_quads: Vec<Vec<Quad>> = disclosed_vcs.iter().map(|(_, vc)| vc.into()).collect();
    vp.extend(vc_quads.into_iter().flatten());
    println!(
        "vp:\n{}\n",
        vp.iter()
            .map(std::string::ToString::to_string)
            .reduce(|l, r| format!("{}\n{}", l, r))
            .unwrap_or(String::new())
    );

    let issued_identifiers_map = issue_quads(&vp)?;
    let canonicalized_vp = relabel_quads(&vp, &issued_identifiers_map)?;
    println!("issued identifiers map:\n{:#?}\n", issued_identifiers_map);
    println!(
        "canonicalized dataset:\n{}\n",
        serialize(&Dataset::from_iter(&canonicalized_vp))
    );

    // TODO: extract proof values

    // TODO: calculate index mapping

    Ok(canonicalized_vp)
}

fn build_vp_metadata(
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
