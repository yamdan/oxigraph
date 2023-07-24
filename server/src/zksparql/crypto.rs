use super::{
    context::{
        ASSERTION_METHOD, CREATED, CRYPTOSUITE, DATA_INTEGRITY_PROOF, FILTER, PROOF, PROOF_PURPOSE,
        PROOF_VALUE, VERIFIABLE_CREDENTIAL, VERIFIABLE_CREDENTIAL_TYPE,
        VERIFIABLE_PRESENTATION_TYPE,
    },
    CRYPTOSUITE_FOR_VP,
};

use chrono::offset::Utc;
use oxiri::IriParseError;
use oxrdf::{
    dataset::GraphView,
    vocab::{rdf::TYPE, xsd},
    BlankNode, BlankNodeIdParseError, Dataset, Graph, GraphNameRef, LiteralRef, NamedNodeRef, Quad,
    QuadRef, Subject, Term, TermRef, Triple,
};
use rdf_canon::{canon::serialize, issue, relabel, CanonicalizationError};
use std::collections::{BTreeMap, BTreeSet, HashMap};

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

pub struct VerifiableCredentialView<'a> {
    document: GraphView<'a>,
    proof: GraphView<'a>,
}

impl<'a> VerifiableCredentialView<'a> {
    pub fn new(document: GraphView<'a>, proof: GraphView<'a>) -> Self {
        Self { document, proof }
    }
}

pub struct VerifiableCredentialTriples {
    document: Vec<Triple>,
    proof: Vec<Triple>,
}

impl From<VerifiableCredentialView<'_>> for VerifiableCredentialTriples {
    fn from(view: VerifiableCredentialView) -> Self {
        let mut document = view
            .document
            .iter()
            .map(|t| t.into_owned())
            .collect::<Vec<_>>();
        document.sort_by_cached_key(|t| t.to_string());
        let mut proof = view
            .proof
            .iter()
            .map(|t| t.into_owned())
            .collect::<Vec<_>>();
        proof.sort_by_cached_key(|t| t.to_string());
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

/// `oxrdf::triple::GraphNameRef` with string-based ordering
#[derive(Eq, PartialEq, Clone)]
struct OrderedGraphNameRef<'a>(GraphNameRef<'a>);
impl Ord for OrderedGraphNameRef<'_> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.to_string().cmp(&other.0.to_string())
    }
}
impl PartialOrd for OrderedGraphNameRef<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.0.to_string().partial_cmp(&other.0.to_string())
    }
}
impl<'a> From<OrderedGraphNameRef<'a>> for GraphNameRef<'a> {
    fn from(value: OrderedGraphNameRef<'a>) -> Self {
        value.0
    }
}
impl<'a> TryFrom<TermRef<'a>> for OrderedGraphNameRef<'a> {
    type Error = DeriveProofError;

    fn try_from(value: TermRef<'a>) -> Result<Self, Self::Error> {
        match value {
            TermRef::NamedNode(n) => Ok(OrderedGraphNameRef(n.into())),
            TermRef::BlankNode(n) => Ok(OrderedGraphNameRef(n.into())),
            _ => Err(DeriveProofError::InternalError(
                "invalid graph name: graph name must not be literal or triple".to_string(),
            )),
        }
    }
}
impl std::fmt::Display for OrderedGraphNameRef<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
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
        .map(
            |VcWithDisclosed {
                 vc: VerifiableCredential { proof, .. },
                 ..
             }| {
                match proof
                    .triples_for_predicate(PROOF_VALUE)
                    .next()
                    .ok_or(DeriveProofError::VCWithoutProofValue)?
                    .object
                {
                    TermRef::Literal(literal) => Ok(literal.value()),
                    _ => Err(DeriveProofError::VCWithInvalidProofValue),
                }
            },
        )
        .collect::<Result<Vec<_>, _>>()?;
    println!("proof values:\n{:#?}\n", proof_values);

    // remove `proofValue`s from disclosed VCs
    let disclosed_vcs = vcs
        .iter()
        .map(
            |VcWithDisclosed {
                 disclosed: VerifiableCredential { document, proof },
                 ..
             }| VerifiableCredential {
                document: Graph::from_iter(document),
                proof: Graph::from_iter(proof.iter().filter(|t| t.predicate != PROOF_VALUE)),
            },
        )
        .collect();

    // build VP (without proof yet)
    let vp = build_vp(&disclosed_vcs)?;
    println!("vp:\n{}\n", vp.to_string());

    // canonicalize VP
    let issued_identifiers_map = issue(&vp)?;
    let canonicalized_vp = relabel(&vp, &issued_identifiers_map)?;
    println!("issued identifiers map:\n{:#?}\n", issued_identifiers_map);
    println!("canonicalized vp:\n{}\n", serialize(&canonicalized_vp));

    // construct extended deanonymization map
    let extended_deanon_map = issued_identifiers_map
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

    // decompose canonicalized VP into graphs
    let VpGraphs {
        metadata: vp_metadata,
        proof: vp_proof,
        filters: filters_graph,
        vcs: vc_graphs,
    } = decompose_vp(&canonicalized_vp)?;

    // convert VC graphs and VC proof graphs into `Vec<Triple>`s
    let mut vc_graphs = vc_graphs
        .into_iter()
        .map(|(_, view)| view.into())
        .collect::<Vec<VerifiableCredentialTriples>>();
    println!("VC graphs (before deanonymized):");
    for VerifiableCredentialTriples { document, proof } in &vc_graphs {
        println!(
            "document:\n{}",
            document
                .iter()
                .map(|t| format!("{} .\n", t.to_string()))
                .reduce(|l, r| format!("{}{}", l, r))
                .unwrap()
        );
        println!(
            "proof:\n{}",
            proof
                .iter()
                .map(|t| format!("{} .\n", t.to_string()))
                .reduce(|l, r| format!("{}{}", l, r))
                .unwrap()
        );
    }

    // deanonymize each VC graphs, keeping their orders
    for VerifiableCredentialTriples { document, proof } in &mut vc_graphs {
        for triple in document.into_iter() {
            deanonymize_subject(&extended_deanon_map, &mut triple.subject)?;
            deanonymize_term(&extended_deanon_map, &mut triple.object)?;
        }
        for triple in proof.into_iter() {
            deanonymize_subject(&extended_deanon_map, &mut triple.subject)?;
            deanonymize_term(&extended_deanon_map, &mut triple.object)?;
        }
    }
    println!("deanonymized VC graphs:");
    for VerifiableCredentialTriples { document, proof } in &vc_graphs {
        println!(
            "document:\n{}",
            document
                .iter()
                .map(|t| format!("{} .\n", t.to_string()))
                .reduce(|l, r| format!("{}{}", l, r))
                .unwrap()
        );
        println!(
            "proof:\n{}",
            proof
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
fn remove_graphs<'a>(
    vp_graphs: &mut BTreeMap<OrderedGraphNameRef<'a>, GraphView<'a>>,
    source: &GraphView<'a>,
    link: NamedNodeRef,
) -> Result<BTreeMap<OrderedGraphNameRef<'a>, GraphView<'a>>, DeriveProofError> {
    source
        .iter()
        .filter(|triple| triple.predicate == link)
        .map(|triple| {
            Ok((
                triple.object.try_into()?,
                vp_graphs
                    .remove(&triple.object.try_into()?)
                    .ok_or(DeriveProofError::InvalidVP)?,
            ))
        })
        .collect::<Result<BTreeMap<_, _>, DeriveProofError>>()
}

// function to remove from the VP the single graph that is reachable from `source` via `link`
fn remove_graph<'a>(
    vp_graphs: &mut BTreeMap<OrderedGraphNameRef<'a>, GraphView<'a>>,
    source: &GraphView<'a>,
    link: NamedNodeRef,
) -> Result<GraphView<'a>, DeriveProofError> {
    let mut graphs = remove_graphs(vp_graphs, source, link)?;
    match graphs.pop_first() {
        Some((_, graph)) => {
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

fn build_vp(vcs: &Vec<VerifiableCredential>) -> Result<Dataset, DeriveProofError> {
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
        CREATED,
        LiteralRef::new_typed_literal(&format!("{:?}", Utc::now()), xsd::DATE_TIME),
        &vp_proof_graph_id,
    ));

    // convert VC graphs (triples) into VC dataset (quads)
    let vc_quads = vcs
        .iter()
        .map(|VerifiableCredential { document, proof }| {
            let document_graph_name = BlankNode::default();
            let proof_graph_name = BlankNode::default();
            let document_id = document
                .subject_for_predicate_object(TYPE, VERIFIABLE_CREDENTIAL_TYPE)
                .ok_or(DeriveProofError::VCWithoutVCType)?;

            let mut document_quads: Vec<Quad> = document
                .iter()
                .map(|t| t.into_owned().in_graph(document_graph_name.clone()))
                .collect();

            // add `proof` link from VC document to VC proof graph
            document_quads.push(Quad::new(
                document_id,
                PROOF,
                proof_graph_name.clone(),
                document_graph_name.clone(),
            ));

            let mut proof_quads: Vec<Quad> = proof
                .iter()
                .map(|t| t.into_owned().in_graph(proof_graph_name.clone()))
                .collect();
            document_quads.append(&mut proof_quads);

            Ok((document_graph_name, document_quads))
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

struct VpGraphs<'a> {
    metadata: GraphView<'a>,
    proof: GraphView<'a>,
    filters: BTreeMap<OrderedGraphNameRef<'a>, GraphView<'a>>,
    vcs: BTreeMap<OrderedGraphNameRef<'a>, VerifiableCredentialView<'a>>,
}

fn decompose_vp<'a>(vp: &'a Dataset) -> Result<VpGraphs<'a>, DeriveProofError> {
    let vp_graph_name_set = vp
        .iter()
        .map(|QuadRef { graph_name, .. }| OrderedGraphNameRef(graph_name))
        .collect::<BTreeSet<_>>();

    let mut vp_graphs = vp_graph_name_set
        .into_iter()
        .map(|vp_graph_name| (vp_graph_name.clone(), vp.graph(vp_graph_name)))
        .collect::<BTreeMap<_, _>>();
    println!("vp graphs:");
    for g in vp_graphs.keys() {
        println!("{}:\n{}\n", g, vp_graphs.get(g).unwrap());
    }

    // extract VP metadata (default graph)
    let metadata = vp_graphs
        .remove(&OrderedGraphNameRef(GraphNameRef::DefaultGraph))
        .ok_or(DeriveProofError::InternalError(
            "VP graphs must have default graph".to_owned(),
        ))?;
    println!("VP metadata:\n{}\n", metadata);

    // extract VP proof graph
    let proof = remove_graph(&mut vp_graphs, &metadata, PROOF)?;
    println!("VP proof graph:\n{}\n", proof);

    // extract filter graphs if any
    let filters = remove_graphs(&mut vp_graphs, &proof, FILTER)?;
    println!("filter graphs:");
    for (_, filter_graph) in &filters {
        println!("{}", filter_graph);
    }

    // extract VC graphs
    let vcs = remove_graphs(&mut vp_graphs, &metadata, VERIFIABLE_CREDENTIAL)?;
    println!("VC graphs:");
    for (_, vc) in &vcs {
        println!("{}", vc);
    }

    // extract VC proof graphs
    let vcs = vcs
        .into_iter()
        .map(|(vc_graph_name, vc)| {
            let vc_proof = remove_graph(&mut vp_graphs, &vc, PROOF)?;
            Ok((vc_graph_name, VerifiableCredentialView::new(vc, vc_proof)))
        })
        .collect::<Result<BTreeMap<_, _>, DeriveProofError>>()?;
    println!("VC proof graphs:");
    for (_, vc) in &vcs {
        println!("{}", vc.proof);
    }

    // TODO: filter out PROOF

    // check if `vp_graphs` is empty
    if !vp_graphs.is_empty() {
        return Err(DeriveProofError::InvalidVP);
    }

    Ok(VpGraphs {
        metadata,
        proof,
        filters,
        vcs,
    })
}
