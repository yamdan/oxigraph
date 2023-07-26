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
    BlankNode, BlankNodeIdParseError, BlankNodeRef, Dataset, Graph, GraphName, GraphNameRef,
    LiteralRef, NamedNodeRef, Quad, QuadRef, Subject, Term, TermRef, Triple,
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
    BlankNodeCollisionError,
    DisclosedVCIsNotSubsetOfOriginalVC,
    InternalError(String),
}

// TODO: implement Error trait
// impl Error for DeriveProofError {}
// impl std::fmt::Display for DeriveProofError {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         todo!()
//     }
// }

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
            .filter(|t| t.predicate != PROOF) // filter out `proof`
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

impl From<&VerifiableCredential> for VerifiableCredentialTriples {
    fn from(view: &VerifiableCredential) -> Self {
        let mut document = view
            .document
            .iter()
            .filter(|t| t.predicate != PROOF) // filter out `proof`
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

impl From<&CanonicalVerifiableCredential> for VerifiableCredentialTriples {
    fn from(view: &CanonicalVerifiableCredential) -> Self {
        let mut document = view.document.iter().map(|t| t.clone()).collect::<Vec<_>>();
        document.sort_by_cached_key(|t| t.to_string());
        let mut proof = view.proof.iter().map(|t| t.clone()).collect::<Vec<_>>();
        proof.sort_by_cached_key(|t| t.to_string());
        Self { document, proof }
    }
}

pub struct CanonicalVerifiableCredential {
    document: Vec<Triple>,
    document_issued_identifiers_map: HashMap<String, String>,
    proof: Vec<Triple>,
    proof_issued_identifiers_map: HashMap<String, String>,
}

impl CanonicalVerifiableCredential {
    pub fn new(
        mut document: Vec<Triple>,
        document_issued_identifiers_map: HashMap<String, String>,
        mut proof: Vec<Triple>,
        proof_issued_identifiers_map: HashMap<String, String>,
    ) -> Self {
        document.sort_by_cached_key(|t| t.to_string());
        proof.sort_by_cached_key(|t| t.to_string());
        Self {
            document,
            document_issued_identifiers_map,
            proof,
            proof_issued_identifiers_map,
        }
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

struct VpGraphs<'a> {
    metadata: GraphView<'a>,
    proof: GraphView<'a>,
    filters: OrderedGraphViews<'a>,
    disclosed_vcs: OrderedVCGraphViews<'a>,
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
impl<'a> From<&'a OrderedGraphNameRef<'a>> for &'a GraphNameRef<'a> {
    fn from(value: &'a OrderedGraphNameRef<'a>) -> Self {
        &value.0
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

#[derive(Debug)]
struct StatementIndexMap {
    document_map: Vec<usize>,
    document_len: usize,
    proof_map: Vec<usize>,
    proof_len: usize,
}

type OrderedGraphViews<'a> = BTreeMap<OrderedGraphNameRef<'a>, GraphView<'a>>;
type OrderedVCGraphViews<'a> = BTreeMap<OrderedGraphNameRef<'a>, VerifiableCredentialView<'a>>;
type OrderedCanonicalVCGraphs<'a> =
    BTreeMap<OrderedGraphNameRef<'a>, &'a CanonicalVerifiableCredential>;

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

    // get original VCs
    let original_vcs = vcs
        .iter()
        .map(|VcWithDisclosed { vc, .. }| vc)
        .collect::<Vec<_>>();

    // get `proofValue`s from original VCs
    let proof_values = get_proof_values(&original_vcs)?;
    println!("proof values:\n{:#?}\n", proof_values);

    // canonicalize original VCs
    let c14n_original_vcs = canonicalize_original_vcs(&original_vcs)?;
    println!("canonicalized original VC graphs:");
    for c14n_original_vc in &c14n_original_vcs {
        println!(
            "document:\n{}",
            c14n_original_vc
                .document
                .iter()
                .map(|t| format!("{} .\n", t.to_string()))
                .reduce(|l, r| format!("{}{}", l, r))
                .unwrap()
        );
        println!(
            "document issued identifiers map:\n{:#?}\n",
            c14n_original_vc.document_issued_identifiers_map
        );
        println!(
            "proof:\n{}",
            c14n_original_vc
                .proof
                .iter()
                .map(|t| format!("{} .\n", t.to_string()))
                .reduce(|l, r| format!("{}{}", l, r))
                .unwrap()
        );
        println!(
            "proof issued identifiers map:\n{:#?}\n",
            c14n_original_vc.proof_issued_identifiers_map
        );
    }

    // remove `proofValue`s from disclosed VCs
    let disclosed_vcs = vcs
        .iter()
        .map(
            |VcWithDisclosed {
                 disclosed: VerifiableCredential { document, proof },
                 ..
             }| {
                VerifiableCredential::new(
                    Graph::from_iter(document),
                    Graph::from_iter(proof.iter().filter(|t| t.predicate != PROOF_VALUE)),
                )
            },
        )
        .collect();

    // build VP (without proof yet) based on disclosed VCs
    let (vp, vc_graph_names) = build_vp(&disclosed_vcs)?;
    println!("vp:\n{}\n", vp.to_string());

    // canonicalize VP
    let c14n_map_for_disclosed = issue(&vp)?;
    let canonicalized_vp = relabel(&vp, &c14n_map_for_disclosed)?;
    println!("issued identifiers map:\n{:#?}\n", c14n_map_for_disclosed);
    println!("canonicalized VP:\n{}", serialize(&canonicalized_vp));

    // compose extended deanonymization map with issued identifiers map for original VC graphs
    let mut c14n_map_for_original_vc = HashMap::<String, String>::new();
    for CanonicalVerifiableCredential {
        document_issued_identifiers_map,
        proof_issued_identifiers_map,
        ..
    } in &c14n_original_vcs
    {
        for (k, v) in document_issued_identifiers_map {
            if c14n_map_for_original_vc.contains_key(k) {
                return Err(DeriveProofError::BlankNodeCollisionError);
            } else {
                c14n_map_for_original_vc.insert(k.to_string(), v.to_string());
            }
        }
        for (k, v) in proof_issued_identifiers_map {
            if c14n_map_for_original_vc.contains_key(k) {
                return Err(DeriveProofError::BlankNodeCollisionError);
            } else {
                c14n_map_for_original_vc.insert(k.to_string(), v.to_string());
            }
        }
    }

    // construct extended deanonymization map
    let extended_deanon_map = extend_deanon_map(
        deanon_map,
        &c14n_map_for_disclosed,
        &c14n_map_for_original_vc,
    )?;
    println!("extended deanon map:");
    for (f, t) in &extended_deanon_map {
        println!("{}: {}", f.to_string(), t.to_string());
    }
    println!("");

    // decompose canonicalized VP into graphs
    let VpGraphs {
        metadata: vp_metadata,
        proof: vp_proof,
        filters: filters_graph,
        disclosed_vcs: c14n_disclosed_vc_graphs,
    } = decompose_vp(&canonicalized_vp)?;
    println!("VP metadata:\n{}\n", vp_metadata);
    println!("VP proof graph:\n{}\n", vp_proof);
    println!("filter graphs:");
    for (_, filter_graph) in &filters_graph {
        println!("{}", filter_graph);
    }
    println!("");
    println!("disclosed VC graphs:");
    for (k, vc) in &c14n_disclosed_vc_graphs {
        println!("{}:", k);
        println!("{}", vc.document);
        println!("{}", vc.proof);
    }

    // associate original VCs with canonicalized graph names of disclosed VCs
    let c14n_original_vc_graphs: OrderedCanonicalVCGraphs = reassociate_vc_with_disclosed(
        &c14n_original_vcs,
        &c14n_disclosed_vc_graphs,
        &extended_deanon_map,
        &vc_graph_names,
    )?;

    // generate index map
    let index_map = gen_index_map(
        c14n_original_vc_graphs,
        c14n_disclosed_vc_graphs,
        &extended_deanon_map,
    )?;
    println!("index_map:\n{:#?}\n", index_map);

    // TODO: calculate meta statements

    // TODO: derive proof value

    Ok(canonicalized_vp)
}

// function to remove from the VP the multiple graphs that are reachable from `source` via `link`
fn remove_graphs<'a>(
    vp_graphs: &mut OrderedGraphViews<'a>,
    source: &GraphView<'a>,
    link: NamedNodeRef,
) -> Result<OrderedGraphViews<'a>, DeriveProofError> {
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
        .collect::<Result<OrderedGraphViews, DeriveProofError>>()
}

// function to remove from the VP the single graph that is reachable from `source` via `link`
fn remove_graph<'a>(
    vp_graphs: &mut OrderedGraphViews<'a>,
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

fn get_proof_values<'a>(
    original_vcs: &'a Vec<&'a VerifiableCredential>,
) -> Result<Vec<&'a str>, DeriveProofError> {
    original_vcs
        .iter()
        .map(|VerifiableCredential { proof, .. }| {
            match proof
                .triples_for_predicate(PROOF_VALUE)
                .next()
                .ok_or(DeriveProofError::VCWithoutProofValue)?
                .object
            {
                TermRef::Literal(literal) => Ok(literal.value()),
                _ => Err(DeriveProofError::VCWithInvalidProofValue),
            }
        })
        .collect::<Result<Vec<_>, _>>()
}

fn canonicalize_original_vcs(
    original_vcs: &Vec<&VerifiableCredential>,
) -> Result<Vec<CanonicalVerifiableCredential>, DeriveProofError> {
    original_vcs
        .iter()
        .map(|VerifiableCredential { document, proof }| {
            let document_dataset = Dataset::from_iter(
                document
                    .iter()
                    .map(|t| Quad::new(t.subject, t.predicate, t.object, GraphName::DefaultGraph)),
            );
            let proof_dataset = Dataset::from_iter(
                proof
                    .iter()
                    .map(|t| Quad::new(t.subject, t.predicate, t.object, GraphName::DefaultGraph)),
            );
            let document_issued_identifiers_map = issue(&document_dataset)?;
            let proof_issued_identifiers_map = issue(&proof_dataset)?;

            let canonicalized_document =
                relabel(&document_dataset, &document_issued_identifiers_map)?;
            let canonicalized_proof = relabel(&proof_dataset, &proof_issued_identifiers_map)?;
            Ok(CanonicalVerifiableCredential::new(
                canonicalized_document
                    .iter()
                    .map(|q| q.into_owned().into())
                    .collect(),
                document_issued_identifiers_map,
                canonicalized_proof
                    .into_iter()
                    .map(|q| q.into_owned().into())
                    .collect(),
                proof_issued_identifiers_map,
            ))
        })
        .collect::<Result<Vec<_>, DeriveProofError>>()
}

fn build_vp(
    disclosed_vcs: &Vec<VerifiableCredential>,
) -> Result<(Dataset, Vec<BlankNode>), DeriveProofError> {
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
    let mut vc_graph_names = Vec::with_capacity(disclosed_vcs.len());
    let vc_quads = disclosed_vcs
        .iter()
        .map(|VerifiableCredential { document, proof }| {
            let document_graph_name = BlankNode::default();
            let proof_graph_name = BlankNode::default();

            vc_graph_names.push(document_graph_name.clone());

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
    Ok((vp, vc_graph_names))
}

fn dataset_into_ordered_graphs(dataset: &Dataset) -> OrderedGraphViews {
    let graph_name_set = dataset
        .iter()
        .map(|QuadRef { graph_name, .. }| OrderedGraphNameRef(graph_name))
        .collect::<BTreeSet<_>>();

    graph_name_set
        .into_iter()
        .map(|graph_name| (graph_name.clone(), dataset.graph(graph_name)))
        .collect()
}

fn extend_deanon_map(
    deanon_map: &HashMap<BlankNode, Term>,
    issued_identifiers_map: &HashMap<String, String>,
    c14n_map_for_original_vc: &HashMap<String, String>,
) -> Result<HashMap<BlankNode, Term>, DeriveProofError> {
    issued_identifiers_map
        .into_iter()
        .map(|(bnid, cnid)| {
            let mapped_bnid = match c14n_map_for_original_vc.get(bnid) {
                Some(v) => v,
                None => bnid,
            };
            let bnode = BlankNode::new(mapped_bnid)?;
            if let Some(v) = deanon_map.get(&bnode) {
                Ok((BlankNode::new(cnid)?, v.clone()))
            } else {
                Ok((BlankNode::new(cnid)?, bnode.into()))
            }
        })
        .collect::<Result<HashMap<_, _>, DeriveProofError>>()
}

fn decompose_vp<'a>(vp: &'a Dataset) -> Result<VpGraphs<'a>, DeriveProofError> {
    let mut vp_graphs = dataset_into_ordered_graphs(vp);
    println!("canonicalized VP graphs:");
    for g in vp_graphs.keys() {
        println!("{}:\n{}\n", g, vp_graphs.get(g).unwrap());
    }

    // extract VP metadata (default graph)
    let metadata = vp_graphs
        .remove(&OrderedGraphNameRef(GraphNameRef::DefaultGraph))
        .ok_or(DeriveProofError::InternalError(
            "VP graphs must have default graph".to_owned(),
        ))?;

    // extract VP proof graph
    let proof = remove_graph(&mut vp_graphs, &metadata, PROOF)?;

    // extract filter graphs if any
    let filters = remove_graphs(&mut vp_graphs, &proof, FILTER)?;

    // extract VC graphs
    let vcs = remove_graphs(&mut vp_graphs, &metadata, VERIFIABLE_CREDENTIAL)?;

    // extract VC proof graphs
    let disclosed_vcs = vcs
        .into_iter()
        .map(|(vc_graph_name, vc)| {
            let vc_proof = remove_graph(&mut vp_graphs, &vc, PROOF)?;
            Ok((vc_graph_name, VerifiableCredentialView::new(vc, vc_proof)))
        })
        .collect::<Result<OrderedVCGraphViews, DeriveProofError>>()?;

    // check if `vp_graphs` is empty
    if !vp_graphs.is_empty() {
        return Err(DeriveProofError::InvalidVP);
    }

    Ok(VpGraphs {
        metadata,
        proof,
        filters,
        disclosed_vcs,
    })
}

fn reassociate_vc_with_disclosed<'a>(
    c14n_original_vcs: &'a Vec<CanonicalVerifiableCredential>,
    c14n_disclosed_vc_graphs: &OrderedVCGraphViews<'a>,
    extended_deanon_map: &'a HashMap<BlankNode, Term>,
    vc_graph_names: &Vec<BlankNode>,
) -> Result<OrderedCanonicalVCGraphs<'a>, DeriveProofError> {
    c14n_disclosed_vc_graphs
        .keys()
        .map(|k| {
            let vc_graph_name_c14n: &GraphNameRef = k.into();
            let vc_graph_name: &BlankNodeRef = match vc_graph_name_c14n {
                GraphNameRef::BlankNode(n) => Ok(n),
                _ => Err(DeriveProofError::InternalError(
                    "invalid VC graph name".to_string(),
                )),
            }?;
            let vc_graph_name = extended_deanon_map.get(&(*vc_graph_name).into()).ok_or(
                DeriveProofError::InternalError("invalid VC graph name".to_string()),
            )?;
            let vc_graph_name = match vc_graph_name {
                Term::BlankNode(n) => Ok(n),
                _ => Err(DeriveProofError::InternalError(
                    "invalid VC graph name".to_string(),
                )),
            }?;
            let index = vc_graph_names
                .iter()
                .position(|v| v == vc_graph_name)
                .ok_or(DeriveProofError::InternalError(
                    "invalid VC index".to_string(),
                ))?;
            let vc = c14n_original_vcs
                .get(index)
                .ok_or(DeriveProofError::InternalError(
                    "invalid VC index".to_string(),
                ))?;
            Ok((k.clone(), vc))
        })
        .collect::<Result<_, DeriveProofError>>()
}

fn gen_index_map(
    c14n_original_vc_graphs: OrderedCanonicalVCGraphs,
    c14n_disclosed_vc_graphs: OrderedVCGraphViews,
    extended_deanon_map: &HashMap<BlankNode, Term>,
) -> Result<Vec<StatementIndexMap>, DeriveProofError> {
    // assert the keys of two VC graphs are equivalent
    if !c14n_original_vc_graphs
        .keys()
        .eq(c14n_disclosed_vc_graphs.keys())
    {
        return Err(DeriveProofError::InternalError(
            "gen_index_map: the keys of two VC graphs must be equivalent".to_string(),
        ));
    }

    // convert original VC graphs and VC proof graphs into `Vec<Triple>`s
    let c14n_original_vc_triples = c14n_original_vc_graphs
        .into_iter()
        .map(|(_, view)| view.into())
        .collect::<Vec<VerifiableCredentialTriples>>();
    println!("canonicalized original VC graphs (sorted):");
    for VerifiableCredentialTriples { document, proof } in &c14n_original_vc_triples {
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

    // convert disclosed VC graphs and VC proof graphs into `Vec<Triple>`s
    let mut c14n_disclosed_vc_triples = c14n_disclosed_vc_graphs
        .into_iter()
        .map(|(_, view)| view.into())
        .collect::<Vec<VerifiableCredentialTriples>>();
    println!("canonicalized disclosed VC graphs (sorted):");
    for VerifiableCredentialTriples { document, proof } in &c14n_disclosed_vc_triples {
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

    // deanonymize each disclosed VC triples, keeping their orders
    for VerifiableCredentialTriples { document, proof } in &mut c14n_disclosed_vc_triples {
        for triple in document.into_iter() {
            deanonymize_subject(extended_deanon_map, &mut triple.subject)?;
            deanonymize_term(extended_deanon_map, &mut triple.object)?;
        }
        for triple in proof.into_iter() {
            deanonymize_subject(extended_deanon_map, &mut triple.subject)?;
            deanonymize_term(extended_deanon_map, &mut triple.object)?;
        }
    }
    println!("deanonymized canonicalized disclosed VC graphs:");
    for VerifiableCredentialTriples { document, proof } in &c14n_disclosed_vc_triples {
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

    // calculate index mapping
    let index_map = c14n_disclosed_vc_triples
        .iter()
        .zip(c14n_original_vc_triples)
        .map(
            |(
                VerifiableCredentialTriples {
                    document: disclosed_document,
                    proof: disclosed_proof,
                },
                VerifiableCredentialTriples {
                    document: original_document,
                    proof: original_proof,
                },
            )| {
                let document_map = disclosed_document
                    .iter()
                    .map(|disclosed_triple| {
                        original_document
                            .iter()
                            .position(|original_triple| *disclosed_triple == *original_triple)
                            .ok_or(DeriveProofError::DisclosedVCIsNotSubsetOfOriginalVC)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let proof_map = disclosed_proof
                    .iter()
                    .map(|disclosed_triple| {
                        original_proof
                            .iter()
                            .position(|original_triple| *disclosed_triple == *original_triple)
                            .ok_or(DeriveProofError::DisclosedVCIsNotSubsetOfOriginalVC)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let document_len = original_document.len();
                let proof_len = original_proof.len();
                Ok(StatementIndexMap {
                    document_map,
                    document_len,
                    proof_map,
                    proof_len,
                })
            },
        )
        .collect::<Result<Vec<_>, DeriveProofError>>()?;

    Ok(index_map)
}
