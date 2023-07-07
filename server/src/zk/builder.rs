use super::{
    context::{
        ASSERTION_METHOD, CREATED, CRYPTOSUITE, DATA_INTEGRITY_PROOF, PROOF, PROOF_PURPOSE,
        PROOF_VALUE, RDF_TYPE, VERIFIABLE_CREDENTIAL, VERIFIABLE_CREDENTIAL_TYPE,
        VERIFIABLE_PRESENTATION_TYPE, VERIFICATION_METHOD,
    },
    error::ZkSparqlError,
    nymizer::Pseudonymizer,
    parser::{ZkQuery, ZkQueryValues},
    CRYPTOSUITE_FOR_VP, PROOF_GRAPH_SUFFIX, SKOLEM_IRI_PREFIX, SUBJECT_GRAPH_SUFFIX,
    VC_VARIABLE_PREFIX,
};

use chrono::offset::Utc;
use oxigraph::store::Store;
use oxrdf::{
    vocab::xsd, BlankNode, GraphName, Literal, NamedNode, NamedNodeRef, Quad, Subject, Term,
    TermRef, Variable,
};
use spargebra::{
    algebra::{Expression, Function, GraphPattern},
    term::{NamedNodePattern, TermPattern, TriplePattern},
};
use std::collections::{HashMap, HashSet};

// construct an extended query to identify credentials to be disclosed
struct ExtendedQuery {
    pattern: GraphPattern,
    variables: Vec<Variable>,
}

#[derive(Debug)]
pub struct TriplePatternWithGraphVar {
    triple_pattern: TriplePattern,
    graph_var: Variable,
}

#[derive(Debug)]
pub struct VerifiableCredential {
    pub metadata: Vec<Quad>,
    pub subject: Vec<Quad>,
    pub proof: Vec<Quad>,
}

pub fn build_extended_fetch_query(query: &ZkQuery) -> Result<spargebra::Query, ZkSparqlError> {
    let extended_graph_variables: Vec<_> = (0..query.patterns.len())
        .map(|i| Variable::new_unchecked(format!("{}{}", VC_VARIABLE_PREFIX, i)))
        .collect();
    let extended_triple_patterns =
        build_extended_triple_patterns(&query.patterns, &extended_graph_variables)?;

    let ExtendedQuery { pattern, variables } =
        build_extended_query(query, extended_graph_variables, &extended_triple_patterns)?;

    Ok(spargebra::Query::Select {
        dataset: None,
        pattern: GraphPattern::Distinct {
            inner: Box::new(GraphPattern::Project {
                inner: Box::new(pattern),
                variables,
            }),
        },
        base_iri: None,
    })
}

pub fn build_extended_prove_query(
    query: &ZkQuery,
) -> Result<(spargebra::Query, Vec<TriplePatternWithGraphVar>), ZkSparqlError> {
    let new_query = replace_blanknodes_with_variables(query);

    let extended_graph_variables: Vec<_> = (0..new_query.patterns.len())
        .map(|i| Variable::new_unchecked(format!("{}{}", VC_VARIABLE_PREFIX, i)))
        .collect();
    let extended_triple_patterns =
        build_extended_triple_patterns(&new_query.patterns, &extended_graph_variables)?;

    let ExtendedQuery { pattern, .. } = build_extended_query(
        &new_query,
        extended_graph_variables,
        &extended_triple_patterns,
    )?;

    Ok((
        spargebra::Query::Select {
            dataset: None,
            pattern: GraphPattern::Distinct {
                inner: Box::new(GraphPattern::Project {
                    inner: Box::new(pattern),
                    variables: new_query.in_scope_variables.into_iter().collect(),
                }),
            },
            base_iri: None,
        },
        extended_triple_patterns,
    ))
}

// Replace the blank nodes generated when expanding the property paths
// with variables to get underlying named nodes in the credentials
// using extended query
fn replace_blanknodes_with_variables(query: &ZkQuery) -> ZkQuery {
    let mut in_scope_variables = query.in_scope_variables.clone();

    let mut blanknode_to_variable = |term: &TermPattern| -> TermPattern {
        match term {
            TermPattern::BlankNode(b) => {
                let v = Variable::new_unchecked(b.as_str());
                in_scope_variables.insert(v.clone());
                TermPattern::Variable(v)
            } // TODO: error check
            _ => term.clone(),
        }
    };

    let new_patterns: Vec<TriplePattern> = query
        .patterns
        .iter()
        .map(|p| TriplePattern {
            subject: blanknode_to_variable(&p.subject),
            predicate: p.predicate.clone(),
            object: blanknode_to_variable(&p.object),
        })
        .collect();

    ZkQuery {
        disclosed_variables: query.disclosed_variables.clone(),
        in_scope_variables,
        patterns: new_patterns,
        filter: query.filter.clone(),
        values: query.values.clone(),
        limit: query.limit.clone(),
    }
}

fn build_extended_triple_patterns(
    patterns: &[TriplePattern],
    extended_graph_variables: &[Variable],
) -> Result<Vec<TriplePatternWithGraphVar>, ZkSparqlError> {
    patterns
        .iter()
        .enumerate()
        .map(|(i, triple_pattern)| {
            let graph_var = extended_graph_variables
                .get(i)
                .ok_or(ZkSparqlError::ExtendedQueryFailed)?;
            Ok(TriplePatternWithGraphVar {
                triple_pattern: triple_pattern.clone(),
                graph_var: graph_var.clone(),
            })
        })
        .collect::<Result<Vec<TriplePatternWithGraphVar>, ZkSparqlError>>()
}

fn build_extended_query(
    query: &ZkQuery,
    extended_graph_variables: Vec<Variable>,
    extended_triple_patterns: &[TriplePatternWithGraphVar],
) -> Result<ExtendedQuery, ZkSparqlError> {
    // wrap each triple pattern with a GRAPH clause
    let extended_bgp = extended_triple_patterns
        .iter()
        .map(|p| {
            Ok(GraphPattern::Graph {
                name: NamedNodePattern::Variable(p.graph_var.clone()),
                inner: Box::new(GraphPattern::Bgp {
                    patterns: vec![p.triple_pattern.clone()],
                }),
            })
        })
        .collect::<Result<Vec<GraphPattern>, ZkSparqlError>>()?
        .into_iter()
        .reduce(|left, right| GraphPattern::Join {
            left: Box::new(left),
            right: Box::new(right),
        })
        .unwrap_or_default();

    // add a VALUE clause, given by the user, to identify the credentials to present
    let extended_bgp_with_values = match &query.values {
        Some(ZkQueryValues {
            variables,
            bindings,
        }) => GraphPattern::Join {
            left: Box::new(GraphPattern::Values {
                variables: variables.clone(),
                bindings: bindings.clone(),
            }),
            right: Box::new(extended_bgp),
        },
        _ => extended_bgp,
    };

    // create FILTER clauses to limit the search target to the subject graphs
    let Some(subject_filter_expr) = extended_graph_variables
        .iter()
        .map(|gvar| {
            Expression::FunctionCall(
                Function::StrEnds,
                vec![
                    Expression::FunctionCall(
                        Function::Str,
                        vec![Expression::Variable(gvar.clone())],
                    ),
                    Expression::Literal(Literal::new_simple_literal(SUBJECT_GRAPH_SUFFIX)),
                ],
            )
        })
        .reduce(|left, right| Expression::And(Box::new(left), Box::new(right)))
        else { return Err(ZkSparqlError::ExtendedQueryFailed) };

    // add user-provided FILTER clauses, if any
    let extended_filter_expr = match &query.filter {
        Some(expr) => Expression::And(Box::new(expr.clone()), Box::new(subject_filter_expr)),
        None => subject_filter_expr,
    };

    // combine with extended BGP
    let extended_bgp_with_values_and_filter = GraphPattern::Filter {
        expr: extended_filter_expr,
        inner: Box::new(extended_bgp_with_values),
    };

    // add the LIMIT if specified by the user
    let extended_graph_pattern = match &query.limit {
        Some(limit) => GraphPattern::Slice {
            inner: Box::new(extended_bgp_with_values_and_filter),
            start: limit.start,
            length: limit.length,
        },
        _ => extended_bgp_with_values_and_filter,
    };

    // form a variable list by combining the variables specified by the user
    // and the extended graph variables `__vc*` added here
    let mut extended_variables = query.disclosed_variables.clone();
    extended_variables.extend(extended_graph_variables.into_iter());

    Ok(ExtendedQuery {
        pattern: extended_graph_pattern,
        variables: extended_variables,
    })
}

pub fn build_disclosed_subjects(
    solutions: &[HashMap<Variable, Term>],
    extended_triple_patterns: &[TriplePatternWithGraphVar],
) -> Result<Vec<Quad>, ZkSparqlError> {
    let disclosed_subjects = solutions
        .iter()
        .map(|solution| {
            extended_triple_patterns
                .iter()
                .map(|pattern| build_disclosed_subject(solution, pattern))
                .collect::<Result<Vec<_>, ZkSparqlError>>()
        })
        .collect::<Result<Vec<_>, ZkSparqlError>>()?;
    Ok(disclosed_subjects.into_iter().flatten().collect())
}

fn build_disclosed_subject(
    solution: &HashMap<Variable, Term>,
    pattern_with_graph_var: &TriplePatternWithGraphVar,
) -> Result<Quad, ZkSparqlError> {
    let TriplePatternWithGraphVar {
        triple_pattern,
        graph_var,
    } = pattern_with_graph_var;

    let g = match solution
        .get(graph_var)
        .ok_or(ZkSparqlError::FailedBuildingDisclosedSubject)?
    {
        Term::NamedNode(n) => GraphName::NamedNode(n.clone()),
        _ => return Err(ZkSparqlError::FailedBuildingDisclosedSubject),
    };

    let s = match &triple_pattern.subject {
        TermPattern::Variable(v) => {
            let term = solution
                .get(v)
                .ok_or(ZkSparqlError::FailedBuildingDisclosedSubject)?;
            match term {
                Term::NamedNode(n) => Subject::NamedNode(n.clone()),
                _ => return Err(ZkSparqlError::FailedBuildingDisclosedSubject),
            }
        }
        TermPattern::NamedNode(n) => Subject::NamedNode(n.clone()),
        TermPattern::BlankNode(n) => Subject::BlankNode(n.clone()),
        _ => return Err(ZkSparqlError::FailedBuildingDisclosedSubject),
    };

    let p = match &triple_pattern.predicate {
        NamedNodePattern::Variable(v) => {
            let term = solution
                .get(v)
                .ok_or(ZkSparqlError::FailedBuildingDisclosedSubject)?
                .clone();
            match term {
                Term::NamedNode(n) => n,
                _ => return Err(ZkSparqlError::FailedBuildingDisclosedSubject),
            }
        }
        NamedNodePattern::NamedNode(n) => n.clone(),
    };

    let o = match &triple_pattern.object {
        TermPattern::Variable(v) => solution
            .get(v)
            .ok_or(ZkSparqlError::FailedBuildingDisclosedSubject)?
            .clone(),
        TermPattern::NamedNode(n) => Term::NamedNode(n.clone()),
        TermPattern::BlankNode(n) => Term::BlankNode(n.clone()),
        TermPattern::Literal(n) => Term::Literal(n.clone()),
        TermPattern::Triple(_) => return Err(ZkSparqlError::FailedBuildingDisclosedSubject),
    };

    Ok(Quad::new(s, p, o, g))
}

pub fn get_verifiable_credential(
    cred_graph_id: &GraphName,
    store: &Store,
) -> Result<VerifiableCredential, ZkSparqlError> {
    let metadata: Vec<Quad> = store
        .quads_for_pattern(None, None, None, Some(cred_graph_id.as_ref()))
        .collect::<Result<_, _>>()?;

    let subject_graph_id = match cred_graph_id {
        GraphName::NamedNode(n) => Ok(GraphName::NamedNode(NamedNode::new(format!(
            "{}{}",
            n.as_str(),
            SUBJECT_GRAPH_SUFFIX
        ))?)),
        _ => Err(ZkSparqlError::FailedGettingVerifiableCredential),
    }?;
    let subject: Vec<Quad> = store
        .quads_for_pattern(None, None, None, Some(subject_graph_id.as_ref()))
        .collect::<Result<_, _>>()?;

    let proof_graph_id = match cred_graph_id {
        GraphName::NamedNode(n) => Ok(GraphName::NamedNode(NamedNode::new(format!(
            "{}{}",
            n.as_str(),
            PROOF_GRAPH_SUFFIX
        ))?)),
        _ => Err(ZkSparqlError::FailedGettingVerifiableCredential),
    }?;
    let proof: Vec<Quad> = store
        .quads_for_pattern(None, None, None, Some(proof_graph_id.as_ref()))
        .collect::<Result<_, _>>()?;

    Ok(VerifiableCredential {
        metadata,
        subject,
        proof,
    })
}

pub fn pseudonymize_metadata_and_proofs(
    graph_id: &GraphName,
    vc: &VerifiableCredential,
    store: &Store,
    nymizer: &mut Pseudonymizer,
) -> Result<VerifiableCredential, ZkSparqlError> {
    let get_nym_targets = |predicate, object| {
        store
            .quads_for_pattern(None, predicate, object, Some(graph_id.as_ref()))
            .map(|quad| match quad?.subject {
                Subject::NamedNode(n) => Ok(n),
                Subject::BlankNode(n) => Err(ZkSparqlError::BlankNodeMustBeSkolemized(n)),
                Subject::Triple(_) => Err(ZkSparqlError::FailedBuildingCredentialMetadata),
            })
            .collect::<Result<HashSet<_>, _>>()
    };

    let metadata_nym_targets = get_nym_targets(
        Some(NamedNodeRef::new(RDF_TYPE)?),
        Some(TermRef::from(NamedNodeRef::new_unchecked(
            VERIFIABLE_CREDENTIAL_TYPE,
        ))),
    )?;
    let proof_nym_targets = get_nym_targets(
        Some(NamedNodeRef::new(RDF_TYPE)?),
        None, // TODO: `?s rdf:type _:o` is sufficient to identify the proof subject (?s) in the proof graph?
    )?;

    let nymized_metadata = vc
        .metadata
        .iter()
        .map(|quad| nymizer.pseudonymize_quad(quad.clone(), &metadata_nym_targets))
        .collect::<Result<_, _>>()?;
    let nymized_proof = vc
        .proof
        .iter()
        .map(|quad| nymizer.pseudonymize_quad(quad.clone(), &proof_nym_targets))
        .collect::<Result<_, _>>()?;

    Ok(VerifiableCredential {
        metadata: nymized_metadata,
        subject: vec![],
        proof: nymized_proof,
    })
}

pub fn get_proof_values(
    cred_graph_ids: &HashSet<GraphName>,
    store: &Store,
) -> Result<HashMap<GraphName, String>, ZkSparqlError> {
    let proof_graph_ids = gen_proof_graph_ids(cred_graph_ids)?;
    proof_graph_ids
        .iter()
        .map(|proof_graph_id| {
            let proof_values: Vec<_> = store
                .quads_for_pattern(
                    None,
                    Some(NamedNodeRef::new(PROOF_VALUE)?),
                    None,
                    Some(proof_graph_id.as_ref()),
                )
                .map(|quad| match quad {
                    Ok(q) => Ok(q.object),
                    Err(_) => Err(ZkSparqlError::InvalidProofValues),
                })
                .collect::<Result<_, _>>()?;
            if proof_values.len() == 1 {
                match proof_values
                    .get(0)
                    .ok_or(ZkSparqlError::InvalidProofValues)?
                {
                    Term::Literal(v) => Ok((proof_graph_id.clone(), v.value().to_owned())),
                    _ => Err(ZkSparqlError::InvalidProofValues),
                }
            } else {
                Err(ZkSparqlError::InvalidProofValues)
            }
        })
        .collect()
}

fn gen_proof_graph_ids(
    cred_graph_ids: &HashSet<GraphName>,
) -> Result<HashSet<GraphName>, ZkSparqlError> {
    cred_graph_ids
        .iter()
        .map(|cred_graph_id| match cred_graph_id {
            GraphName::NamedNode(n) => Ok(GraphName::NamedNode(NamedNode::new(format!(
                "{}{}",
                n.as_str(),
                PROOF_GRAPH_SUFFIX
            ))?)),
            _ => Err(ZkSparqlError::FailedGettingVerifiableCredential),
        })
        .collect::<Result<_, _>>()
}

pub fn build_vp_metadata(
    cred_graph_ids: &HashSet<GraphName>,
    verification_method: &NamedNode,
) -> Result<Vec<Quad>, ZkSparqlError> {
    let vp_id = Pseudonymizer::generate_pseudonymous_iri();
    let vp_proof_id = Pseudonymizer::generate_pseudonymous_iri();
    let vp_proof_graph_id = Pseudonymizer::generate_pseudonymous_iri();
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
                GraphName::BlankNode(n) => Err(ZkSparqlError::BlankNodeMustBeSkolemized(n.clone())),
                GraphName::DefaultGraph => Err(ZkSparqlError::InternalError(
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
        .collect::<Result<_, ZkSparqlError>>()?;
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

pub fn deskolemize(quad: &Quad) -> Result<Quad, ZkSparqlError> {
    let s = match &quad.subject {
        Subject::NamedNode(n) if is_skolem_iri(n) => Subject::BlankNode(deskolemize_iri(n)?),
        _ => quad.subject.clone(),
    };
    let p = quad.predicate.clone();
    let o = match &quad.object {
        Term::NamedNode(n) if is_skolem_iri(n) => Term::BlankNode(deskolemize_iri(n)?),
        _ => quad.object.clone(),
    };
    let g = match &quad.graph_name {
        GraphName::NamedNode(n) if is_skolem_iri(n) => GraphName::BlankNode(deskolemize_iri(n)?),
        _ => quad.graph_name.clone(),
    };
    Ok(Quad::new(s, p, o, g))
}

pub fn is_skolem_iri(iri: &NamedNode) -> bool {
    iri.as_str().starts_with(SKOLEM_IRI_PREFIX)
}

pub fn deskolemize_iri(iri: &NamedNode) -> Result<BlankNode, ZkSparqlError> {
    let iri_str = iri.as_str();
    if iri.as_str().starts_with(SKOLEM_IRI_PREFIX) {
        BlankNode::new(&iri_str[SKOLEM_IRI_PREFIX.len()..iri_str.len()])
            .map_err(|_| ZkSparqlError::InvalidSkolemIRI(iri.clone()))
    } else {
        Err(ZkSparqlError::InvalidSkolemIRI(iri.clone()))
    }
}
