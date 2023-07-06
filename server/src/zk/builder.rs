use super::{
    error::ZkSparqlError,
    nymizer::Pseudonymizer,
    parser::{ZkQuery, ZkQueryValues},
    PROOF_GRAPH_SUFFIX, SUBJECT_GRAPH_SUFFIX, VC_VARIABLE_PREFIX,
};

use oxigraph::store::Store;
use oxrdf::{
    GraphName, GraphNameRef, Literal, NamedNode, NamedNodeRef, Quad, Subject, Term, TermRef,
    Variable,
};
use spargebra::{
    algebra::{Expression, Function, GraphPattern},
    term::{NamedNodePattern, TermPattern, TriplePattern},
};
use std::collections::{HashMap, HashSet};

const RDF_TYPE: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type";
const VERIFIABLE_CREDENTIAL: &str = "https://www.w3.org/2018/credentials#VerifiableCredential";

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

pub fn build_credential_metadata(
    cred_graph_ids: &HashSet<GraphName>,
    store: &Store,
    nymizer: &mut Pseudonymizer,
) -> Result<Vec<Quad>, ZkSparqlError> {
    let creds = cred_graph_ids
        .iter()
        .map(|cred_graph_id| {
            let quads = store
                .quads_for_pattern(None, None, None, Some(cred_graph_id.into()))
                .collect::<Result<Vec<_>, _>>();
            let cred_ids: Vec<_> = store
                .quads_for_pattern(
                    None,
                    Some(NamedNodeRef::new_unchecked(RDF_TYPE)),
                    Some(TermRef::from(NamedNodeRef::new_unchecked(
                        VERIFIABLE_CREDENTIAL,
                    ))),
                    Some(cred_graph_id.into()),
                )
                .map(|quad| quad.map(|quad| quad.subject))
                .collect::<Result<Vec<_>, _>>()?;
            let cred_ids: HashSet<NamedNode> = cred_ids
                .iter()
                .map(|c| match c {
                    Subject::NamedNode(n) => Ok(n.clone()),
                    Subject::BlankNode(n) => {
                        Err(ZkSparqlError::BlankNodeMustBeSkolemized(n.clone()))
                    }
                    Subject::Triple(_) => Err(ZkSparqlError::FailedBuildingCredentialMetadata),
                })
                .collect::<Result<HashSet<_>, _>>()?;
            match quads {
                Ok(quads) => Ok(quads
                    .into_iter()
                    .map(|quad| nymizer.pseudonymize_quad(quad, &cred_ids))
                    .collect::<Vec<_>>()),
                Err(_) => Err(ZkSparqlError::FailedBuildingCredentialMetadata),
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    creds.into_iter().flatten().collect()
}

pub fn build_proofs(
    cred_ids: &HashSet<GraphName>,
    store: &Store,
) -> Result<Vec<Quad>, ZkSparqlError> {
    let proofs = cred_ids
        .iter()
        .map(|cred_id| {
            let proof_id = match cred_id {
                GraphName::NamedNode(n) => format!("{}{}", n.as_str(), PROOF_GRAPH_SUFFIX),
                _ => return Err(ZkSparqlError::FailedBuildingDisclosedDataset),
            };
            Ok(store
                .quads_for_pattern(
                    None,
                    None,
                    None,
                    Some(GraphNameRef::from(NamedNodeRef::new(&proof_id)?)),
                )
                .collect::<Result<Vec<_>, _>>()?)
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(proofs.into_iter().flatten().collect())
}
