use crate::{bad_request, base_url, query_results_content_negotiation, HttpError, ReadForWrite};
use nanoid::nanoid;
use oxhttp::model::{Request, Response};
use oxigraph::{
    sparql::{EvaluationError, QueryResults, QuerySolutionIter},
    store::{StorageError, Store},
};
use oxiri::{Iri, IriParseError};
use oxrdf::{GraphName, GraphNameRef, NamedNode, NamedNodeRef, Quad, Subject, Term};
use sparesults::QueryResultsSerializer;
use spargebra::{
    algebra::{Expression, Function, GraphPattern, QueryDataset},
    term::{GroundTerm, Literal, NamedNodePattern, TermPattern, TriplePattern, Variable},
    ParseError,
};
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

pub enum ZkSparqlError {
    ConstructNotSupported,
    DescribeNotSupported,
    InvalidSparqlQuery(ParseError),
    InvalidZkSparqlQuery,
    SparqlEvaluationError(EvaluationError),
    ExtendedQueryFailed,
    FailedBuildingPseudonymousSolution,
    FailedBuildingDisclosedSubject,
    FailedBuildingDisclosedDataset,
}

impl From<EvaluationError> for ZkSparqlError {
    fn from(value: EvaluationError) -> Self {
        Self::SparqlEvaluationError(value)
    }
}

impl From<IriParseError> for ZkSparqlError {
    fn from(_: IriParseError) -> Self {
        Self::FailedBuildingPseudonymousSolution
    }
}

impl From<StorageError> for ZkSparqlError {
    fn from(_: StorageError) -> Self {
        Self::FailedBuildingDisclosedDataset
    }
}

impl Into<HttpError> for ZkSparqlError {
    fn into(self) -> HttpError {
        match self {
            ZkSparqlError::ConstructNotSupported => {
                bad_request("CONSTRUCT is not supported in zk-SPARQL")
            }
            ZkSparqlError::DescribeNotSupported => {
                bad_request("DESCRIBE is not supported in zk-SPARQL")
            }
            ZkSparqlError::InvalidSparqlQuery(e) => {
                bad_request(format!("invalid SPARQL query: {}", e))
            }
            ZkSparqlError::InvalidZkSparqlQuery => bad_request("invalid zk-SPARQL query"),
            ZkSparqlError::SparqlEvaluationError(e) => {
                bad_request(format!("sparql evaluation failed: {}", e))
            }
            ZkSparqlError::ExtendedQueryFailed => bad_request("internal query execution failed"),
            ZkSparqlError::FailedBuildingPseudonymousSolution => {
                bad_request("building pseudonymous solution failed")
            }
            ZkSparqlError::FailedBuildingDisclosedSubject => {
                bad_request("building disclosed subject failed")
            }
            ZkSparqlError::FailedBuildingDisclosedDataset => {
                bad_request("building disclosed dataset failed")
            }
        }
    }
}

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
        let extended_results =
            evaluate_zksparql_fetch(store, &query, request).map_err(std::convert::Into::into)?;
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

#[derive(Debug, Default)]
struct ZkQuery {
    disclosed_variables: Vec<Variable>,
    in_scope_variables: HashSet<Variable>,
    patterns: Vec<TriplePattern>,
    filter: Option<Expression>,
    values: Option<ZkQueryValues>,
    limit: Option<ZkQueryLimit>,
}

#[derive(Debug, Default, Clone)]
struct ZkQueryValues {
    variables: Vec<Variable>,
    bindings: Vec<Vec<Option<GroundTerm>>>,
}

#[derive(Debug, Default, Clone)]
struct ZkQueryLimit {
    start: usize,
    length: Option<usize>,
}

/// Evaluate a zk-SPARQL query on the Fetch endpoint
fn evaluate_zksparql_fetch(
    store: &Store,
    query: &str,
    request: &Request,
) -> Result<QueryResults, ZkSparqlError> {
    // 1. parse a zk-SPARQL query
    let parsed_zk_query = parse_zk_query(query, Some(&base_url(request)))?;
    println!("parsed_zk_query: {:#?}", parsed_zk_query);

    // 2. build an extended SELECT query to identify credentials to be disclosed
    let extended_query = build_extended_fetch_query(&parsed_zk_query)?;
    println!("extended fetch query: {:#?}", extended_query);
    println!("extended fetch query (SPARQL): {}", extended_query);

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
    println!("parsed_zk_query: {:#?}", parsed_zk_query);

    // 2. build an extended prove query to construct disclosed quads from credentials
    let (extended_query, extended_triple_patterns) = build_extended_prove_query(&parsed_zk_query)?;
    println!("extended prove query: {:#?}", extended_query);
    println!("extended prove query (SPARQL): {}", extended_query);

    // 3. execute the extended prove query to get extended prove solutions
    let extended_results = store.query(extended_query)?;
    let extended_solutions = match extended_results {
        QueryResults::Solutions(solutions) => solutions,
        _ => return Err(ZkSparqlError::ExtendedQueryFailed),
    };

    // 4. build pseudonymous solutions
    let PseudonymousSolutions {
        solutions,
        deanon_map,
    } = build_pseudonymous_solutions(extended_solutions, &parsed_zk_query.disclosed_variables)?;
    println!("pseudonymous solutions: {:#?}", solutions);
    println!("deanon map: {:#?}", deanon_map);

    // 5. build disclosed subjects by assigning pseudonymous solutions to extended prove patterns
    let mut disclosed_subjects = build_disclosed_subjects(&solutions, &extended_triple_patterns)?;

    // 6. build disclosed dataset and proofs
    let cred_ids: HashSet<_> = disclosed_subjects
        .iter()
        .map(|quad| quad.graph_name.clone())
        .collect();

    let mut disclosed_dataset = build_credential_metadata(&cred_ids, store)?;
    disclosed_dataset.append(&mut disclosed_subjects);
    println!(
        "disclosed dataset: {}",
        disclosed_dataset
            .iter()
            .map(|q| q.to_string())
            .reduce(|l, r| format!("{}\n{}", l, r))
            .unwrap_or("".to_string())
    );

    let proofs = build_proofs(&cred_ids, store)?;
    println!(
        "proofs: {}",
        proofs
            .iter()
            .map(|q| q.to_string())
            .reduce(|l, r| format!("{}\n{}", l, r))
            .unwrap_or("".to_string())
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

struct PseudonymousSolutions {
    solutions: Vec<HashMap<Variable, Term>>,
    deanon_map: HashMap<Term, Term>,
}

#[derive(Default)]
struct Pseudonymizer {
    mapping: HashMap<(Variable, Term), Term>,
}

impl Pseudonymizer {
    fn generate_pseudonymous_iri() -> NamedNode {
        let val = nanoid!(21, &PSEUDONYM_ALPHABETS);
        NamedNode::new_unchecked(format!("{}{}", PSEUDONYMOUS_IRI_PREFIX, val))
    }

    fn generate_pseudonymous_var() -> Literal {
        let val = nanoid!(21, &PSEUDONYM_ALPHABETS);
        Literal::new_simple_literal(format!("{}{}", PSEUDONYMOUS_VAR_PREFIX, val))
    }

    fn issue(&mut self, var: &Variable, term: &Term) -> Result<Term, ZkSparqlError> {
        match term {
            Term::NamedNode(n) if n.as_str().starts_with(SKOLEM_IRI_PREFIX) => Ok(term.clone()),
            Term::NamedNode(n) if !n.as_str().starts_with(SKOLEM_IRI_PREFIX) => Ok(self
                .mapping
                .entry((var.clone(), term.clone()))
                .or_insert(Term::NamedNode(Self::generate_pseudonymous_iri()))
                .clone()),
            Term::Literal(_) => Ok(self
                .mapping
                .entry((var.clone(), term.clone()))
                .or_insert(Term::Literal(Self::generate_pseudonymous_var()))
                .clone()),
            _ => Err(ZkSparqlError::FailedBuildingPseudonymousSolution),
        }
    }

    fn get_inverse(&self) -> HashMap<Term, Term> {
        self.mapping
            .iter()
            .map(|((_, t), nym)| (nym.clone(), t.clone()))
            .collect()
    }
}

fn build_pseudonymous_solutions(
    solutions: QuerySolutionIter,
    disclosed_variables: &[Variable],
) -> Result<PseudonymousSolutions, ZkSparqlError> {
    let disclosed_variables: HashSet<_> = disclosed_variables.iter().collect();
    let mut pseudonymizer = Pseudonymizer::default();

    let pseudonymous_solutions: Result<Vec<HashMap<_, _>>, ZkSparqlError> = solutions
        .map(|solution| {
            solution?
                .iter()
                .map(|(var, term)| {
                    let pseudonymized_term = if disclosed_variables.contains(var) {
                        term.clone()
                    } else if var.as_str().starts_with(VC_VARIABLE_PREFIX) {
                        match term {
                            Term::NamedNode(n) => {
                                if n.as_str().ends_with(SUBJECT_GRAPH_SUFFIX) {
                                    Term::NamedNode(NamedNode::new(
                                        &n.as_str()
                                            [0..(n.as_str().len() - SUBJECT_GRAPH_SUFFIX.len())],
                                    )?)
                                } else {
                                    return Err(ZkSparqlError::FailedBuildingPseudonymousSolution);
                                }
                            }
                            _ => return Err(ZkSparqlError::FailedBuildingPseudonymousSolution),
                        }
                    } else {
                        pseudonymizer.issue(var, term)?
                    };
                    Ok((var.clone(), pseudonymized_term))
                })
                .collect()
        })
        .collect();

    Ok(PseudonymousSolutions {
        solutions: pseudonymous_solutions?,
        deanon_map: pseudonymizer.get_inverse(),
    })
}

fn build_credential_metadata(
    cred_ids: &HashSet<GraphName>,
    store: &Store,
) -> Result<Vec<Quad>, ZkSparqlError> {
    let creds = cred_ids
        .iter()
        .map(|cred_id| {
            store
                .quads_for_pattern(None, None, None, Some(cred_id.into()))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(creds.into_iter().flatten().collect())
}

fn build_proofs(cred_ids: &HashSet<GraphName>, store: &Store) -> Result<Vec<Quad>, ZkSparqlError> {
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

fn build_disclosed_subjects(
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

// parse a zk-SPARQL query
fn parse_zk_query(query: &str, base_iri: Option<&str>) -> Result<ZkQuery, ZkSparqlError> {
    let parsed_query =
        spargebra::Query::parse(query, base_iri).map_err(ZkSparqlError::InvalidSparqlQuery)?;
    match parsed_query {
        spargebra::Query::Construct { .. } => Err(ZkSparqlError::ConstructNotSupported),
        spargebra::Query::Describe { .. } => Err(ZkSparqlError::DescribeNotSupported),
        spargebra::Query::Select {
            dataset,
            pattern,
            base_iri,
        } => parse_zk_select(dataset, pattern, base_iri),
        spargebra::Query::Ask {
            dataset,
            pattern,
            base_iri,
        } => parse_zk_ask(dataset, pattern, base_iri),
    }
}

fn parse_zk_select(
    _dataset: Option<QueryDataset>,
    pattern: GraphPattern,
    _base_iri: Option<Iri<String>>,
) -> Result<ZkQuery, ZkSparqlError> {
    println!("original pattern: {:#?}", pattern);

    match pattern {
        GraphPattern::Slice {
            inner,
            start,
            length,
        } => match *inner {
            GraphPattern::Project { inner, variables } => {
                parse_zk_common(*inner, variables, Some(ZkQueryLimit { start, length }))
            }
            _ => Err(ZkSparqlError::InvalidZkSparqlQuery),
        },
        GraphPattern::Project { inner, variables } => parse_zk_common(*inner, variables, None),
        _ => Err(ZkSparqlError::InvalidZkSparqlQuery),
    }
}

fn parse_zk_ask(
    _dataset: Option<QueryDataset>,
    pattern: GraphPattern,
    _base_iri: Option<Iri<String>>,
) -> Result<ZkQuery, ZkSparqlError> {
    println!("original pattern: {:#?}", pattern);

    match pattern {
        GraphPattern::Slice {
            inner,
            start,
            length,
        } => parse_zk_common(*inner, vec![], Some(ZkQueryLimit { start, length })),
        _ => parse_zk_common(pattern, vec![], None),
    }
}

struct ZkBgpAndValues {
    bgp: Vec<TriplePattern>,
    values: Option<ZkQueryValues>,
}

fn parse_zk_common(
    pattern: GraphPattern,
    disclosed_variables: Vec<Variable>,
    limit: Option<ZkQueryLimit>,
) -> Result<ZkQuery, ZkSparqlError> {
    let mut in_scope_variables = HashSet::new();
    pattern.on_in_scope_variable(|v| {
        in_scope_variables.insert(v.clone());
    });
    let patterns: Vec<TriplePattern>;
    let mut filter: Option<Expression> = None;
    let mut values: Option<ZkQueryValues> = None;

    match pattern {
        GraphPattern::Filter { expr, inner } => {
            filter = Some(expr);
            match *inner {
                GraphPattern::Bgp { patterns: bgp } => {
                    patterns = bgp;
                }
                GraphPattern::Join { left, right } => match parse_zk_values(*left, *right) {
                    Ok(ZkBgpAndValues { bgp, values: v }) => {
                        patterns = bgp;
                        values = v;
                    }
                    Err(e) => return Err(e),
                },
                _ => return Err(ZkSparqlError::InvalidZkSparqlQuery),
            };
        }
        GraphPattern::Bgp { patterns: bgp } => {
            patterns = bgp;
        }
        GraphPattern::Join { left, right } => match parse_zk_values(*left, *right) {
            Ok(ZkBgpAndValues { bgp, values: v }) => {
                patterns = bgp;
                values = v;
            }
            Err(e) => return Err(e),
        },
        _ => return Err(ZkSparqlError::InvalidZkSparqlQuery),
    };

    Ok(ZkQuery {
        disclosed_variables,
        in_scope_variables,
        patterns,
        filter,
        values,
        limit,
    })
}

fn parse_zk_values(
    left: GraphPattern,
    right: GraphPattern,
) -> Result<ZkBgpAndValues, ZkSparqlError> {
    match (left, right) {
        (
            GraphPattern::Values {
                variables,
                bindings,
            },
            GraphPattern::Bgp { patterns: bgp },
        )
        | (
            GraphPattern::Bgp { patterns: bgp },
            GraphPattern::Values {
                variables,
                bindings,
            },
        ) => Ok(ZkBgpAndValues {
            bgp,
            values: Some(ZkQueryValues {
                variables,
                bindings,
            }),
        }),
        _ => Err(ZkSparqlError::InvalidZkSparqlQuery),
    }
}

// construct an extended query to identify credentials to be disclosed
struct ExtendedQuery {
    pattern: GraphPattern,
    variables: Vec<Variable>,
}

fn build_extended_fetch_query(query: &ZkQuery) -> Result<spargebra::Query, ZkSparqlError> {
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

fn build_extended_prove_query(
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

#[derive(Debug)]
struct TriplePatternWithGraphVar {
    triple_pattern: TriplePattern,
    graph_var: Variable,
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

fn prove(
    store: &Store,
    parsed_zk_query: &ZkQuery,
    extended_results: &QueryResults,
) -> Option<String> {
    println!("!!! prove (TBD) !!!");

    Some("".to_string())
}
