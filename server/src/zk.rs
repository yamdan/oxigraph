use crate::{bad_request, base_url, query_results_content_negotiation, HttpError, ReadForWrite};
use nanoid::nanoid;
use oxhttp::model::{Request, Response};
use oxigraph::{
    sparql::{EvaluationError, QueryResults, QuerySolutionIter},
    store::Store,
};
use oxiri::Iri;
use oxrdf::{NamedNode, Term, Triple};
use sparesults::QueryResultsSerializer;
use spargebra::{
    algebra::{Expression, Function, GraphPattern, QueryDataset},
    term::{GroundTerm, Literal, NamedNodePattern, TermPattern, TriplePattern, Variable},
    ParseError,
};
use std::{
    collections::{HashMap, HashSet},
    iter::zip,
};
use url::form_urlencoded;

const SUBJECT_GRAPH_SUFFIX: &str = ".subject";
const VC_VARIABLE_PREFIX: &str = "__vc";

pub enum ZkSparqlError {
    ConstructNotSupported,
    DescribeNotSupported,
    InvalidSparqlQuery(ParseError),
    InvalidZkSparqlQuery,
    SparqlEvaluationError(EvaluationError),
    ValuesNotExist, // query to the prove endpoint requires VALUES
    ExtendedQueryFailed,
    FailedBuildingPseudonymousSolution,
}

impl From<EvaluationError> for ZkSparqlError {
    fn from(value: EvaluationError) -> Self {
        Self::SparqlEvaluationError(value)
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
            ZkSparqlError::ValuesNotExist => {
                bad_request("query for prove endpoint requires VALUES clause")
            }
            ZkSparqlError::ExtendedQueryFailed => bad_request("internal query execution failed"),
            ZkSparqlError::FailedBuildingPseudonymousSolution => {
                bad_request("building pseudonymous solution failed")
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
        evaluate_zksparql_prove(store, &query, request).map_err(|e| e.into())
    } else {
        let extended_results =
            evaluate_zksparql_fetch(store, &query, request).map_err(|e| e.into())?;
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
        .map_err(|e| ZkSparqlError::SparqlEvaluationError(e))
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
    let values = match &parsed_zk_query.values {
        Some(v) => v,
        None => return Err(ZkSparqlError::ValuesNotExist), // TODO: allow query without VALUES
    };

    let mut graphs: HashMap<_, Vec<_>> = HashMap::new();
    for (var, val) in zip(&values.variables, &values.bindings[0]) {
        graphs.entry(val).or_insert_with(Vec::new).push(var);
    }

    let extended_query = build_extended_prove_query(&parsed_zk_query)?;
    println!("extended prove query: {:#?}", extended_query);
    println!("extended prove query (SPARQL): {}", extended_query);

    // 3. execute the extended prove query to get extended prove solutions
    let extended_results = store.query(extended_query)?;

    let extended_solutions = match extended_results {
        QueryResults::Solutions(solutions) => solutions,
        _ => return Err(ZkSparqlError::ExtendedQueryFailed),
    };

    // TODO: build pseudonymous solutions
    let PseudonymousSolutions {
        solutions,
        deanon_map: mapping,
    } = build_pseudonymous_solutions(&extended_solutions, &parsed_zk_query.disclosed_variables)?;

    // TODO: assign pseudonymous solutions to extended prove patterns
    let disclosed_subjects = solutions.iter().map(|solution| {
        parsed_zk_query
            .patterns
            .iter()
            .map(move |pattern| assign_solution_to_pattern(solution, pattern))
    });

    // 4. return query results
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

struct PseudonymousSolutions<'a> {
    solutions: Vec<HashMap<&'a Variable, &'a Term>>,
    deanon_map: HashMap<Term, Term>,
}

#[derive(Default)]
struct PseudonymIssuer<'a> {
    map_to_pseudonym: HashMap<(&'a Variable, &'a Term), Term>,
}

const PSEUDONYMOUS_IRI_PREFIX: &str = "urn:bnid:";
const PSEUDONYMOUS_VAR_PREFIX: &str = "urn:var:";

impl<'a> PseudonymIssuer<'a> {
    fn generate_pseudonymous_iri() -> NamedNode {
        let val = nanoid!();
        NamedNode::new_unchecked(format!("{}{}", PSEUDONYMOUS_IRI_PREFIX, val))
    }

    fn generate_pseudonymous_var() -> Literal {
        let val = nanoid!();
        Literal::new_simple_literal(format!("{}{}", PSEUDONYMOUS_VAR_PREFIX, val))
    }

    fn issue(&mut self, var: &'a Variable, term: &'a Term) -> Result<&Term, ZkSparqlError> {
        match term {
            Term::NamedNode(_) => Ok(self
                .map_to_pseudonym
                .entry((var, term))
                .or_insert(Term::NamedNode(Self::generate_pseudonymous_iri()))),
            Term::Literal(_) => Ok(self
                .map_to_pseudonym
                .entry((var, term))
                .or_insert(Term::Literal(Self::generate_pseudonymous_var()))),
            _ => Err(ZkSparqlError::FailedBuildingPseudonymousSolution),
        }
    }

    fn generate_deanon_map(&self) -> HashMap<Term, Term> {
        self.map_to_pseudonym
            .iter()
            .map(|((_, t), nym)| (nym.clone(), *t.clone()))
            .collect()
    }
}

fn build_pseudonymous_solutions<'a>(
    solutions: &QuerySolutionIter,
    disclosed_variables: &Vec<Variable>,
) -> Result<PseudonymousSolutions<'a>, ZkSparqlError> {
    let disclosed_variables: HashSet<_> = disclosed_variables.iter().collect();
    let nym_issuer = PseudonymIssuer::default();

    let mut pseudonymous_solutions: Result<Vec<HashMap<_, _>>, ZkSparqlError> = solutions
        .map(|solution| {
            solution?
                .iter()
                .map(|(var, term)| {
                    if disclosed_variables.contains(var) {
                        Ok((var, term))
                    } else {
                        Ok((var, nym_issuer.issue(var, term)?))
                    }
                })
                .collect()
        })
        .collect();
    let deanon_map = nym_issuer.generate_deanon_map();
    Ok(PseudonymousSolutions {
        solutions: pseudonymous_solutions?,
        deanon_map,
    })
}

fn assign_solution_to_pattern<'a>(
    solution: &HashMap<&'a Variable, &'a Term>,
    pattern: &TriplePattern,
) -> Result<Triple, HttpError> {
    todo!()
}

// parse a zk-SPARQL query
fn parse_zk_query(query: &str, base_iri: Option<&str>) -> Result<ZkQuery, ZkSparqlError> {
    let parsed_query = spargebra::Query::parse(query, base_iri)
        .map_err(|e| ZkSparqlError::InvalidSparqlQuery(e))?;
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
    let ExtendedQuery { pattern, variables } = build_extended_common(query)?;

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

fn build_extended_prove_query(query: &ZkQuery) -> Result<spargebra::Query, ZkSparqlError> {
    let new_query = replace_blanknodes_with_variables(query);
    println!("new_query.patterns: {:#?}", new_query.patterns);

    let ExtendedQuery { pattern, .. } = build_extended_common(&new_query)?;

    Ok(spargebra::Query::Select {
        dataset: None,
        pattern: GraphPattern::Distinct {
            inner: Box::new(GraphPattern::Project {
                inner: Box::new(pattern),
                variables: new_query.in_scope_variables.into_iter().collect(),
            }),
        },
        base_iri: None,
    })
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

fn build_extended_common(query: &ZkQuery) -> Result<ExtendedQuery, ZkSparqlError> {
    // TODO: replace the vc variable prefix (`__vc`) with randomized one?
    let extended_graph_variables: Vec<_> = (0..query.patterns.len())
        .map(|i| Variable::new_unchecked(format!("{}{}", VC_VARIABLE_PREFIX, i)))
        .collect();

    // wrap each triple pattern with a GRAPH clause
    let extended_bgp = query
        .patterns
        .iter()
        .enumerate()
        .map(|(i, triple_pattern)| {
            let v = extended_graph_variables
                .get(i)
                .ok_or(ZkSparqlError::ExtendedQueryFailed)?;
            Ok(GraphPattern::Graph {
                name: NamedNodePattern::Variable(v.clone()),
                inner: Box::new(GraphPattern::Bgp {
                    patterns: vec![triple_pattern.clone()],
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
