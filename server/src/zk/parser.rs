use super::error::ZkSparqlError;

use oxiri::Iri;
use oxrdf::Variable;
use spargebra::{
    algebra::{Expression, GraphPattern, QueryDataset},
    term::{GroundTerm, TriplePattern},
};
use std::collections::HashSet;

#[derive(Debug, Default)]
pub struct ZkQuery {
    pub disclosed_variables: Vec<Variable>,
    pub in_scope_variables: HashSet<Variable>,
    pub patterns: Vec<TriplePattern>,
    pub filter: Option<Expression>,
    pub values: Option<ZkQueryValues>,
    pub limit: Option<ZkQueryLimit>,
}

#[derive(Debug, Default, Clone)]
pub struct ZkQueryValues {
    pub variables: Vec<Variable>,
    pub bindings: Vec<Vec<Option<GroundTerm>>>,
}

#[derive(Debug, Default, Clone)]
pub struct ZkQueryLimit {
    pub start: usize,
    pub length: Option<usize>,
}

struct ZkBgpAndValues {
    bgp: Vec<TriplePattern>,
    values: Option<ZkQueryValues>,
}

pub fn parse_zk_query(query: &str, base_iri: Option<&str>) -> Result<ZkQuery, ZkSparqlError> {
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
