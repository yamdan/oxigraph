use super::{
    error::ZkSparqlError, PSEUDONYMOUS_IRI_PREFIX, PSEUDONYMOUS_VAR_PREFIX, PSEUDONYM_ALPHABETS,
    SKOLEM_IRI_PREFIX, SUBJECT_GRAPH_SUFFIX, VC_VARIABLE_PREFIX,
};

use nanoid::nanoid;
use oxigraph::sparql::QuerySolutionIter;
use oxrdf::{Literal, NamedNode, Term, Variable};
use std::collections::{HashMap, HashSet};

pub struct PseudonymousSolutions {
    pub solutions: Vec<HashMap<Variable, Term>>,
    pub deanon_map: HashMap<Term, Term>,
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

pub fn pseudonymize_solutions(
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
