use super::{
    error::ZkSparqlError, PSEUDONYMOUS_IRI_PREFIX, PSEUDONYMOUS_VAR_PREFIX, PSEUDONYM_ALPHABETS,
    SKOLEM_IRI_PREFIX, SUBJECT_GRAPH_SUFFIX, VC_VARIABLE_PREFIX,
};

use nanoid::nanoid;
use oxigraph::sparql::QuerySolutionIter;
use oxrdf::{Literal, NamedNode, Quad, Subject, Term, Variable};
use std::collections::{HashMap, HashSet};

pub struct PseudonymousSolutions {
    pub solutions: Vec<HashMap<Variable, Term>>,
    pub deanon_map: HashMap<NamedNode, Term>,
}

#[derive(Default)]
pub struct Pseudonymizer {
    iri_to_nym: HashMap<NamedNode, NamedNode>,
    nym_to_literal: HashMap<NamedNode, Term>,
}

impl Pseudonymizer {
    fn generate_pseudonymous_iri() -> NamedNode {
        let val = nanoid!(21, &PSEUDONYM_ALPHABETS);
        NamedNode::new_unchecked(format!("{}{}", PSEUDONYMOUS_IRI_PREFIX, val))
    }

    fn generate_pseudonymous_var() -> NamedNode {
        let val = nanoid!(21, &PSEUDONYM_ALPHABETS);
        NamedNode::new_unchecked(format!("{}{}", PSEUDONYMOUS_VAR_PREFIX, val))
    }

    fn issue_iri_nym(&mut self, iri: &NamedNode) -> NamedNode {
        let nym = Self::generate_pseudonymous_iri();
        self.iri_to_nym.entry(iri.clone()).or_insert(nym).clone()
    }

    fn get_iri_nym(&self, iri: &NamedNode) -> Option<NamedNode> {
        self.iri_to_nym.get(iri).cloned()
    }

    fn issue_literal_nym(&mut self, literal: &Literal) -> NamedNode {
        let nym = Self::generate_pseudonymous_var();
        self.nym_to_literal
            .insert(nym.clone(), Term::Literal(literal.clone()));
        nym
    }

    fn get_deanon_map(&self) -> HashMap<NamedNode, Term> {
        let mut nym_to_iri: HashMap<NamedNode, Term> = self
            .iri_to_nym
            .iter()
            .map(|(iri, nym)| (nym.clone(), Term::NamedNode(iri.clone())))
            .collect();
        nym_to_iri.extend(self.nym_to_literal.clone());
        nym_to_iri
    }

    pub fn pseudonymize_solutions(
        &mut self,
        solutions: QuerySolutionIter,
        disclosed_variables: &[Variable],
    ) -> Result<PseudonymousSolutions, ZkSparqlError> {
        let disclosed_variables: HashSet<_> = disclosed_variables.iter().collect();

        let pseudonymous_solutions: Result<Vec<HashMap<_, _>>, ZkSparqlError> = solutions
            .map(|solution| {
                solution?
                    .iter()
                    .map(|(var, term)| {
                        let pseudonymized_term = if disclosed_variables.contains(var) {
                            term.clone()
                        } else if var.as_str().starts_with(VC_VARIABLE_PREFIX) {
                            match term {
                                Term::NamedNode(n)
                                    if n.as_str().ends_with(SUBJECT_GRAPH_SUFFIX) =>
                                {
                                    Term::NamedNode(NamedNode::new(
                                        &n.as_str()
                                            [0..(n.as_str().len() - SUBJECT_GRAPH_SUFFIX.len())],
                                    )?)
                                }
                                _ => return Err(ZkSparqlError::FailedBuildingPseudonymousSolution),
                            }
                        } else {
                            match term {
                                Term::NamedNode(n) if n.as_str().starts_with(SKOLEM_IRI_PREFIX) => {
                                    term.clone()
                                }
                                Term::NamedNode(n) => Term::NamedNode(self.issue_iri_nym(n)),
                                Term::Literal(l) => Term::NamedNode(self.issue_literal_nym(l)),
                                _ => return Err(ZkSparqlError::FailedBuildingPseudonymousSolution),
                            }
                        };
                        Ok((var.clone(), pseudonymized_term))
                    })
                    .collect()
            })
            .collect();

        Ok(PseudonymousSolutions {
            solutions: pseudonymous_solutions?,
            deanon_map: self.get_deanon_map(),
        })
    }
}
