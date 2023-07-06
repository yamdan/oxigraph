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
    iri_mapping: HashMap<NamedNode, NamedNode>,
    literal_mapping: HashMap<Literal, NamedNode>,
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

    fn issue_iri(&mut self, iri: &NamedNode) -> NamedNode {
        if iri.as_str().starts_with(SKOLEM_IRI_PREFIX) {
            iri.clone()
        } else {
            self.iri_mapping
                .entry(iri.clone())
                .or_insert(Self::generate_pseudonymous_iri())
                .clone()
        }
    }

    fn issue_literal(&mut self, literal: &Literal) -> NamedNode {
        let nym = Self::generate_pseudonymous_var();
        self.literal_mapping.insert(literal.clone(), nym.clone());
        nym
    }

    fn get_inverse(&self) -> HashMap<NamedNode, Term> {
        let mut iri_mapping_inverse: HashMap<NamedNode, Term> = self
            .iri_mapping
            .iter()
            .map(|(iri, nym)| (nym.clone(), Term::NamedNode(iri.clone())))
            .collect();
        let literal_mapping_inverse: HashMap<NamedNode, Term> = self
            .literal_mapping
            .iter()
            .map(|(literal, nym)| (nym.clone(), Term::Literal(literal.clone())))
            .collect();
        iri_mapping_inverse.extend(literal_mapping_inverse);
        iri_mapping_inverse
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
                                Term::NamedNode(n) => Term::NamedNode(self.issue_iri(n)),
                                Term::Literal(l) => Term::NamedNode(self.issue_literal(l)),
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
            deanon_map: self.get_inverse(),
        })
    }
}
