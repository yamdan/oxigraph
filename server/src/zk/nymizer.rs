use super::{
    error::ZkSparqlError, PSEUDONYMOUS_IRI_PREFIX, PSEUDONYMOUS_VAR_PREFIX, PSEUDONYM_ALPHABETS,
    SKOLEM_IRI_PREFIX,
};

use nanoid::nanoid;
use oxrdf::{Literal, NamedNode, Term, Variable};
use std::collections::HashMap;

pub struct PseudonymousSolutions {
    pub solutions: Vec<HashMap<Variable, Term>>,
    pub deanon_map: HashMap<Term, Term>,
}

#[derive(Default)]
pub struct Pseudonymizer {
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

    pub fn issue(&mut self, var: &Variable, term: &Term) -> Result<Term, ZkSparqlError> {
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

    pub fn get_inverse(&self) -> HashMap<Term, Term> {
        self.mapping
            .iter()
            .map(|((_, t), nym)| (nym.clone(), t.clone()))
            .collect()
    }
}
