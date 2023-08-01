use super::{error::ZkSparqlError, NYM_IRI_PREFIX, SUBJECT_GRAPH_SUFFIX, VC_VARIABLE_PREFIX};

use oxigraph::sparql::QuerySolutionIter;
use oxrdf::{
    BlankNode, GraphName, Literal, NamedNode, NamedOrBlankNode, Quad, Subject, Term, Variable,
};
use std::collections::{HashMap, HashSet};

#[derive(Default)]
pub struct Pseudonymizer {
    iri_to_nym: HashMap<NamedNode, NamedOrBlankNode>,
    nym_to_literal: HashMap<NamedOrBlankNode, Term>,
}

impl Pseudonymizer {
    fn get_iri_nym(&self, iri: &NamedNode) -> Option<NamedOrBlankNode> {
        self.iri_to_nym.get(iri).cloned()
    }

    // issue blank node nym to pseudonymize an IRI as subject, object, or graph name
    fn issue_nym_for_iri(&mut self, iri: &NamedNode) -> NamedOrBlankNode {
        self.iri_to_nym
            .entry(iri.clone())
            .or_insert(BlankNode::default().into())
            .clone()
    }

    // issue IRI nym to pseudonymize an IRI as predicate
    fn issue_named_nym_for_iri(&mut self, iri: &NamedNode) -> NamedOrBlankNode {
        self.iri_to_nym
            .entry(iri.clone())
            .or_insert(
                NamedNode::new_unchecked(format!(
                    "{}{}",
                    NYM_IRI_PREFIX,
                    BlankNode::default().as_str()
                ))
                .into(),
            )
            .clone()
    }

    // issue blank node nym to pseudonymize a literal as object
    fn issue_nym_for_literal(&mut self, literal: &Literal) -> NamedOrBlankNode {
        let nym = BlankNode::default();
        self.nym_to_literal.insert(
            NamedOrBlankNode::BlankNode(nym.clone()),
            Term::Literal(literal.clone()),
        );
        NamedOrBlankNode::BlankNode(nym)
    }

    pub fn get_deanon_map(&self) -> HashMap<NamedOrBlankNode, Term> {
        let mut nym_to_iri: HashMap<NamedOrBlankNode, Term> = self
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
        predicate_variables: &HashSet<&Variable>,
    ) -> Result<Vec<HashMap<Variable, Term>>, ZkSparqlError> {
        let disclosed_variables: HashSet<_> = disclosed_variables.iter().collect();

        solutions
            .map(|solution| {
                solution?
                    .iter()
                    .map(|(var, term)| {
                        let pseudonymized_term = if var.as_str().starts_with(VC_VARIABLE_PREFIX) {
                            match term {
                                Term::NamedNode(n)
                                    if n.as_str().ends_with(SUBJECT_GRAPH_SUFFIX) =>
                                {
                                    Ok(Term::NamedNode(NamedNode::new(
                                        &n.as_str()
                                            [0..(n.as_str().len() - SUBJECT_GRAPH_SUFFIX.len())],
                                    )?))
                                }
                                _ => Err(ZkSparqlError::InternalError(
                                    "stored VC graph name must be IRI".to_owned(),
                                )),
                            }
                        } else if disclosed_variables.contains(var) {
                            Ok(term.clone())
                        } else if predicate_variables.contains(var) {
                            match term {
                                Term::NamedNode(n) => Ok(self.issue_named_nym_for_iri(n).into()),
                                _ => Err(ZkSparqlError::InternalError(
                                    "predicate must be IRI".to_owned(),
                                )),
                            }
                        } else {
                            match term {
                                Term::NamedNode(n) => Ok(self.issue_nym_for_iri(n).into()),
                                Term::Literal(l) => Ok(self.issue_nym_for_literal(l).into()),
                                Term::BlankNode(_) => Ok(term.clone()),
                                Term::Triple(_) => Err(ZkSparqlError::InternalError(
                                    "stored VC must not contain a quoted triple".to_owned(),
                                )),
                            }
                        };
                        Ok((var.clone(), pseudonymized_term?))
                    })
                    .collect::<Result<HashMap<_, _>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()
    }

    pub fn pseudonymize_quad(
        &mut self,
        quad: &Quad,
        additional_targets: &HashSet<NamedNode>,
    ) -> Result<Quad, ZkSparqlError> {
        let mut pseudonymize_iri = |iri| {
            if additional_targets.contains(iri) {
                self.issue_nym_for_iri(iri)
            } else {
                match self.get_iri_nym(iri) {
                    Some(nym) => nym,
                    None => NamedOrBlankNode::NamedNode(iri.clone()),
                }
            }
        };

        let s = match &quad.subject {
            Subject::NamedNode(iri) => Ok(match pseudonymize_iri(&iri) {
                NamedOrBlankNode::NamedNode(n) => Subject::NamedNode(n),
                NamedOrBlankNode::BlankNode(b) => Subject::BlankNode(b),
            }),
            Subject::BlankNode(_) => Ok(quad.subject.clone()),
            Subject::Triple(_) => Err(ZkSparqlError::FailedPseudonymizingQuad),
        }?;
        let p = match pseudonymize_iri(&quad.predicate) {
            NamedOrBlankNode::NamedNode(_) => Ok(quad.predicate.clone()), // predicate should not be initially pseudonymized here
            NamedOrBlankNode::BlankNode(_) => Err(ZkSparqlError::FailedPseudonymizingQuad),
        }?;
        let o = match &quad.object {
            Term::NamedNode(iri) => Ok(match pseudonymize_iri(&iri) {
                NamedOrBlankNode::NamedNode(n) => Term::NamedNode(n),
                NamedOrBlankNode::BlankNode(b) => Term::BlankNode(b),
            }),
            Term::BlankNode(_) => Ok(quad.object.clone()),
            Term::Literal(_) => Ok(quad.object.clone()),
            Term::Triple(_) => Err(ZkSparqlError::FailedPseudonymizingQuad),
        }?;
        let g = match &quad.graph_name {
            GraphName::NamedNode(iri) => match pseudonymize_iri(&iri) {
                NamedOrBlankNode::NamedNode(n) => GraphName::NamedNode(n),
                NamedOrBlankNode::BlankNode(b) => GraphName::BlankNode(b),
            },
            GraphName::BlankNode(_) => quad.graph_name.clone(),
            GraphName::DefaultGraph => quad.graph_name.clone(),
        };
        Ok(Quad::new(s, p, o, g))
    }
}
