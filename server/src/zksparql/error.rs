use super::crypto::DeriveProofError;
use crate::{bad_request, HttpError};

use oxigraph::{sparql::EvaluationError, store::StorageError};
use oxiri::IriParseError;
use oxrdf::{BlankNode, NamedNode, VariableNameParseError};
use rdf_canon::CanonicalizationError;
use spargebra::ParseError;

pub enum ZkSparqlError {
    ConstructNotSupported,
    DescribeNotSupported,
    InvalidSparqlQuery(ParseError),
    InvalidZkSparqlQuery,
    SparqlEvaluationError(EvaluationError),
    ExtendedQueryFailed,
    IriParseError(IriParseError),
    FailedPseudonymizingQuad,
    MissingGraphVar,
    FailedBuildingDisclosedSubject,
    StorageError(StorageError),
    FailedBuildingCredentialMetadata,
    BlankNodeMustBeSkolemized(BlankNode),
    InvalidProofValues,
    FailedGettingVerifiableCredential,
    InvalidSkolemIRI(NamedNode),
    CanonicalizationError(CanonicalizationError),
    VariableNameParseError(VariableNameParseError),
    DeriveProofError(DeriveProofError),
    InvalidVCWithMultipleProofs,
    InvalidVCWithoutProofs,
    InvalidVCWithInvalidProofGraphName,
    InternalError(String),
}

impl From<EvaluationError> for ZkSparqlError {
    fn from(e: EvaluationError) -> Self {
        Self::SparqlEvaluationError(e)
    }
}

impl From<IriParseError> for ZkSparqlError {
    fn from(e: IriParseError) -> Self {
        Self::IriParseError(e)
    }
}

impl From<StorageError> for ZkSparqlError {
    fn from(e: StorageError) -> Self {
        Self::StorageError(e)
    }
}

impl From<VariableNameParseError> for ZkSparqlError {
    fn from(e: VariableNameParseError) -> Self {
        Self::VariableNameParseError(e)
    }
}

impl From<DeriveProofError> for ZkSparqlError {
    fn from(e: DeriveProofError) -> Self {
        Self::DeriveProofError(e)
    }
}

impl From<ZkSparqlError> for HttpError {
    fn from(val: ZkSparqlError) -> Self {
        match val {
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
            ZkSparqlError::IriParseError(e) => bad_request(format!("IRI parse error: {}", e)),
            ZkSparqlError::FailedPseudonymizingQuad => bad_request("pseudonymizing quad failed"),
            ZkSparqlError::MissingGraphVar => {
                bad_request("graph variables must be given by VALUES at the prove endpoint")
            }
            ZkSparqlError::FailedBuildingDisclosedSubject => {
                bad_request("building disclosed subject failed")
            }
            ZkSparqlError::StorageError(e) => {
                bad_request(format!("building disclosed dataset failed: {}", e))
            }
            ZkSparqlError::FailedBuildingCredentialMetadata => {
                bad_request("building credential metadata failed")
            }
            ZkSparqlError::BlankNodeMustBeSkolemized(blank_node) => bad_request(format!(
                "input blank node must be skolemized: {}",
                blank_node
            )),
            ZkSparqlError::InvalidProofValues => {
                bad_request("one proof must contain only one proof value")
            }
            ZkSparqlError::FailedGettingVerifiableCredential => {
                bad_request("failed to get a verifable credential")
            }
            ZkSparqlError::InvalidSkolemIRI(n) => {
                bad_request(format!("invalid skolem IRI: {}", n.as_str()))
            }
            ZkSparqlError::CanonicalizationError(e) => {
                bad_request(format!("canonicalization error: {}", e))
            }
            ZkSparqlError::VariableNameParseError(e) => {
                bad_request(format!("variable name parse error: {}", e))
            }
            ZkSparqlError::DeriveProofError(e) => {
                bad_request(format!("derive proof failed: {:?}", e))
            }
            ZkSparqlError::InvalidVCWithMultipleProofs => {
                bad_request("invalid VC with multiple proofs")
            }
            ZkSparqlError::InvalidVCWithoutProofs => bad_request("invalid VC without proofs"),
            ZkSparqlError::InvalidVCWithInvalidProofGraphName => {
                bad_request("invalid VC with invalid proof graph name")
            }
            ZkSparqlError::InternalError(msg) => bad_request(format!("internal error: {}", msg)),
        }
    }
}
