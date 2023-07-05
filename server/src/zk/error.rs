use crate::{bad_request, HttpError};

use oxigraph::{sparql::EvaluationError, store::StorageError};
use oxiri::IriParseError;
use spargebra::ParseError;

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
