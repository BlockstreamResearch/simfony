use crate::error::{Diagnostic, Error};

/// Why the analysis of a node failed.
#[derive(Debug)]
pub(super) enum Failure {
    /// A new error that was not reported yet.
    New(Diagnostic),
    /// The error was already reported to the scope.
    Reported,
}

impl From<Diagnostic> for Failure {
    fn from(diagnostic: Diagnostic) -> Self {
        Self::New(diagnostic)
    }
}

/// Check whether an error mentions a type that contains `!`.
pub(super) fn mentions_never(error: &Error) -> bool {
    match error {
        Error::ExpressionUnexpectedType { ty } | Error::RawHashUnsupportedType { ty } => {
            ty.contains_never()
        }
        Error::ExpressionTypeMismatch { expected, found } => {
            expected.contains_never() || found.contains_never()
        }
        Error::InvalidCast { source, target } => source.contains_never() || target.contains_never(),
        _ => false,
    }
}
