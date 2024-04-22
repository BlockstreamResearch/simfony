use std::fmt;
use std::sync::Arc;

use simplicity::elements;

use crate::parse::{Identifier, Span, Type, UIntType};
use crate::Rule;

/// Helper trait to update a result with the affected span.
pub trait WithSpan<T> {
    /// Update the result with a span of the affected area in the source file.
    fn with_span<S: Into<Span>>(self, span: S) -> Result<T, RichError>;
}

impl<T, E: Into<Error>> WithSpan<T> for Result<T, E> {
    fn with_span<S: Into<Span>>(self, span: S) -> Result<T, RichError> {
        self.map_err(|e| e.into().with_span(span.into()))
    }
}

/// Helper trait to update a result with the affected source file.
pub trait WithFile<T> {
    /// Update the result with the source file.
    ///
    /// Required for pretty errors.
    fn with_file<F: Into<Arc<str>>>(self, file: F) -> Result<T, RichError>;
}

impl<T> WithFile<T> for Result<T, RichError> {
    fn with_file<F: Into<Arc<str>>>(self, file: F) -> Result<T, RichError> {
        self.map_err(|e| e.with_file(file.into()))
    }
}

/// An error enriched with context.
///
/// Records _what_ happened and _where_.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct RichError {
    /// The error that occurred.
    error: Error,
    /// Area that the error spans inside the file.
    span: Span,
    /// File in which the error occurred.
    ///
    /// Required to print pretty errors.
    file: Option<Arc<str>>,
}

impl RichError {
    /// Create a new error with context.
    pub fn new(error: Error, span: Span) -> RichError {
        RichError {
            error,
            span,
            file: None,
        }
    }

    /// Add the file where the error occurred.
    ///
    /// Enable pretty errors.
    pub fn with_file(self, file: Arc<str>) -> Self {
        Self {
            error: self.error,
            span: self.span,
            file: Some(file),
        }
    }
}

impl fmt::Display for RichError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let line = self.span.line.to_string();
        writeln!(f, "{:width$} |", " ", width = line.len())?;

        // FIXME: Handle objects that wrap lines
        if let Some(ref file) = self.file {
            if let Some(line_str) = file.lines().nth(self.span.line.get() - 1) {
                writeln!(f, "{line} | {line_str}")?;
                write!(f, "{:width$} |", " ", width = line.len())?;
                write!(f, "{:width$}", " ", width = self.span.col.get())?;
                write!(f, "{:^<width$} ", "", width = self.span.len.get())?;
                return write!(f, "{}", self.error);
            }
        }

        writeln!(f, "{line} | {}", self.error)?;
        write!(f, "{:width$} |", " ", width = line.len())
    }
}

impl std::error::Error for RichError {}

impl From<RichError> for String {
    fn from(error: RichError) -> Self {
        error.to_string()
    }
}

impl From<pest::error::Error<Rule>> for RichError {
    fn from(error: pest::error::Error<Rule>) -> Self {
        let description = error.variant.message().to_string();
        let span = match error.line_col {
            pest::error::LineColLocation::Pos((line, col)) => Span::new(line, col),
            pest::error::LineColLocation::Span((line, col), (_, col_end)) => {
                Span::new(line, col).with_len(std::cmp::max(1, col_end.saturating_sub(col)))
            }
        };

        Self::new(Error::Grammar(description), span)
    }
}

/// An individual error.
///
/// Records _what_ happened but not where.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Error {
    ArraySizeZero,
    ListBoundPow2,
    BitStringPow2,
    HexStringPow2,
    CannotParse(String),
    Grammar(String),
    // TODO: Remove this error once Simfony has a type system
    CannotCompile(String),
    JetDoesNotExist(Arc<str>),
    TypeValueMismatch(Type),
    InvalidDecimal(UIntType),
    UnmatchedPattern(&'static str),
    UndefinedVariable(Identifier),
}

#[rustfmt::skip]
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::ArraySizeZero => write!(
                f,
                "Array size must be positive: 1, 2, 3, 4, 5, ..."
            ),
            Error::ListBoundPow2 => write!(
                f,
                "List bound must be a power of two greater one: 2, 4, 8, 16, 32, ..."
            ),
            Error::BitStringPow2 => write!(
                f,
                "Length of bit string must be a power of two: 1, 2, 4, 8, 16, ..."
            ),
            Error::HexStringPow2 => write!(
                f,
                "Length of hex string must be a power of two: 1, 2, 4, 8, 16, ..."
            ),
            Error::CannotParse(description) => write!(
                f,
                "Cannot parse: {description}"
            ),
            Error::Grammar(description) => write!(
                f,
                "Grammar error: {description}"
            ),
            Error::CannotCompile(description) => write!(
                f,
                "Failed to compile to Simplicity: {description}"
            ),
            Error::JetDoesNotExist(name) => write!(
                f,
                "Jet `{name}` does not exist"
            ),
            Error::TypeValueMismatch(ty) => write!(
                f,
                "Value does not match the assigned type `{ty}`"
            ),
            Error::InvalidDecimal(ty) => write!(
                f,
                "Use bit strings or hex strings for values of type `{ty}`"
            ),
            Error::UnmatchedPattern(pattern) => write!(
                f,
                "Pattern `{pattern}` not covered in match"
            ),
            Error::UndefinedVariable(identifier) => write!(
                f,
                "Variable `{identifier}` is not defined"
            ),
        }
    }
}

impl std::error::Error for Error {}

impl Error {
    /// Enrich the error with a span.
    pub fn with_span<S: Into<Span>>(self, span: S) -> RichError {
        RichError::new(self, span.into())
    }
}

impl From<elements::hex::Error> for Error {
    fn from(error: elements::hex::Error) -> Self {
        Self::CannotParse(error.to_string())
    }
}

impl From<std::num::ParseIntError> for Error {
    fn from(error: std::num::ParseIntError) -> Self {
        Self::CannotParse(error.to_string())
    }
}

impl From<simplicity::types::Error> for Error {
    fn from(error: simplicity::types::Error) -> Self {
        Self::CannotCompile(error.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const FILE: &str = r#"let a1: List<u32, 2> = None;
let b1: List<u32, 2> = Some(1);
let c1: List<u32, 4> = (None, None);
let a : u32 = 2;
let b : (u16, (u8, (u4, (u2, (u1, Either<(), ()>))))) = 3;
let (carry, res) = jet_add_32(a, b);
let add_res = jet_add_32(10, 20);
let (carry2, res3) = add_res;
jet_verify(jet_eq_32(res3, 30));"#;

    #[test]
    fn display() {
        let error = Error::ListBoundPow2
            .with_span(Span::new(1, 14).with_len(6))
            .with_file(Arc::from(FILE));
        let expected = r#"
  |
1 | let a1: List<u32, 2> = None;
  |              ^^^^^^ List bound must be a power of two: 1, 2, 4, 8, 16, ..."#;
        assert_eq!(&expected[1..], &error.to_string());
    }
}
