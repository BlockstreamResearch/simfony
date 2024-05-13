use std::fmt;
use std::sync::Arc;

use simplicity::elements;

use crate::parse::{Identifier, Position, Span, Type, UIntType};
use crate::Rule;

/// Helper trait to convert `Result<T, E>` into `Result<T, RichError>`.
pub trait WithSpan<T> {
    /// Update the result with the affected span.
    fn with_span<S: Into<Span>>(self, span: S) -> Result<T, RichError>;
}

impl<T, E: Into<Error>> WithSpan<T> for Result<T, E> {
    fn with_span<S: Into<Span>>(self, span: S) -> Result<T, RichError> {
        self.map_err(|e| e.into().with_span(span.into()))
    }
}

/// Helper trait to update `Result<A, RichError>` with the the affected source file.
pub trait WithFile<T> {
    /// Update the result with the affected source file.
    ///
    /// Enable pretty errors.
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

    /// Add the source file where the error occurred.
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
        let start_line_index = self.span.start.line.get() - 1;
        let end_line_index = self.span.end.line.get() - 1;
        let line_num_width = self.span.end.line.get().to_string().len();
        writeln!(f, "{:width$} |", " ", width = line_num_width)?;

        if let Some(ref file) = self.file {
            let mut lines = file.lines().skip(start_line_index).peekable();
            let start_line_len = lines.peek().map(|l| l.len()).unwrap_or(0);
            for (relative_line_index, line_str) in lines
                .take(end_line_index - start_line_index + 1)
                .enumerate()
            {
                let line_num = start_line_index + relative_line_index + 1;
                writeln!(f, "{line_num:line_num_width$} | {line_str}")?;
            }
            let (underline_start, underline_length) = if self.span.is_multiline() {
                (0, start_line_len)
            } else {
                (
                    self.span.start.col.get(),
                    self.span.end.col.get() - self.span.start.col.get(),
                )
            };
            write!(f, "{:width$} |", " ", width = line_num_width)?;
            write!(f, "{:width$}", " ", width = underline_start)?;
            write!(f, "{:^<width$} ", "", width = underline_length)?;
            write!(f, "{}", self.error)
        } else {
            let start_line_num = self.span.end.line.get();
            write!(f, "{start_line_num} | {}", self.error)
        }
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
        let (start, end) = match error.line_col {
            pest::error::LineColLocation::Pos((line, col)) => {
                (Position::new(line, col), Position::new(line, col + 1))
            }
            pest::error::LineColLocation::Span((line, col), (line_end, col_end)) => {
                (Position::new(line, col), Position::new(line_end, col_end))
            }
        };
        let span = Span::new(start, end);
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
    UnmatchedPattern(String),
    // TODO: Remove CompileError once Simfony has a type system
    // The Simfony compiler should never produce ill-typed Simplicity code
    // The compiler can only be this precise if it knows a type system at least as expressive as Simplicity's
    CannotCompile(String),
    JetDoesNotExist(Arc<str>),
    TypeValueMismatch(Type),
    InvalidDecimal(UIntType),
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
            Error::UnmatchedPattern(pattern) => write!(
                f,
                "Pattern `{pattern}` not covered in match"
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
            Error::UndefinedVariable(identifier) => write!(
                f,
                "Variable `{identifier}` is not defined"
            ),
        }
    }
}

impl std::error::Error for Error {}

impl Error {
    /// Update the error with the affected span.
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
let x: u32 = Left(
    Right(0)
);
"#;

    #[test]
    fn display_single_line() {
        let error = Error::ListBoundPow2
            .with_span(Span::new(Position::new(1, 14), Position::new(1, 20)))
            .with_file(Arc::from(FILE));
        let expected = r#"
  |
1 | let a1: List<u32, 2> = None;
  |              ^^^^^^ List bound must be a power of two greater one: 2, 4, 8, 16, 32, ..."#;
        assert_eq!(&expected[1..], &error.to_string());
    }

    #[test]
    fn display_multi_line() {
        let error = Error::CannotParse(
            "Expected value of type `u32`, got `Either<Either<_, u32>, _>`".to_string(),
        )
        .with_span(Span::new(Position::new(2, 21), Position::new(4, 2)))
        .with_file(Arc::from(FILE));
        let expected = r#"
  |
2 | let x: u32 = Left(
3 |     Right(0)
4 | );
  | ^^^^^^^^^^^^^^^^^^ Cannot parse: Expected value of type `u32`, got `Either<Either<_, u32>, _>`"#;
        assert_eq!(&expected[1..], &error.to_string());
    }
}
