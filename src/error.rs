use std::fmt;
use std::sync::Arc;

use simplicity::elements;

use crate::parse::{Identifier, JetName, MatchPattern, Position, Rule, Span, WitnessName};
use crate::types::{ResolvedType, UIntType};

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

/// Helper trait to update `Result<A, RichError>` with the affected source file.
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
        match self.file {
            Some(ref file) if !file.is_empty() => {
                let start_line_index = self.span.start.line.get() - 1;
                let n_spanned_lines = self.span.end.line.get() - start_line_index;
                let line_num_width = self.span.end.line.get().to_string().len();
                writeln!(f, "{:width$} |", " ", width = line_num_width)?;

                let mut lines = file.lines().skip(start_line_index).peekable();
                let start_line_len = lines.peek().map(|l| l.len()).unwrap_or(0);

                for (relative_line_index, line_str) in lines.take(n_spanned_lines).enumerate() {
                    let line_num = start_line_index + relative_line_index + 1;
                    writeln!(f, "{line_num:line_num_width$} | {line_str}")?;
                }

                let (underline_start, underline_length) = match self.span.is_multiline() {
                    true => (0, start_line_len),
                    false => (
                        self.span.start.col.get(),
                        self.span.end.col.get() - self.span.start.col.get(),
                    ),
                };
                write!(f, "{:width$} |", " ", width = line_num_width)?;
                write!(f, "{:width$}", " ", width = underline_start)?;
                write!(f, "{:^<width$} ", "", width = underline_length)?;
                write!(f, "{}", self.error)
            }
            _ => {
                write!(f, "{}", self.error)
            }
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
    ListBoundPow2(usize),
    BitStringPow2(usize),
    HexStringPow2(usize),
    CannotParse(String),
    Grammar(String),
    IncompatibleMatchArms(MatchPattern, MatchPattern),
    // TODO: Remove CompileError once Simfony has a type system
    // The Simfony compiler should never produce ill-typed Simplicity code
    // The compiler can only be this precise if it knows a type system at least as expressive as Simplicity's
    CannotCompile(String),
    JetDoesNotExist(JetName),
    TypeValueMismatch(ResolvedType),
    InvalidNumberOfArguments(usize, usize),
    ExpressionTypeMismatch(ResolvedType, ResolvedType),
    IntegerOutOfBounds(UIntType),
    UndefinedVariable(Identifier),
    UndefinedAlias(Identifier),
    VariableReuseInPattern(Identifier),
    ReusedWitness(WitnessName),
}

#[rustfmt::skip]
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::ListBoundPow2(bound) => write!(
                f,
                "Expected a power of two greater than one (2, 4, 8, 16, 32, ...) as list bound, found {bound}"
            ),
            Error::BitStringPow2(len) => write!(
                f,
                "Expected a valid bit string length (1, 2, 4, 8, 16, 32, 64, 128, 256), found {len}"
            ),
            Error::HexStringPow2(len) => write!(
                f,
                "Expected a valid hex string length (2, 4, 8, 16, 32, 64), found {len}"
            ),
            Error::CannotParse(description) => write!(
                f,
                "Cannot parse: {description}"
            ),
            Error::Grammar(description) => write!(
                f,
                "Grammar error: {description}"
            ),
            Error::IncompatibleMatchArms(pattern1, pattern2) => write!(
                f,
                "Match arm `{pattern1}` is incompatible with arm `{pattern2}`"
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
            Error::InvalidNumberOfArguments(expected, found) => write!(
                f,
                "Expected {expected} arguments, found {found} arguments"
            ),
            Error::ExpressionTypeMismatch(expected, found) => write!(
                f,
                "Expected expression of type `{expected}`, found type `{found}`"
            ),
            Error::IntegerOutOfBounds(ty) => write!(
                f,
                "Value is out of bounds for type `{ty}`"
            ),
            Error::UndefinedVariable(identifier) => write!(
                f,
                "Variable `{identifier}` is not defined"
            ),
            Error::UndefinedAlias(identifier) => write!(
                f,
                "Type alias `{identifier}` is not defined"
            ),
            Error::VariableReuseInPattern(identifier) => write!(
                f,
                "Variable `{identifier}` is used twice in the pattern"
            ),
            Error::ReusedWitness(name) => write!(
                f,
                "Witness `{name}` has been used before somewhere in the program"
            ),
        }
    }
}

impl std::error::Error for Error {}

impl Error {
    /// Update the error with the affected span.
    pub fn with_span(self, span: Span) -> RichError {
        RichError::new(self, span)
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

impl From<crate::num::ParseIntError> for Error {
    fn from(error: crate::num::ParseIntError) -> Self {
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

    const FILE: &str = r#"let a1: List<u32, 5> = None;
let x: u32 = Left(
    Right(0)
);"#;
    const EMPTY_FILE: &str = "";

    #[test]
    fn display_single_line() {
        let error = Error::ListBoundPow2(5)
            .with_span(Span::new(Position::new(1, 14), Position::new(1, 20)))
            .with_file(Arc::from(FILE));
        let expected = r#"
  |
1 | let a1: List<u32, 5> = None;
  |              ^^^^^^ Expected a power of two greater than one (2, 4, 8, 16, 32, ...) as list bound, found 5"#;
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

    #[test]
    fn display_entire_file() {
        let error = Error::CannotParse("This span covers the entire file".to_string())
            .with_span(Span::from(FILE))
            .with_file(Arc::from(FILE));
        let expected = r#"
  |
1 | let a1: List<u32, 5> = None;
2 | let x: u32 = Left(
3 |     Right(0)
4 | );
  | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ Cannot parse: This span covers the entire file"#;
        assert_eq!(&expected[1..], &error.to_string());
    }

    #[test]
    fn display_no_file() {
        let error = Error::CannotParse("This error has no file".to_string())
            .with_span(Span::from(EMPTY_FILE));
        let expected = "Cannot parse: This error has no file";
        assert_eq!(&expected, &error.to_string());

        let error = Error::CannotParse("This error has no file".to_string())
            .with_span(Span::new(Position::new(1, 1), Position::new(2, 2)));
        assert_eq!(&expected, &error.to_string());
    }

    #[test]
    fn display_empty_file() {
        let error = Error::CannotParse("This error has an empty file".to_string())
            .with_span(Span::from(EMPTY_FILE))
            .with_file(Arc::from(EMPTY_FILE));
        let expected = "Cannot parse: This error has an empty file";
        assert_eq!(&expected, &error.to_string());

        let error = Error::CannotParse("This error has an empty file".to_string())
            .with_span(Span::new(Position::new(1, 1), Position::new(2, 2)))
            .with_file(Arc::from(EMPTY_FILE));
        assert_eq!(&expected, &error.to_string());
    }
}
