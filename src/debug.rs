use crate::types::ResolvedType;

/// Name of a call expression with a debug symbol.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TrackedCallName {
    Assert,
    Panic,
    Jet,
    UnwrapLeft(ResolvedType),
    UnwrapRight(ResolvedType),
    Unwrap,
}
