//! AL evaluation errors.

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvalError {
    UnknownFunc(String),
    UnknownVar(&'static str),
    AssertFailed,
    Fail,
    Unimplemented(&'static str),
    TypeMismatch(&'static str),
}

impl std::fmt::Display for EvalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownFunc(n) => write!(f, "unknown AL function: {n}"),
            Self::UnknownVar(n) => write!(f, "unknown AL variable: {n}"),
            Self::AssertFailed => write!(f, "AL assert failed"),
            Self::Fail => write!(f, "AL fail"),
            Self::Unimplemented(s) => write!(f, "AL eval unimplemented: {s}"),
            Self::TypeMismatch(s) => write!(f, "AL type mismatch: {s}"),
        }
    }
}

impl std::error::Error for EvalError {}
