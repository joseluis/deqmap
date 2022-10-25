// deqmap::error
//
//! Error types.
//

use core::result;

/// Common result type.
pub type Result<N> = result::Result<N, Error>;

/// Common error type.
#[non_exhaustive]
#[derive(Debug)]
pub enum Error {
    /// Index is out of bound.
    IndexOutOfBounds,

    /// A generic error message.
    String(String),
}

impl Error {
    /// New miscelaneous error.
    pub fn new(err: impl ToString) -> Self {
        Self::String(err.to_string())
    }
}

/// impl Display & Error
mod std_impls {
    use super::Error;
    use std::fmt::Debug;
    use std::{error::Error as StdError, fmt};

    impl StdError for Error {}

    impl fmt::Display for Error {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Error::IndexOutOfBounds => write!(f, "Index is out of bounds."),
                Error::String(e) => Debug::fmt(e, f),

                #[allow(unreachable_patterns)]
                _ => write!(f, "Error"),
            }
        }
    }
    impl From<&str> for Error {
        fn from(err: &str) -> Self {
            Error::new(err)
        }
    }

    impl From<String> for Error {
        fn from(err: String) -> Self {
            Error::String(err)
        }
    }
}
