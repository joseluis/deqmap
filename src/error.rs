// deqmap::error
//
//! Error types.
//

use core::result;
use std::collections::TryReserveError;

/// `DeqMap` result type.
pub type DeqMapResult<N> = result::Result<N, DeqMapError>;

/// `DeqMap` error type.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeqMapError {
    /// Index is out of bound.
    IndexOutOfBounds,

    /// The key already exists.
    KeyAlreadyExists,

    ///
    TryReserve(TryReserveError),

    /// A generic error message.
    String(String),
}

impl DeqMapError {
    /// New miscelaneous error.
    pub fn new(err: impl ToString) -> Self {
        Self::String(err.to_string())
    }
}

/// impl Display & Error
mod std_impls {
    use super::{DeqMapError, TryReserveError};
    use std::fmt::Debug;
    use std::{error::Error as StdError, fmt};

    impl StdError for DeqMapError {}

    impl fmt::Display for DeqMapError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                DeqMapError::IndexOutOfBounds => write!(f, "Index is out of bounds."),
                DeqMapError::KeyAlreadyExists => write!(f, "The key already exists."),
                DeqMapError::String(e) => Debug::fmt(e, f),

                #[allow(unreachable_patterns)]
                _ => write!(f, "Error"),
            }
        }
    }

    impl From<&str> for DeqMapError {
        fn from(err: &str) -> Self {
            DeqMapError::new(err)
        }
    }

    impl From<String> for DeqMapError {
        fn from(err: String) -> Self {
            DeqMapError::String(err)
        }
    }

    impl From<TryReserveError> for DeqMapError {
        fn from(err: TryReserveError) -> Self {
            DeqMapError::TryReserve(err)
        }
    }
}
