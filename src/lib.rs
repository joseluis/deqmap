// deqmap::lib
//
//!
//

#![warn(clippy::all)]
#![allow(
    clippy::float_arithmetic,
    clippy::implicit_return,
    clippy::needless_return,
    clippy::blanket_clippy_restriction_lints,
    clippy::pattern_type_mismatch
)]
#![forbid(unsafe_code)]

mod error;
pub use error::{DeqMapError, DeqMapResult};

mod deqmap;
pub use self::deqmap::{DeqMap, DeqMapIter};

#[cfg(test)]
mod tests;
