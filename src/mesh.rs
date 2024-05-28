//! Provides utilities handling mesh.
//!
//! We note that [`MeshCoord`] supports non-negative latitude and longitude only.
//! Therefore, [`MeshNode`] and [`MeshCell`] have the same restriction of [`MeshCoord`].
//!
//! The third digit of [`MeshCoord`] depends on mesh.
//! If the mesh unit is [`MeshUnit::Five`], it takes 0 or 5 only.
//! Hence, the methods/operations that relate with [`MeshCoord`] returns [`Err`],
//! if [`MeshUnit::Five`] is given even though the third digit is neither 0 nor 5,
//! in general.
use std::error::Error;
use std::fmt::{Display, Formatter};

pub use cell::MeshCell;
pub(crate) use code::MeshCode;
pub use coord::MeshCoord;
pub use node::MeshNode;
pub use unit::MeshUnit;

mod cell;
mod code;
mod coord;
mod node;
mod unit;

/// Returns `ture` when `meshcode` is valid.
///
/// # Example
///
/// ```
/// # use jgdtrans::mesh::*;
/// #
/// assert_eq!(is_meshcode(&54401027), true);
/// assert_eq!(is_meshcode(&10900000), false);
/// assert_eq!(is_meshcode(&100000000), false);
/// ```
#[inline]
pub const fn is_meshcode(meshcode: &u32) -> bool {
    MeshNode::try_from_meshcode(meshcode).is_some()
}

//
// Error
//

/// An error on the [`TryFrom`] trait of [`mesh`](mod@self) module.
#[derive(Debug)]
pub struct MeshTryFromError;

impl MeshTryFromError {
    #[cold]
    const fn new() -> Self {
        Self {}
    }
}

impl Error for MeshTryFromError {}

impl Display for MeshTryFromError {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "the value would be out-of-bounds of the output",)
    }
}
