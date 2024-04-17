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
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
#[cfg(feature = "serde")]
use serde_repr::{Deserialize_repr, Serialize_repr};

use crate::Point;

/// The mesh unit, or approximate length of cell's edge.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(Serialize_repr, Deserialize_repr))]
#[repr(u8)]
pub enum MeshUnit {
    /// for 1 \[km\]
    One = 1,
    /// for 5 \[km\]
    Five = 5,
}

impl From<&MeshUnit> for u8 {
    #[inline]
    fn from(value: &MeshUnit) -> Self {
        match value {
            MeshUnit::One => 1,
            MeshUnit::Five => 5,
        }
    }
}

/// Represents mesh coordinate, namely, discrete latitude and/or longitude.
///
/// This supports non-negative latitude and longitude only.
///
/// This has three digits, _first_, _second_ and _third_.
/// The first takes values from 0 to 99, the second does from 0 to 7
/// and the third does from 0 to 9 inclusive.
///
/// We note that the third digits takes either 0 or 5 only
/// on the mesh with mesh unit [`MeshUnit::Five`].
///
/// # Example
///
/// ```
/// # use jgdtrans::*;
/// # use jgdtrans::mesh::*;
/// # fn run() -> Option<()> {
/// // The selection of MeshCoord depends on mesh unit
/// let coord = MeshCoord::try_from_latitude(&36.103774791666666, &MeshUnit::One)?;
/// assert_eq!(coord, MeshCoord::try_new(54, 1, 2).unwrap());
/// // Every fifth MeshCoord is taken, when MeshUnit::Five given
/// let coord = MeshCoord::try_from_latitude(&36.103774791666666, &MeshUnit::Five)?;
/// assert_eq!(coord, MeshCoord::try_new(54, 1, 0).unwrap());
///
/// // Increment/decrement (not in-place)
/// let coord = MeshCoord::try_new(54, 1, 2)?;
/// assert_eq!(coord.try_next_up(&MeshUnit::One)?, MeshCoord::try_new(54, 1, 3).unwrap());
/// assert_eq!(coord.try_next_down(&MeshUnit::One)?, MeshCoord::try_new(54, 1, 1).unwrap());
///
/// // Unit must be consistent with MeshCoord,
/// // otherwise it returns None.
/// assert_eq!(coord.try_next_up(&MeshUnit::Five), None);
/// # Some(())}
/// # fn main() -> () {run();()}
/// ```
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct MeshCoord {
    /// takes 0 to 99 inclusive
    pub(crate) first: u8,
    /// takes 0 to 7 inclusive
    pub(crate) second: u8,
    /// takes 0 to 9 inclusive
    pub(crate) third: u8,
}

impl MeshCoord {
    /// Makes a [`MeshCoord`].
    ///
    /// Notes, `first` takes values from 0 to 99,
    /// `second` does from 0 to 7,
    /// and `third` does from 0 to 9 inclusive.
    ///
    /// # Errors
    ///
    /// Returns [`None`] when one of `first`, `second` and `third` is out-of-bounds.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshCoord;
    /// # fn run() -> Option<()> {
    /// let coord = MeshCoord::try_new(1, 2, 3)?;
    /// assert_eq!(coord.first(), &1);
    /// assert_eq!(coord.second(), &2);
    /// assert_eq!(coord.third(), &3);
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn try_new(first: u8, second: u8, third: u8) -> Option<Self> {
        if first.gt(&99) || second.gt(&7) || third.gt(&9) {
            return None;
        };

        Some(Self {
            first,
            second,
            third,
        })
    }

    /// Returns the first digit (`0..100`) of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshCoord;
    /// # fn run() -> Option<()> {
    /// let coord = MeshCoord::try_new(1, 2, 3)?;
    /// assert_eq!(coord.first(), &1);
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn first(&self) -> &u8 {
        &self.first
    }

    /// Returns the second digit (`0..8`) of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshCoord;
    /// # fn run() -> Option<()> {
    /// let coord = MeshCoord::try_new(1, 2, 3)?;
    /// assert_eq!(coord.second(), &2);
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn second(&self) -> &u8 {
        &self.second
    }

    /// Returns the third digit (`0..10`) of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshCoord;
    /// # fn run() -> Option<()> {
    /// let coord = MeshCoord::try_new(1, 2, 3)?;
    /// assert_eq!(coord.third(), &3);
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn third(&self) -> &u8 {
        &self.third
    }

    /// Returns `true` if `self` is compatible to the `mesh_unit`.
    ///
    /// This always returns `true` when `mesh_unit` is [`MeshUnit::One`].
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// let coord = MeshCoord::try_new(1, 2, 3)?;
    /// assert_eq!(coord.is_mesh_unit(&MeshUnit::One), true);
    /// assert_eq!(coord.is_mesh_unit(&MeshUnit::Five), false);
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    #[inline]
    pub fn is_mesh_unit(&self, mesh_unit: &MeshUnit) -> bool {
        match mesh_unit {
            MeshUnit::One => true,
            MeshUnit::Five => (self.third % u8::from(mesh_unit)).eq(&0),
        }
    }

    fn from_degree(degree: &f64, mesh_unit: &MeshUnit) -> Self {
        debug_assert!(degree.ge(&0.) && degree.le(&180.));

        let integer = degree.floor() as u32;

        let first = integer % 100;
        let second = (8. * degree).floor() as u32 - 8 * integer;
        let third = (80. * degree).floor() as u32 - 80 * integer - 10 * second;

        // max of integer is 180
        // therefore first, second and third fit u8
        // no error check required
        Self {
            first: first as u8,
            second: second as u8,
            third: match mesh_unit {
                MeshUnit::One => third as u8,
                MeshUnit::Five => {
                    if third < 5 {
                        0
                    } else {
                        5
                    }
                }
            },
        }
    }

    /// Makes the greatest [`MeshCoord`] less than latitude `degree` with `mesh_unit`.
    ///
    /// `degree` satisfies 0.0 <= and <= 66.666...
    ///
    /// # Errors
    ///
    /// Returns [`None`] when `degree` is out-of-bounds.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// let degree = 36.103774791666666;
    ///
    /// assert_eq!(
    ///     MeshCoord::try_from_latitude(&degree, &MeshUnit::One)?,
    ///     MeshCoord::try_new(54, 1, 2).unwrap()
    /// );
    /// assert_eq!(
    ///     MeshCoord::try_from_latitude(&degree, &MeshUnit::Five)?,
    ///     MeshCoord::try_new(54, 1, 0).unwrap()
    /// );
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn try_from_latitude(degree: &f64, mesh_unit: &MeshUnit) -> Option<Self> {
        if degree.is_nan() {
            return None;
        };

        let value = {
            let value = 3.0 * degree / 2.0;

            // Minimum add-hook trick to ensure the identity,
            // 1. MeshCoord::try_from_latitude(&coord.to_latitude(), &MeshUnit::One)
            // 2. MeshCoord::try_from_longitude(&coord.to_longitude(), &MeshUnit::One)
            if (degree.to_bits() % 2).eq(&1) {
                value.next_up()
            } else {
                value
            }
        };

        if value.lt(&0.0) || value.ge(&100.0) {
            return None;
        };

        Some(Self::from_degree(&value, mesh_unit))
    }

    /// Makes the greatest [`MeshCoord`] less than longitude `degree` with `mesh_unit`.
    ///
    /// `degree` satisfies 100.0 <= and <= 180.0.
    ///
    /// # Errors
    ///
    /// Returns [`None`] when `degree` is out-of-range.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// let degree = 140.08785504166664;
    ///
    /// assert_eq!(
    ///     MeshCoord::try_from_longitude(&degree, &MeshUnit::One)?,
    ///     MeshCoord::try_new(40, 0, 7).unwrap()
    /// );
    /// assert_eq!(
    ///     MeshCoord::try_from_longitude(&degree, &MeshUnit::Five)?,
    ///     MeshCoord::try_new(40, 0, 5).unwrap()
    /// );
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn try_from_longitude(degree: &f64, mesh_unit: &MeshUnit) -> Option<Self> {
        if degree.is_nan() || degree.lt(&100.0) || degree.gt(&180.0) {
            return None;
        };

        Some(Self::from_degree(degree, mesh_unit))
    }

    fn to_degree(&self) -> f64 {
        self.first as f64 + self.second as f64 / 8. + self.third as f64 / 80.
    }

    /// Returns the latitude that `self` converts into.
    ///
    /// This does not check that `self` represents latitude.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// let degree = 36.103774791666666;
    ///
    /// // MeshCoord is a component of the greatest node less than `degree`
    /// let coord = MeshCoord::try_from_latitude(&degree, &MeshUnit::One)?;
    /// assert_eq!(coord.to_latitude(), 36.1);
    ///
    /// let coord = MeshCoord::try_from_latitude(&degree, &MeshUnit::Five)?;
    /// assert_eq!(coord.to_latitude(), 36.083333333333336);
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn to_latitude(&self) -> f64 {
        2. * self.to_degree() / 3.
    }

    /// Returns the longitude that `self` converts into.
    ///
    /// This does not check that `self` represents longitude.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// let degree = 140.08785504166664;
    ///
    /// // MeshCoord is a component of the greatest node less than `degree`
    /// let coord = MeshCoord::try_from_longitude(&degree, &MeshUnit::One)?;
    /// assert_eq!(coord.to_longitude(), 140.0875);
    ///
    /// let coord = MeshCoord::try_from_longitude(&degree, &MeshUnit::Five)?;
    /// assert_eq!(coord.to_longitude(), 140.0625);
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn to_longitude(&self) -> f64 {
        100. + self.to_degree()
    }

    /// Returns the smallest [`MeshCoord`] greater than `self`.
    ///
    /// # Errors
    ///
    /// Returns [`None`] when `mesh_unit` is [`MeshUnit::Five`]
    /// although `self.third` is either `0` or `5`,
    /// or `self` is `MeshCoord { first: 99, second: 7, third: 9 }`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// let coord = MeshCoord::try_new(0, 0, 0)?;
    /// assert_eq!(coord.try_next_up(&MeshUnit::One)?, MeshCoord::try_new(0, 0, 1)?);
    /// assert_eq!(coord.try_next_up(&MeshUnit::Five)?, MeshCoord::try_new(0, 0, 5)?);
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn try_next_up(&self, mesh_unit: &MeshUnit) -> Option<Self> {
        if !self.is_mesh_unit(mesh_unit) {
            return None;
        }

        let delta: u8 = mesh_unit.into();
        // 9 for MeshUnit::One and 5 for MeshUnit::Five
        let bound = match mesh_unit {
            MeshUnit::One => 9,
            MeshUnit::Five => 5,
        };

        if self.third.eq(&bound) {
            if self.second.eq(&7) {
                if self.first.eq(&99) {
                    None
                } else {
                    // `first` is not 99
                    Some(Self {
                        first: self.first + 1,
                        second: 0,
                        third: 0,
                    })
                }
            } else {
                // `second` is not 7
                Some(Self {
                    first: self.first,
                    second: self.second + 1,
                    third: 0,
                })
            }
        } else {
            // `third` is not 1 nor 5
            Some(Self {
                first: self.first,
                second: self.second,
                third: self.third + delta,
            })
        }
    }

    /// Returns the greatest [`MeshCoord`] less than `self`.
    ///
    /// # Errors
    ///
    /// Returns [`None`] when `mesh_unit` is [`MeshUnit::Five`]
    /// although `self.third` is either `0` or `5`,
    /// or `self` is `MeshCoord { first: 0, second: 0, third: 0 }`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// assert_eq!(
    ///     MeshCoord::try_new(0, 0, 1)?.try_next_down(&MeshUnit::One)?,
    ///     MeshCoord::try_new(0, 0, 0)?
    /// );
    /// assert_eq!(
    ///     MeshCoord::try_new(0, 0, 5)?.try_next_down(&MeshUnit::Five)?,
    ///     MeshCoord::try_new(0, 0, 0)?
    /// );
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn try_next_down(&self, mesh_unit: &MeshUnit) -> Option<Self> {
        if !self.is_mesh_unit(mesh_unit) {
            return None;
        }

        let delta: u8 = mesh_unit.into();
        // 9 for MeshUnit::One and 5 for MeshUnit::Five
        let bound = match mesh_unit {
            MeshUnit::One => 9,
            MeshUnit::Five => 5,
        };

        if self.third.eq(&0) {
            if self.second.eq(&0) {
                if self.first.eq(&0) {
                    None
                } else {
                    // `first` is not 0
                    Some(Self {
                        first: self.first - 1,
                        second: 7,
                        third: bound,
                    })
                }
            } else {
                // `second` is not 0
                Some(Self {
                    first: self.first,
                    second: self.second - 1,
                    third: bound,
                })
            }
        } else {
            // `third` is not 0
            Some(Self {
                first: self.first,
                second: self.second,
                third: self.third - delta,
            })
        }
    }
}

/// Represents mesh node, a pair of [`MeshCoord`]s.
///
/// We note that this supports non-negative latitude and longitude only.
///
/// # Example
///
/// ```
/// # use jgdtrans::*;
/// # use jgdtrans::mesh::*;
/// # fn run() -> Option<()> {
/// // Construct from latitude and longitude, altitude ignores
/// let point = Point::new(36.10377479, 140.087855041, 0.0);
/// let node = MeshNode::try_from_point(&point, &MeshUnit::One)?;
/// assert_eq!(node.to_meshcode(), 54401027);
///
/// // The result depends on the selection of the mesh unit
/// let node = MeshNode::try_from_point(&point, &MeshUnit::Five)?;
/// assert_eq!(node.to_meshcode(), 54401005);
///
/// // Construct from meshcode
/// let node = MeshNode::try_from_meshcode(&54401027)?;
///
/// // The position where the MeshNode locates
/// assert_eq!(node.to_point(), Point::new(36.1, 140.0875, 0.0));
/// # Some(())}
/// # fn main() -> () {run();()}
/// ```
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct MeshNode {
    /// The mesh coord of latitude
    pub(crate) latitude: MeshCoord,
    /// The mesh coord of longitude
    ///
    /// This satisfies `MeshCoord {first: 0, second: 0, third: 0}` <=
    /// and <= `MeshCoord {first: 80, second: 0, third: 0}`
    pub(crate) longitude: MeshCoord,
}

impl From<MeshNode> for u32 {
    /// Makes a meshcode of [`MeshNode`].
    #[inline]
    fn from(value: MeshNode) -> Self {
        value.to_meshcode()
    }
}

impl MeshNode {
    /// Makes a [`MeshNode`].
    ///
    /// `longitude` satisfies `MeshCoord {first: 0, second: 0, third: 0}` <=
    /// and <= `MeshCoord {first: 80, second: 0, third: 0}`.
    ///
    /// # Errors
    ///
    /// Returns [`None`] when `longitude` is out-of-bounds.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// let latitude = MeshCoord::try_new(54, 1, 2)?;
    /// let longitude = MeshCoord::try_new(40, 0, 7)?;
    ///
    /// let node = MeshNode::try_new(latitude.clone(), longitude.clone())?;
    /// assert_eq!(node.latitude(), &latitude);
    /// assert_eq!(node.longitude(), &longitude);
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn try_new(latitude: MeshCoord, longitude: MeshCoord) -> Option<Self> {
        if longitude.gt(&MeshCoord {
            first: 80,
            second: 0,
            third: 0,
        }) {
            return None;
        };

        Some(Self {
            latitude,
            longitude,
        })
    }

    /// Returns the latitude coordinate of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// let latitude = MeshCoord::try_new(54, 1, 2)?;
    /// let longitude = MeshCoord::try_new(40, 0, 7)?;
    ///
    /// let node = MeshNode::try_new(latitude.clone(), longitude)?;
    /// assert_eq!(node.latitude(), &latitude);
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn latitude(&self) -> &MeshCoord {
        &self.latitude
    }

    /// Returns the longitude coordinate of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::{MeshCoord, MeshNode};
    /// # fn run() -> Option<()> {
    /// let latitude = MeshCoord::try_new(54, 1, 2)?;
    /// let longitude = MeshCoord::try_new(40, 0, 7)?;
    ///
    /// let node = MeshNode::try_new(latitude, longitude.clone())?;
    /// assert_eq!(node.longitude(), &longitude);
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn longitude(&self) -> &MeshCoord {
        &self.longitude
    }

    /// Returns `true` if `self` is compatible to the `mesh_unit`.
    ///
    /// This always returns `true` when [`MeshUnit::One`] given.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// let node = MeshNode::try_from_meshcode(&54401027)?;
    /// assert_eq!(node.is_mesh_unit(&MeshUnit::One), true);
    /// assert_eq!(node.is_mesh_unit(&MeshUnit::Five), false);
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    #[inline]
    pub fn is_mesh_unit(&self, mesh_unit: &MeshUnit) -> bool {
        match mesh_unit {
            MeshUnit::One => true,
            MeshUnit::Five => {
                self.latitude.is_mesh_unit(mesh_unit) && self.longitude.is_mesh_unit(mesh_unit)
            }
        }
    }

    /// Makes the nearest north-west [`MeshNode`] of `point`.
    ///
    /// This is independent of [`point.altitude`](Point::altitude).
    ///
    /// # Errors
    ///
    /// Returns [`None`] when [`point.latitude`](Point::longitude)
    /// and/or [`point.longitude`](Point::longitude) is out-of-bounds.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// let point = Point::new(36.10377479, 140.087855041, 0.0);
    ///
    /// assert_eq!(
    ///     MeshNode::try_from_point(&point, &MeshUnit::One)?,
    ///     MeshNode::try_new(
    ///         MeshCoord::try_new(54, 1, 2)?,
    ///         MeshCoord::try_new(40, 0, 7)?
    ///     )?
    /// );
    /// assert_eq!(
    ///     MeshNode::try_from_point(&point, &MeshUnit::Five)?,
    ///     MeshNode::try_new(
    ///         MeshCoord::try_new(54, 1, 0)?,
    ///         MeshCoord::try_new(40, 0, 5)?
    ///     )?
    /// );
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn try_from_point(point: &Point, mesh_unit: &MeshUnit) -> Option<Self> {
        let latitude = MeshCoord::try_from_latitude(&point.latitude, mesh_unit)?;
        let longitude = MeshCoord::try_from_longitude(&point.longitude, mesh_unit)?;

        Some(Self {
            latitude,
            longitude,
        })
    }

    /// Makes a [`MeshNode`] represented by `meshcode`.
    ///
    /// This is inverse of [`MeshNode::to_meshcode()`].
    ///
    /// # Errors
    ///
    /// Returns [`None`] when an invalid `meshcode` given.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// assert_eq!(
    ///     MeshNode::try_from_meshcode(&54401027)?,
    ///     MeshNode::try_new(
    ///         MeshCoord::try_new(54, 1, 2)?,
    ///         MeshCoord::try_new(40, 0, 7)?
    ///     )?
    /// );
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn try_from_meshcode(meshcode: &u32) -> Option<Self> {
        #[allow(clippy::inconsistent_digit_grouping)]
        if meshcode.ge(&10000_00_00) {
            return None;
        }

        macro_rules! div_rem {
            ($n:ident, $m:literal) => {
                ($n / $m, $n % $m)
            };
        }

        // code < 10000_00_00
        // lat_first, lng_first < 100
        #[allow(clippy::inconsistent_digit_grouping)]
        let (lat_first, rest) = div_rem!(meshcode, 100_00_00_u32);
        #[allow(clippy::inconsistent_digit_grouping)]
        let (lng_first, rest) = div_rem!(rest, 100_00_u32);

        // lat_second, lng_second < 8
        let (lat_second, rest) = div_rem!(rest, 10_00_u32);
        let (lng_second, rest) = div_rem!(rest, 100_u32);

        // lat_third, lng_third < 10
        let (lat_third, lng_third) = div_rem!(rest, 10_u32);

        let latitude = MeshCoord::try_new(lat_first as u8, lat_second as u8, lat_third as u8)?;
        let longitude = MeshCoord::try_new(lng_first as u8, lng_second as u8, lng_third as u8)?;

        Self::try_new(latitude, longitude)
    }

    /// Returns a meshcode represents `self`.
    ///
    /// The result is up to 8 digits.
    ///
    /// This method is an inverse of [`MeshNode::try_from_meshcode()`].
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// let node = MeshNode::try_new(
    ///     MeshCoord::try_new(54, 1, 2)?,
    ///     MeshCoord::try_new(40, 0, 7)?
    /// )?;
    ///
    /// assert_eq!(node.to_meshcode(), 54401027);
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn to_meshcode(&self) -> u32 {
        (self.latitude.first as u32 * 100 + self.longitude.first as u32) * 10_000
            + (self.latitude.second as u32 * 10 + self.longitude.second as u32) * 100
            + (self.latitude.third as u32 * 10 + self.longitude.third as u32)
    }

    /// Returns a [`Point`] (latitude and longitude) where `self` locates.
    ///
    /// The resulting altitude is 0.0.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// let node = MeshNode::try_new(
    ///     MeshCoord::try_new(54, 1, 2)?,
    ///     MeshCoord::try_new(40, 0, 7)?
    /// )?;
    ///
    /// assert_eq!(node.to_point(), Point::new(36.1, 140.0875, 0.0));
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn to_point(&self) -> Point {
        Point::new(
            self.latitude.to_latitude(),
            self.longitude.to_longitude(),
            0.0,
        )
    }
}

/// Represents unit mesh cell, a quadruplet of [`MeshNode`]s and [`MeshUnit`].
///
/// This has no other [`MeshNode`]s inside `self` in the unit.
///
/// The cell is, roughly, a square with `mesh_unit` \[km\] length edges.
///
/// # Example
///
/// ```
/// # use jgdtrans::*;
/// # use jgdtrans::mesh::*;
/// # fn run() -> Option<()> {
/// // Construct from latitude and longitude, altitude ignores
/// // (The result depends on the selection of the mesh unit)
/// let point = Point::new(36.10377479, 140.087855041, 0.0);
/// let cell = MeshCell::try_from_point(&point, MeshUnit::One)?;
/// assert_eq!(cell.south_west(), &MeshNode::try_from_meshcode(&54401027)?);
/// assert_eq!(cell.south_east(), &MeshNode::try_from_meshcode(&54401028)?);
/// assert_eq!(cell.north_west(), &MeshNode::try_from_meshcode(&54401037)?);
/// assert_eq!(cell.north_east(), &MeshNode::try_from_meshcode(&54401038)?);
///
/// // Construct from node
/// let node = MeshNode::try_from_meshcode(&54401027)?;
/// assert_eq!(MeshCell::try_from_node(node, MeshUnit::One)?, cell);
///
/// // Construct from meshcode
/// assert_eq!(MeshCell::try_from_meshcode(&54401027, MeshUnit::One)?, cell);
///
/// // Find the position within cell, from 0.0 to 1.0
/// // (Again, the result depends on the selection of the mesh unit)
/// let (latitude, longitude) = cell.position(&point);
/// assert_eq!(latitude, 0.4529748000001632);
/// assert_eq!(longitude, 0.028403280000475206);
///
/// // the south-west node of the cell is (0, 0), origin
/// let (latitude, longitude) = cell.position(&cell.south_west().to_point());
/// assert!((0.0 - latitude).abs() < 1e-12);
/// assert!((0.0 - longitude).abs() < 1e-12);
///
/// // the north-east node is (1, 1)
/// let (latitude, longitude) = cell.position(&cell.north_east().to_point());
/// assert!((1.0 - latitude).abs() < 1e-12);
/// assert!((1.0 - longitude).abs() < 1e-12);
/// # Some(())}
/// # fn main() -> () {run();()}
/// ```
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct MeshCell {
    /// The south-west node of the cell
    pub(crate) south_west: MeshNode,
    /// The south-east node of the cell
    pub(crate) south_east: MeshNode,
    /// The north-west node of the cell
    pub(crate) north_west: MeshNode,
    /// The north-east node of the cell
    pub(crate) north_east: MeshNode,
    /// The mesh unit which is consistent with nodes
    pub(crate) mesh_unit: MeshUnit,
}

impl MeshCell {
    /// Makes a [`MeshCell`].
    ///
    /// # Errors
    ///
    /// Returns [`None`] when the nodes and `mesh_unit` does not
    /// construct a unit cell.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// let sw = MeshNode::try_from_meshcode(&54401027)?;
    /// let se = MeshNode::try_from_meshcode(&54401028)?;
    /// let nw = MeshNode::try_from_meshcode(&54401037)?;
    /// let ne = MeshNode::try_from_meshcode(&54401038)?;
    /// let cell = MeshCell::try_new(sw.clone(), se.clone(), nw.clone(), ne.clone(), MeshUnit::One)?;
    ///
    /// assert_eq!(cell.south_west(), &sw);
    /// assert_eq!(cell.south_east(), &se);
    /// assert_eq!(cell.north_west(), &nw);
    /// assert_eq!(cell.north_east(), &ne);
    /// assert_eq!(cell.mesh_unit(), &MeshUnit::One);
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn try_new(
        south_west: MeshNode,
        south_east: MeshNode,
        north_west: MeshNode,
        north_east: MeshNode,
        mesh_unit: MeshUnit,
    ) -> Option<Self> {
        // consistently on unit v.s. the third
        if !south_west.is_mesh_unit(&mesh_unit)
            || !south_east.is_mesh_unit(&mesh_unit)
            || !north_west.is_mesh_unit(&mesh_unit)
            || !north_east.is_mesh_unit(&mesh_unit)
        {
            return None;
        };

        let lat_next = south_west.latitude.try_next_up(&mesh_unit)?;
        let lng_next = south_west.longitude.try_next_up(&mesh_unit)?;

        if lat_next.ne(&north_west.latitude) || south_west.longitude.ne(&north_west.longitude) {
            return None;
        }
        if south_west.latitude.ne(&south_east.latitude) || lng_next.ne(&south_east.longitude) {
            return None;
        }
        if lat_next.ne(&north_east.latitude) || lng_next.ne(&north_east.longitude) {
            return None;
        }

        Some(Self {
            south_west,
            south_east,
            north_west,
            north_east,
            mesh_unit,
        })
    }

    /// Returns the south-west node of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// let sw = MeshNode::try_from_meshcode(&54401027)?;
    /// let se = MeshNode::try_from_meshcode(&54401028)?;
    /// let nw = MeshNode::try_from_meshcode(&54401037)?;
    /// let ne = MeshNode::try_from_meshcode(&54401038)?;
    /// let cell = MeshCell::try_new(sw.clone(), se, nw, ne, MeshUnit::One)?;
    ///
    /// assert_eq!(cell.south_west(), &sw);
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn south_west(&self) -> &MeshNode {
        &self.south_west
    }

    /// Returns the south-east node of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// let south_west = MeshNode::try_from_meshcode(&54401027)?;
    /// let south_east = MeshNode::try_from_meshcode(&54401028)?;
    /// let north_west = MeshNode::try_from_meshcode(&54401037)?;
    /// let north_east = MeshNode::try_from_meshcode(&54401038)?;
    /// let cell = MeshCell::try_new(south_west, south_east.clone(), north_west, north_east, MeshUnit::One)?;
    ///
    /// assert_eq!(cell.south_east(), &south_east);
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn south_east(&self) -> &MeshNode {
        &self.south_east
    }

    /// Returns the north-west node of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// let south_west = MeshNode::try_from_meshcode(&54401027)?;
    /// let south_east = MeshNode::try_from_meshcode(&54401028)?;
    /// let north_west = MeshNode::try_from_meshcode(&54401037)?;
    /// let north_east = MeshNode::try_from_meshcode(&54401038)?;
    /// let cell = MeshCell::try_new(south_west, south_east, north_west.clone(), north_east, MeshUnit::One)?;
    ///
    /// assert_eq!(cell.north_west(), &north_west);
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn north_west(&self) -> &MeshNode {
        &self.north_west
    }

    /// Returns the north-east node of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// let south_west = MeshNode::try_from_meshcode(&54401027)?;
    /// let south_east = MeshNode::try_from_meshcode(&54401028)?;
    /// let north_west = MeshNode::try_from_meshcode(&54401037)?;
    /// let north_east = MeshNode::try_from_meshcode(&54401038)?;
    /// let cell = MeshCell::try_new(south_west, south_east, north_west, north_east.clone(), MeshUnit::One)?;
    ///
    /// assert_eq!(cell.north_east(), &north_east);
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn north_east(&self) -> &MeshNode {
        &self.north_east
    }

    /// Returns the mesh unit of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// let south_west = MeshNode::try_from_meshcode(&54401027)?;
    /// let south_east = MeshNode::try_from_meshcode(&54401028)?;
    /// let north_west = MeshNode::try_from_meshcode(&54401037)?;
    /// let north_east = MeshNode::try_from_meshcode(&54401038)?;
    /// let cell = MeshCell::try_new(south_west, south_east, north_west, north_east, MeshUnit::One)?;
    ///
    /// assert_eq!(cell.mesh_unit(), &MeshUnit::One);
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn mesh_unit(&self) -> &MeshUnit {
        &self.mesh_unit
    }

    /// Makes a [`MeshCell`] with the south-east [`MeshNode`] which represented by meshcode `code`.
    ///
    /// # Errors
    ///
    /// Returns [`None`] when an invalid `meshcode` given,
    /// or it cannot construct a unit cell.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// assert_eq!(
    ///     MeshCell::try_from_meshcode(&54401027, MeshUnit::One)?,
    ///     MeshCell::try_new(
    ///         // south_west
    ///         MeshNode::try_from_meshcode(&54401027)?,
    ///         // south_east
    ///         MeshNode::try_from_meshcode(&54401028)?,
    ///         // north_west
    ///         MeshNode::try_from_meshcode(&54401037)?,
    ///         // north_east
    ///         MeshNode::try_from_meshcode(&54401038)?,
    ///         // mesh_unit
    ///         MeshUnit::One
    ///     )?
    /// );
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn try_from_meshcode(meshcode: &u32, mesh_unit: MeshUnit) -> Option<Self> {
        let sw = MeshNode::try_from_meshcode(meshcode)?;
        Self::try_from_node(sw, mesh_unit)
    }

    /// Makes a [`MeshCell`] that has `node` as a south-west node.
    ///
    /// # Errors
    ///
    /// Returns [`None`] when it cannot construct a unit cell.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// let code = 54401027;
    /// let south_west = MeshNode::try_from_meshcode(&54401027)?;
    ///
    /// assert_eq!(
    ///     MeshCell::try_from_node(south_west, MeshUnit::One)?,
    ///     MeshCell::try_from_meshcode(&54401027, MeshUnit::One)?
    /// );
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn try_from_node(node: MeshNode, mesh_unit: MeshUnit) -> Option<Self> {
        let next_lat_coord = node.latitude.try_next_up(&mesh_unit)?;
        let next_lng_coord = node.longitude.try_next_up(&mesh_unit)?;

        // Call MeshNode::try_new
        // to check next_coord_lat
        let south_east = MeshNode::try_new(node.latitude.clone(), next_lng_coord.clone())?;
        let north_west = MeshNode::try_new(next_lat_coord.clone(), node.longitude.clone())?;
        let north_east = MeshNode::try_new(next_lat_coord, next_lng_coord)?;

        Some(Self {
            south_west: node,
            south_east,
            north_west,
            north_east,
            mesh_unit,
        })
    }

    /// Makes a [`MeshCell`] which contains a [`Point`].
    ///
    /// The result is independent on [`point.altitude`](Point::altitude).
    ///
    /// # Errors
    ///
    /// Returns [`None`] when it cannot construct a unit cell.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// let point: Point = Point::new(36.10377479, 140.087855041, 0.0);
    ///
    /// assert_eq!(
    ///     MeshCell::try_from_point(&point, MeshUnit::One)?,
    ///     MeshCell::try_new(
    ///         MeshNode::try_from_meshcode(&54401027)?,
    ///         MeshNode::try_from_meshcode(&54401028)?,
    ///         MeshNode::try_from_meshcode(&54401037)?,
    ///         MeshNode::try_from_meshcode(&54401038)?,
    ///         MeshUnit::One
    ///     )?
    /// );
    /// assert_eq!(
    ///     MeshCell::try_from_point(&point, MeshUnit::Five)?,
    ///     MeshCell::try_new(
    ///         MeshNode::try_from_meshcode(&54401005)?,
    ///         MeshNode::try_from_meshcode(&54401100)?,
    ///         MeshNode::try_from_meshcode(&54401055)?,
    ///         MeshNode::try_from_meshcode(&54401150)?,
    ///         MeshUnit::Five
    ///     )?
    /// );
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn try_from_point(point: &Point, mesh_unit: MeshUnit) -> Option<Self> {
        let node = MeshNode::try_from_point(point, &mesh_unit)?;
        Self::try_from_node(node, mesh_unit)
    }

    /// Return the position in the cell.
    ///
    /// This returns from 0.0 to 1.0 for each latitude and longitude
    /// if `point` is inside `self`.
    ///
    /// We note that the result is a (latitude, longitude) pair,
    /// not a (right-handed) (y, x) pair.
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// // sample latitude and longitude
    /// let point = Point::new(36.10377479, 140.087855041, 0.0);
    ///
    /// let cell = MeshCell::try_from_point(&point, MeshUnit::One)?;
    /// // the south-west of the cell is (0, 0), origin
    /// let (latitude, longitude) = cell.position(&cell.south_west().to_point());
    /// assert!((0.0 - latitude).abs() < 1e-12);
    /// assert!((0.0 - longitude).abs() < 1e-12);
    /// // the south-east is (0, 1)
    /// let (latitude, longitude) = cell.position(&cell.south_east().to_point());
    /// assert!((0.0 - latitude).abs() < 1e-12);
    /// assert!((1.0 - longitude).abs() < 1e-12);
    /// // the north-west is (1, 0)
    /// let (latitude, longitude) = cell.position(&cell.north_west().to_point());
    /// assert!((1.0 - latitude).abs() < 1e-12);
    /// assert!((0.0 - longitude).abs() < 1e-12);
    /// // the north-east is (1, 1)
    /// let (latitude, longitude) = cell.position(&cell.north_east().to_point());
    /// assert!((1.0 - latitude).abs() < 1e-12);
    /// assert!((1.0 - longitude).abs() < 1e-12);
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn run() -> Option<()> {
    /// let point = Point::new(36.10377479, 140.087855041, 0.0);
    ///
    /// let cell = MeshCell::try_from_point(&point, MeshUnit::One)?;
    /// assert_eq!(
    ///     cell.position(&point),
    ///     (0.4529748000001632, 0.028403280000475206)
    /// );
    ///
    /// // the result depends on unit
    /// let cell = MeshCell::try_from_point(&point, MeshUnit::Five)?;
    /// assert_eq!(
    ///     cell.position(&point),
    ///     (0.4905949600000099, 0.405680656000186)
    /// );
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn position(&self, point: &Point) -> (f64, f64) {
        let lat = point.latitude - self.south_west.latitude.to_latitude();
        let lng = point.longitude - self.south_west.longitude.to_longitude();

        // The cell stretches 1.5 times in the latitude direction
        // compared to the longitude direction,
        // then here uses 120 = 1.5 * 80.
        match self.mesh_unit {
            MeshUnit::One => (120. * lat, 80. * lng),
            MeshUnit::Five => (24. * lat, 16. * lng),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod tests_mesh_coord {
        use super::*;

        #[test]
        fn test_try_new() {
            assert!(MeshCoord::try_new(100, 0, 0).is_none());
            assert!(MeshCoord::try_new(99, 8, 0).is_none());
            assert!(MeshCoord::try_new(99, 7, 10).is_none());
        }

        #[test]
        fn test_getter() {
            let coord = MeshCoord::try_new(99, 7, 9).unwrap();
            assert_eq!(coord.first(), &99);
            assert_eq!(coord.second(), &7);
            assert_eq!(coord.third(), &9);
        }

        #[test]
        fn test_try_from_latitude() {
            // unsupported value
            assert!(MeshCoord::try_from_latitude(&f64::NAN, &MeshUnit::One).is_none());
            assert!(MeshCoord::try_from_latitude(&0.0f64.next_down(), &MeshUnit::One).is_none());
            assert!(MeshCoord::try_from_latitude(&66.666666666666666666, &MeshUnit::One).is_none());

            // on-the-bound
            assert_eq!(
                MeshCoord::try_from_latitude(&0.0, &MeshUnit::One).unwrap(),
                MeshCoord::try_new(0, 0, 0).unwrap()
            );
            assert_eq!(
                MeshCoord::try_from_latitude(&66.66666666666665, &MeshUnit::One).unwrap(),
                MeshCoord::try_new(99, 7, 9).unwrap()
            );

            // healthy
            assert_eq!(
                MeshCoord::try_from_latitude(&36.103774791666666, &MeshUnit::One).unwrap(),
                MeshCoord::try_new(54, 1, 2).unwrap()
            );
            assert_eq!(
                MeshCoord::try_from_latitude(&36.103774791666666, &MeshUnit::Five).unwrap(),
                MeshCoord::try_new(54, 1, 0).unwrap()
            );
        }

        #[test]
        fn test_try_from_longitude() {
            // unsupported value
            assert!(MeshCoord::try_from_longitude(&f64::NAN, &MeshUnit::One).is_none());
            assert!(MeshCoord::try_from_longitude(&100.0f64.next_down(), &MeshUnit::One).is_none());
            assert!(MeshCoord::try_from_longitude(&180.0f64.next_up(), &MeshUnit::One).is_none());

            // on-the-bound
            assert_eq!(
                MeshCoord::try_from_longitude(&100.0, &MeshUnit::One).unwrap(),
                MeshCoord::try_new(0, 0, 0).unwrap()
            );
            assert_eq!(
                MeshCoord::try_from_longitude(&180.0, &MeshUnit::One).unwrap(),
                MeshCoord::try_new(80, 0, 0).unwrap()
            );

            // healthy
            assert_eq!(
                MeshCoord::try_from_longitude(&140.08785504166664, &MeshUnit::One).unwrap(),
                MeshCoord::try_new(40, 0, 7).unwrap()
            );
            assert_eq!(
                MeshCoord::try_from_longitude(&140.08785504166664, &MeshUnit::Five).unwrap(),
                MeshCoord::try_new(40, 0, 5).unwrap()
            );
        }

        #[test]
        fn test_to_latitude() {
            let v = 36.103774791666666;

            assert_eq!(
                MeshCoord::try_from_latitude(&v, &MeshUnit::One)
                    .unwrap()
                    .to_latitude(),
                36.1,
            );
            assert_eq!(
                MeshCoord::try_from_latitude(&v, &MeshUnit::Five)
                    .unwrap()
                    .to_latitude(),
                36.083333333333336,
            );
        }

        #[test]
        fn test_to_longitude() {
            let v = 140.08785504166664;

            assert_eq!(
                MeshCoord::try_from_longitude(&v, &MeshUnit::One)
                    .unwrap()
                    .to_longitude(),
                140.0875,
            );
            assert_eq!(
                MeshCoord::try_from_longitude(&v, &MeshUnit::Five)
                    .unwrap()
                    .to_longitude(),
                140.0625,
            );
        }

        #[test]
        fn test_try_next_up() {
            // error
            assert!(MeshCoord::try_new(0, 7, 2)
                .unwrap()
                .try_next_up(&MeshUnit::Five)
                .is_none());
            assert!(MeshCoord::try_new(99, 7, 9)
                .unwrap()
                .try_next_up(&MeshUnit::One)
                .is_none());
            assert!(MeshCoord::try_new(99, 7, 5)
                .unwrap()
                .try_next_up(&MeshUnit::Five)
                .is_none());

            // healty
            assert_eq!(
                MeshCoord::try_new(0, 0, 0)
                    .unwrap()
                    .try_next_up(&MeshUnit::One)
                    .unwrap(),
                MeshCoord::try_new(0, 0, 1).unwrap(),
            );
            assert_eq!(
                MeshCoord::try_new(0, 0, 0)
                    .unwrap()
                    .try_next_up(&MeshUnit::Five)
                    .unwrap(),
                MeshCoord::try_new(0, 0, 5).unwrap(),
            );

            // healty: carry
            assert_eq!(
                MeshCoord::try_new(0, 0, 9)
                    .unwrap()
                    .try_next_up(&MeshUnit::One)
                    .unwrap(),
                MeshCoord::try_new(0, 1, 0).unwrap(),
            );
            assert_eq!(
                MeshCoord::try_new(0, 7, 9)
                    .unwrap()
                    .try_next_up(&MeshUnit::One)
                    .unwrap(),
                MeshCoord::try_new(1, 0, 0).unwrap(),
            );

            assert_eq!(
                MeshCoord::try_new(0, 0, 5)
                    .unwrap()
                    .try_next_up(&MeshUnit::Five)
                    .unwrap(),
                MeshCoord::try_new(0, 1, 0).unwrap(),
            );
            assert_eq!(
                MeshCoord::try_new(0, 7, 5)
                    .unwrap()
                    .try_next_up(&MeshUnit::Five)
                    .unwrap(),
                MeshCoord::try_new(1, 0, 0).unwrap(),
            );
        }

        #[test]
        fn test_try_next_down() {
            // error
            assert!(MeshCoord::try_new(0, 7, 2)
                .unwrap()
                .try_next_down(&MeshUnit::Five)
                .is_none());
            assert!(MeshCoord::try_new(0, 0, 0)
                .unwrap()
                .try_next_down(&MeshUnit::One)
                .is_none());

            // healty
            assert_eq!(
                MeshCoord::try_new(0, 0, 1)
                    .unwrap()
                    .try_next_down(&MeshUnit::One)
                    .unwrap(),
                MeshCoord::try_new(0, 0, 0).unwrap(),
            );
            assert_eq!(
                MeshCoord::try_new(0, 0, 5)
                    .unwrap()
                    .try_next_down(&MeshUnit::Five)
                    .unwrap(),
                MeshCoord::try_new(0, 0, 0).unwrap(),
            );

            // healty: carry
            assert_eq!(
                MeshCoord::try_new(0, 1, 0)
                    .unwrap()
                    .try_next_down(&MeshUnit::One)
                    .unwrap(),
                MeshCoord::try_new(0, 0, 9).unwrap(),
            );
            assert_eq!(
                MeshCoord::try_new(1, 0, 0)
                    .unwrap()
                    .try_next_down(&MeshUnit::One)
                    .unwrap(),
                MeshCoord::try_new(0, 7, 9).unwrap(),
            );

            assert_eq!(
                MeshCoord::try_new(0, 1, 0)
                    .unwrap()
                    .try_next_down(&MeshUnit::Five)
                    .unwrap(),
                MeshCoord::try_new(0, 0, 5).unwrap(),
            );
            assert_eq!(
                MeshCoord::try_new(1, 0, 0)
                    .unwrap()
                    .try_next_down(&MeshUnit::Five)
                    .unwrap(),
                MeshCoord::try_new(0, 7, 5).unwrap(),
            );
        }

        #[test]
        fn test_identity_on_from_to() {
            // latitude
            let bound = MeshCoord::try_new(99, 7, 9).unwrap();
            let mut coord = MeshCoord::try_new(0, 0, 0).unwrap();
            while coord != bound {
                assert_eq!(
                    coord,
                    MeshCoord::try_from_latitude(&coord.to_latitude(), &MeshUnit::One).unwrap(),
                );
                coord = coord.try_next_up(&MeshUnit::One).unwrap();
            }
            assert_eq!(
                coord,
                MeshCoord::try_from_latitude(&coord.to_latitude(), &MeshUnit::One).unwrap(),
            );

            // longitude
            let bound = MeshCoord::try_new(80, 0, 0).unwrap();
            let mut coord = MeshCoord::try_new(0, 0, 0).unwrap();
            while coord != bound {
                assert_eq!(
                    coord,
                    MeshCoord::try_from_longitude(&coord.to_longitude(), &MeshUnit::One).unwrap(),
                );
                coord = coord.try_next_up(&MeshUnit::One).unwrap();
            }
            assert_eq!(
                coord,
                MeshCoord::try_from_longitude(&coord.to_longitude(), &MeshUnit::One).unwrap(),
            );
        }
    }

    mod tests_mesh_node {
        use super::*;

        #[test]
        fn test_try_new() {
            let mut coord = MeshCoord::try_new(0, 0, 0).unwrap();

            while coord.le(&MeshCoord::try_new(80, 0, 0).unwrap()) {
                let temp = MeshNode::try_new(MeshCoord::try_new(0, 0, 0).unwrap(), coord.clone());
                assert!(temp.is_some());
                coord = coord.try_next_up(&MeshUnit::One).unwrap();
            }

            while coord.lt(&MeshCoord::try_new(99, 7, 9).unwrap()) {
                let temp = MeshNode::try_new(MeshCoord::try_new(0, 0, 0).unwrap(), coord.clone());
                assert!(temp.is_none());
                coord = coord.try_next_up(&MeshUnit::One).unwrap();
            }
            assert!(MeshNode::try_new(MeshCoord::try_new(0, 0, 0).unwrap(), coord,).is_none());
        }

        #[test]
        fn test_getter() {
            let node = MeshNode::try_new(
                MeshCoord::try_new(54, 1, 2).unwrap(),
                MeshCoord::try_new(40, 0, 7).unwrap(),
            )
            .unwrap();

            assert_eq!(node.latitude(), &MeshCoord::try_new(54, 1, 2).unwrap());
            assert_eq!(node.longitude(), &MeshCoord::try_new(40, 0, 7).unwrap());
        }

        #[test]
        fn test_try_from_point() {
            let point = Point::new(36.103774791666666, 140.08785504166664, 10.0);

            assert_eq!(
                MeshNode::try_from_point(&point, &MeshUnit::One).unwrap(),
                MeshNode::try_new(
                    MeshCoord::try_new(54, 1, 2).unwrap(),
                    MeshCoord::try_new(40, 0, 7).unwrap()
                )
                .unwrap()
            );

            assert_eq!(
                MeshNode::try_from_point(&point, &MeshUnit::Five).unwrap(),
                MeshNode::try_new(
                    MeshCoord::try_new(54, 1, 0).unwrap(),
                    MeshCoord::try_new(40, 0, 5).unwrap()
                )
                .unwrap()
            );
        }

        #[test]
        fn test_try_from_meshcode() {
            // error
            assert!(MeshNode::try_from_meshcode(&54401827).is_none());
            assert!(MeshNode::try_from_meshcode(&54408027).is_none());
            assert!(MeshNode::try_from_meshcode(&54801021).is_none());
            assert!(MeshNode::try_from_meshcode(&54801120).is_none());
            assert!(MeshNode::try_from_meshcode(&54811020).is_none());
            assert!(MeshNode::try_from_meshcode(&100000000).is_none());

            // healthy
            assert_eq!(
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshNode::try_new(
                    MeshCoord::try_new(54, 1, 2).unwrap(),
                    MeshCoord::try_new(40, 0, 7).unwrap()
                )
                .unwrap()
            );
            assert_eq!(
                MeshNode::try_from_meshcode(&0).unwrap(),
                MeshNode::try_new(
                    MeshCoord::try_new(0, 0, 0).unwrap(),
                    MeshCoord::try_new(0, 0, 0).unwrap()
                )
                .unwrap()
            );
        }

        #[test]
        fn test_to_meshcode() {
            assert_eq!(
                MeshNode::try_new(
                    MeshCoord::try_new(54, 1, 2).unwrap(),
                    MeshCoord::try_new(40, 0, 7).unwrap()
                )
                .unwrap()
                .to_meshcode(),
                54401027
            )
        }

        #[test]
        fn test_to_point() {
            assert_eq!(
                MeshNode::try_new(
                    MeshCoord::try_new(54, 1, 2).unwrap(),
                    MeshCoord::try_new(40, 0, 7).unwrap()
                )
                .unwrap()
                .to_point(),
                Point::new(36.1, 140.0875, 0.0)
            )
        }

        #[test]
        fn test_identity() {
            // on latitude and longitude is
            // tested by tests_mesh_coord::test_identity

            //
            // latitude
            //
            let bound = MeshNode::try_new(
                MeshCoord::try_new(99, 7, 9).unwrap(),
                MeshCoord::try_new(0, 0, 0).unwrap(),
            )
            .unwrap();
            let mut node = MeshNode::try_new(
                MeshCoord::try_new(0, 0, 0).unwrap(),
                MeshCoord::try_new(0, 0, 0).unwrap(),
            )
            .unwrap();
            while node != bound {
                assert_eq!(
                    node,
                    MeshNode::try_from_meshcode(&node.to_meshcode()).unwrap()
                );
                node = MeshNode::try_new(
                    node.latitude().try_next_up(&MeshUnit::One).unwrap(),
                    MeshCoord::try_new(0, 0, 0).unwrap(),
                )
                .unwrap();
            }

            // for MeshCoord(99, 7, 9)
            assert_eq!(
                node,
                MeshNode::try_from_meshcode(&node.to_meshcode()).unwrap()
            );

            //
            // longitude
            //
            let bound = MeshNode::try_new(
                MeshCoord::try_new(0, 0, 0).unwrap(),
                MeshCoord::try_new(80, 0, 0).unwrap(),
            )
            .unwrap();
            let mut node = MeshNode::try_new(
                MeshCoord::try_new(0, 0, 0).unwrap(),
                MeshCoord::try_new(0, 0, 0).unwrap(),
            )
            .unwrap();

            while node != bound {
                assert_eq!(
                    node,
                    MeshNode::try_from_meshcode(&node.to_meshcode()).unwrap()
                );
                node = MeshNode::try_new(
                    MeshCoord::try_new(0, 0, 0).unwrap(),
                    node.longitude().try_next_up(&MeshUnit::One).unwrap(),
                )
                .unwrap();
            }

            // for MeshCoord(80, 0,0 )
            assert_eq!(
                node,
                MeshNode::try_from_meshcode(&node.to_meshcode()).unwrap()
            );
        }
    }

    mod tests_mesh_cell {
        use super::*;

        #[test]
        fn test_try_new() {
            // healty
            assert!(MeshCell::try_new(
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshNode::try_from_meshcode(&54401028).unwrap(),
                MeshNode::try_from_meshcode(&54401037).unwrap(),
                MeshNode::try_from_meshcode(&54401038).unwrap(),
                MeshUnit::One
            )
            .is_some());
            assert!(MeshCell::try_new(
                MeshNode::try_from_meshcode(&54401005).unwrap(),
                MeshNode::try_from_meshcode(&54401100).unwrap(),
                MeshNode::try_from_meshcode(&54401055).unwrap(),
                MeshNode::try_from_meshcode(&54401150).unwrap(),
                MeshUnit::Five
            )
            .is_some());

            // error
            // incorrect unit
            assert!(MeshCell::try_new(
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshNode::try_from_meshcode(&54401028).unwrap(),
                MeshNode::try_from_meshcode(&54401037).unwrap(),
                MeshNode::try_from_meshcode(&54401038).unwrap(),
                MeshUnit::Five
            )
            .is_none());
            assert!(MeshCell::try_new(
                MeshNode::try_from_meshcode(&54401005).unwrap(),
                MeshNode::try_from_meshcode(&54401100).unwrap(),
                MeshNode::try_from_meshcode(&54401055).unwrap(),
                MeshNode::try_from_meshcode(&54401150).unwrap(),
                MeshUnit::One
            )
            .is_none());

            // not a unit cell
            // longitude
            assert!(MeshCell::try_new(
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshNode::try_from_meshcode(&54401037).unwrap(),
                MeshNode::try_from_meshcode(&54401038).unwrap(),
                MeshUnit::One
            )
            .is_none());
            assert!(MeshCell::try_new(
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshNode::try_from_meshcode(&54401028).unwrap(),
                MeshNode::try_from_meshcode(&54401036).unwrap(),
                MeshNode::try_from_meshcode(&54401038).unwrap(),
                MeshUnit::One
            )
            .is_none());
            assert!(MeshCell::try_new(
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshNode::try_from_meshcode(&54401028).unwrap(),
                MeshNode::try_from_meshcode(&54401037).unwrap(),
                MeshNode::try_from_meshcode(&54401037).unwrap(),
                MeshUnit::One
            )
            .is_none());

            // latitude
            assert!(MeshCell::try_new(
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshNode::try_from_meshcode(&54401018).unwrap(),
                MeshNode::try_from_meshcode(&54401037).unwrap(),
                MeshNode::try_from_meshcode(&54401038).unwrap(),
                MeshUnit::One
            )
            .is_none());
            assert!(MeshCell::try_new(
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshNode::try_from_meshcode(&54401028).unwrap(),
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshNode::try_from_meshcode(&54401038).unwrap(),
                MeshUnit::One
            )
            .is_none());
            assert!(MeshCell::try_new(
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshNode::try_from_meshcode(&54401028).unwrap(),
                MeshNode::try_from_meshcode(&54401037).unwrap(),
                MeshNode::try_from_meshcode(&54401028).unwrap(),
                MeshUnit::One
            )
            .is_none());
        }

        #[test]
        fn test_getter() {
            let cell = MeshCell::try_new(
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshNode::try_from_meshcode(&54401028).unwrap(),
                MeshNode::try_from_meshcode(&54401037).unwrap(),
                MeshNode::try_from_meshcode(&54401038).unwrap(),
                MeshUnit::One,
            )
            .unwrap();

            assert_eq!(
                cell.south_west(),
                &MeshNode::try_from_meshcode(&54401027).unwrap()
            );
            assert_eq!(
                cell.south_east(),
                &MeshNode::try_from_meshcode(&54401028).unwrap()
            );
            assert_eq!(
                cell.north_west(),
                &MeshNode::try_from_meshcode(&54401037).unwrap()
            );
            assert_eq!(
                cell.north_east(),
                &MeshNode::try_from_meshcode(&54401038).unwrap()
            );
            assert_eq!(cell.mesh_unit(), &MeshUnit::One);
        }

        #[test]
        fn test_try_from_meshcode() {
            assert_eq!(
                MeshCell::try_from_meshcode(&54401027, MeshUnit::One).unwrap(),
                MeshCell::try_new(
                    MeshNode::try_from_meshcode(&54401027).unwrap(),
                    MeshNode::try_from_meshcode(&54401028).unwrap(),
                    MeshNode::try_from_meshcode(&54401037).unwrap(),
                    MeshNode::try_from_meshcode(&54401038).unwrap(),
                    MeshUnit::One
                )
                .unwrap()
            );
            assert_eq!(
                MeshCell::try_from_meshcode(&54401005, MeshUnit::Five).unwrap(),
                MeshCell::try_new(
                    MeshNode::try_from_meshcode(&54401005).unwrap(),
                    MeshNode::try_from_meshcode(&54401100).unwrap(),
                    MeshNode::try_from_meshcode(&54401055).unwrap(),
                    MeshNode::try_from_meshcode(&54401150).unwrap(),
                    MeshUnit::Five
                )
                .unwrap()
            );

            // error
            assert!(MeshCell::try_from_meshcode(&54401027, MeshUnit::Five).is_none());
        }

        #[test]
        fn test_try_from_sw_node() {
            assert_eq!(
                MeshCell::try_from_node(
                    MeshNode::try_from_meshcode(&54401027).unwrap(),
                    MeshUnit::One
                )
                .unwrap(),
                MeshCell::try_new(
                    MeshNode::try_from_meshcode(&54401027).unwrap(),
                    MeshNode::try_from_meshcode(&54401028).unwrap(),
                    MeshNode::try_from_meshcode(&54401037).unwrap(),
                    MeshNode::try_from_meshcode(&54401038).unwrap(),
                    MeshUnit::One
                )
                .unwrap()
            );
            assert_eq!(
                MeshCell::try_from_node(
                    MeshNode::try_from_meshcode(&54401005).unwrap(),
                    MeshUnit::Five
                )
                .unwrap(),
                MeshCell::try_new(
                    MeshNode::try_from_meshcode(&54401005).unwrap(),
                    MeshNode::try_from_meshcode(&54401100).unwrap(),
                    MeshNode::try_from_meshcode(&54401055).unwrap(),
                    MeshNode::try_from_meshcode(&54401150).unwrap(),
                    MeshUnit::Five
                )
                .unwrap()
            );

            // error
            assert!(MeshCell::try_from_node(
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshUnit::Five
            )
            .is_none());
        }

        #[test]
        fn test_try_from_point() {
            let point = Point::new(36.10377479, 140.087855041, 10.0);

            assert_eq!(
                MeshCell::try_from_point(&point, MeshUnit::One).unwrap(),
                MeshCell::try_new(
                    MeshNode::try_from_meshcode(&54401027).unwrap(),
                    MeshNode::try_from_meshcode(&54401028).unwrap(),
                    MeshNode::try_from_meshcode(&54401037).unwrap(),
                    MeshNode::try_from_meshcode(&54401038).unwrap(),
                    MeshUnit::One
                )
                .unwrap()
            );
            assert_eq!(
                MeshCell::try_from_point(&point, MeshUnit::Five).unwrap(),
                MeshCell::try_new(
                    MeshNode::try_from_meshcode(&54401005).unwrap(),
                    MeshNode::try_from_meshcode(&54401100).unwrap(),
                    MeshNode::try_from_meshcode(&54401055).unwrap(),
                    MeshNode::try_from_meshcode(&54401150).unwrap(),
                    MeshUnit::Five
                )
                .unwrap()
            );
        }

        #[test]
        fn test_position() {
            let point = Point::new(36.10377479, 140.087855041, 10.0);

            let cell = MeshCell::try_from_point(&point, MeshUnit::One).unwrap();
            assert_eq!(
                cell.position(&point),
                (0.4529748000001632, 0.028403280000475206)
            );

            let cell = MeshCell::try_from_point(&point, MeshUnit::Five).unwrap();
            assert_eq!(
                cell.position(&point),
                (0.4905949600000099, 0.405680656000186)
            );
        }
    }
}
