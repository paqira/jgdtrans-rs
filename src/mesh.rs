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
use std::str::FromStr;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
#[cfg(feature = "serde")]
use serde_repr::{Deserialize_repr, Serialize_repr};

use crate::error::{
    ErrorAxis, MeshCellErrorKind, MeshCoordErrorKind, MeshNodeErrorKind, ParseMeshCoordErrorKind,
    ParseMeshNodeErrorKind,
};
use crate::{Error, Point, Result};

/// The mesh unit (unit shortly), or approximate length of cell's edge.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(Serialize_repr, Deserialize_repr))]
#[repr(u8)]
pub enum MeshUnit {
    /// for 1 \[km\]
    One = 1,
    /// for 5 \[km\]
    Five = 5,
}

impl From<MeshUnit> for u8 {
    fn from(value: MeshUnit) -> Self {
        (&value).into()
    }
}

impl From<&MeshUnit> for u8 {
    fn from(value: &MeshUnit) -> Self {
        match value {
            MeshUnit::One => 1,
            MeshUnit::Five => 5,
        }
    }
}

impl MeshUnit {
    #[inline]
    fn is_five(&self) -> bool {
        matches!(self, Self::Five)
    }
}

/// Represents mech coordinate, namely, discrete latitude and/or longitude.
///
/// This supports non-negative latitude and/or longitude only.
///
/// This has three digits, _first_, _second_ and _third_.
/// The first takes values from 0 to 99, the second does from 0 to 7
/// and the third does from 0 to 9 inclusive.
///
/// We note that the third digits takes either 0 or 5 only
/// on the mesh with unit [`MeshUnit::Five`].
///
/// # Example
///
/// ```
/// # use jgdtrans::*;
/// # use jgdtrans::mesh::*;
/// # fn main() -> Result<()> {
/// // The selection of MeshCoord depends on unit
/// let coord = MeshCoord::try_from_latitude(&36.103774791666666, &MeshUnit::One)?;
/// assert_eq!(coord, MeshCoord::try_new(54, 1, 2)?);
/// // Every fifth MeshCoord is taken, if unit is MeshUnit::Five
/// let coord = MeshCoord::try_from_latitude(&36.103774791666666, &MeshUnit::Five)?;
/// assert_eq!(coord, MeshCoord::try_new(54, 1, 0)?);
///
/// // Increment/decrement (not inplace)
/// let coord: MeshCoord = (54, 1, 2).try_into()?;
/// assert_eq!(coord.try_next_up(&MeshUnit::One)?, MeshCoord::try_new(54, 1, 3)?);
/// assert_eq!(coord.try_next_down(&MeshUnit::One)?, MeshCoord::try_new(54, 1, 1)?);
/// // Unit must be consistent with MeshCoord,
/// // otherwise it returns Err.
/// assert!(coord.try_next_up(&MeshUnit::Five).is_err());
/// # Ok(())}
/// ```
#[derive(Debug, PartialEq, PartialOrd, Eq, Hash, Ord, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct MeshCoord {
    /// takes 0 to 99 inclusive
    pub(crate) first: u8,
    /// takes 0 to 7 inclusive
    pub(crate) second: u8,
    /// takes 0 to 9 inclusive
    pub(crate) third: u8,
}

impl TryFrom<(u8, u8, u8)> for MeshCoord {
    type Error = Error;
    /// Makes a [`MeshCoord`] from a digits triplet
    fn try_from(value: (u8, u8, u8)) -> Result<Self> {
        Self::try_new(value.0, value.1, value.2)
    }
}

impl MeshCoord {
    #[inline]
    fn is_multiple_5(&self) -> bool {
        matches!(self.third, 0 | 5)
    }
}

impl MeshCoord {
    /// Makes a [`MeshCoord`].
    ///
    /// # Errors
    ///
    /// If one of `first`, `second` and `third` is out-of-range.
    /// `first` takes values from 0 to 99,
    /// `second` does from 0 to 7,
    /// and `third` does from 0 to 9 inclusive.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshCoord;
    /// # fn main() -> Result<()> {
    /// let coord = MeshCoord::try_new(1, 2, 3)?;
    /// assert_eq!(coord.first(), &1);
    /// assert_eq!(coord.second(), &2);
    /// assert_eq!(coord.third(), &3);
    /// # Ok(())}
    /// ```
    pub fn try_new(first: u8, second: u8, third: u8) -> Result<Self> {
        if first.gt(&99) || second.gt(&7) || third.gt(&9) {
            return Err(Error::new_mesh_coord(MeshCoordErrorKind::Overflow));
        };

        Ok(Self {
            first,
            second,
            third,
        })
    }

    /// Returns the first digit of `self` (`0..100`).
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshCoord;
    /// # fn main() -> Result<()> {
    /// let coord = MeshCoord::try_new(1, 2, 3)?;
    /// assert_eq!(coord.first(), &1);
    /// # Ok(())}
    /// ```
    pub fn first(&self) -> &u8 {
        &self.first
    }

    /// Returns the second digit of `self` (`0..8`).
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshCoord;
    /// # fn main() -> Result<()> {
    /// let coord = MeshCoord::try_new(1, 2, 3)?;
    /// assert_eq!(coord.second(), &2);
    /// # Ok(())}
    /// ```
    pub fn second(&self) -> &u8 {
        &self.second
    }

    /// Returns the third digit of `self` (`0..10`).
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshCoord;
    /// # fn main() -> Result<()> {
    /// let coord = MeshCoord::try_new(1, 2, 3)?;
    /// assert_eq!(coord.third(), &3);
    /// # Ok(())}
    /// ```
    pub fn third(&self) -> &u8 {
        &self.third
    }

    fn from_value(value: &f64, unit: &MeshUnit) -> Self {
        debug_assert!(value.ge(&0.) && value.le(&180.));

        let integer = value.floor() as u32;

        let first = integer % 100;
        let second = (8. * value).floor() as u32 - 8 * integer;
        let third = (80. * value).floor() as u32 - 80 * integer - 10 * second;

        // max of integer is 180
        // therefore first, second and third fit u8
        // no error check required
        Self {
            first: first as u8,
            second: second as u8,
            third: match unit {
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

    /// Makes the greatest [`MeshCoord`] less than latitude `v` with `unit`.
    ///
    /// `v` is latitude which satisfies 0.0 <= and <= 66.666...
    ///
    /// # Errors
    ///
    /// If `v` is out-of-range.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn main() -> Result<()> {
    /// let v = 36.103774791666666;
    /// assert_eq!(
    ///     MeshCoord::try_from_latitude(&v, &MeshUnit::One)?,
    ///     MeshCoord::try_new(54, 1, 2)?
    /// );
    /// assert_eq!(
    ///     MeshCoord::try_from_latitude(&v, &MeshUnit::Five)?,
    ///     MeshCoord::try_new(54, 1, 0)?
    /// );
    /// # Ok(())}
    /// ```
    pub fn try_from_latitude(v: &f64, unit: &MeshUnit) -> Result<Self> {
        let value = {
            let value = 3.0 * v / 2.0;

            // Minimum add-hook trick to ensure the identity,
            // 1. MeshCoord::try_from_latitude(&coord.to_latitude(), &MeshUnit::One)
            // 2. MeshCoord::try_from_longitude(&coord.to_longitude(), &MeshUnit::One)
            if (v.to_bits() % 2).eq(&1) {
                value.next_up()
            } else {
                value
            }
        };

        if value.is_nan() {
            return Err(Error::new_parse_mesh_coord(
                ParseMeshCoordErrorKind::NAN,
                ErrorAxis::Latitude,
            ));
        };

        if value.lt(&0.0) || value.ge(&100.0) {
            return Err(Error::new_parse_mesh_coord(
                ParseMeshCoordErrorKind::Overflow,
                ErrorAxis::Latitude,
            ));
        };

        Ok(Self::from_value(&value, unit))
    }

    /// Makes the greatest [`MeshCoord`] less than longitiude `v` with `unit`.
    ///
    /// `v` is longitude which satisfies 100.0 <= and <= 180.0.
    ///
    /// # Errors
    ///
    /// If `v` is out-of-range.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn try_main() -> Result<()> {
    /// let v = 140.08785504166664;
    ///
    /// assert_eq!(
    ///     MeshCoord::try_from_longitude(&v, &MeshUnit::One)?,
    ///     MeshCoord::try_new(40, 0, 7)?
    /// );
    /// assert_eq!(
    ///     MeshCoord::try_from_longitude(&v, &MeshUnit::Five)?,
    ///     MeshCoord::try_new(40, 0, 5)?
    /// );
    /// # Ok(())}
    /// # fn main() {try_main().unwrap()}
    /// ```
    pub fn try_from_longitude(v: &f64, unit: &MeshUnit) -> Result<Self> {
        if v.is_nan() {
            return Err(Error::new_parse_mesh_coord(
                ParseMeshCoordErrorKind::NAN,
                ErrorAxis::Longitude,
            ));
        };

        if v.lt(&100.0) || v.gt(&180.0) {
            return Err(Error::new_parse_mesh_coord(
                ParseMeshCoordErrorKind::Overflow,
                ErrorAxis::Longitude,
            ));
        };

        Ok(Self::from_value(v, unit))
    }

    fn to_value(&self) -> f64 {
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
    /// # fn main() -> Result<()> {
    /// let v = 36.103774791666666;
    ///
    /// // MeshCoord is a component of the greatest node less than `v`
    /// let coord = MeshCoord::try_from_latitude(&v, &MeshUnit::One)?;
    /// assert_eq!(coord.to_latitude(), 36.1);
    ///
    /// let coord = MeshCoord::try_from_latitude(&v, &MeshUnit::Five)?;
    /// assert_eq!(coord.to_latitude(), 36.083333333333336);
    /// # Ok(())}
    /// ```
    pub fn to_latitude(&self) -> f64 {
        2. * self.to_value() / 3.
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
    /// # fn main() -> Result<()> {
    /// let v = 140.08785504166664;
    ///
    /// // MeshCoord is a component of the greatest node less than `v`
    /// let coord = MeshCoord::try_from_longitude(&v, &MeshUnit::One)?;
    /// assert_eq!(coord.to_longitude(), 140.0875);
    ///
    /// let coord = MeshCoord::try_from_longitude(&v, &MeshUnit::Five)?;
    /// assert_eq!(coord.to_longitude(), 140.0625);
    /// # Ok(())}
    /// ```
    pub fn to_longitude(&self) -> f64 {
        100. + self.to_value()
    }

    /// Returns the smallest [`MeshCoord`] greater than `self`.
    ///
    /// # Errors
    ///
    /// If `unit` is [`MeshUnit::Five`] although `self.third` is either `0` or `5`,
    /// or `self` is `MeshCoord { first: 99, second: 7, third: 9 }`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn main() -> Result<()> {
    /// let corrd = MeshCoord::try_new(0, 0, 0)?;
    /// assert_eq!(corrd.try_next_up(&MeshUnit::One)?, MeshCoord::try_new(0, 0, 1)?);
    /// assert_eq!(corrd.try_next_up(&MeshUnit::Five)?, MeshCoord::try_new(0, 0, 5)?);
    /// # Ok(())}
    /// ```
    pub fn try_next_up(&self, unit: &MeshUnit) -> Result<Self> {
        if unit.is_five() && !self.is_multiple_5() {
            return Err(Error::new_mesh_coord(MeshCoordErrorKind::MeshUnit));
        }

        let mesh_unit: u8 = unit.into();
        // 9 for MeshUnit::One and 5 for MeshUnit::Five
        let bound = 10 - mesh_unit;

        if self.third.eq(&bound) {
            if self.second.eq(&7) {
                if self.first.eq(&99) {
                    Err(Error::new_mesh_coord(MeshCoordErrorKind::PosOverflow))
                } else {
                    // `first` is not 99
                    Ok(Self {
                        first: self.first + 1,
                        second: 0,
                        third: 0,
                    })
                }
            } else {
                // `second` is not 7
                Ok(Self {
                    first: self.first,
                    second: self.second + 1,
                    third: 0,
                })
            }
        } else {
            // `third` is not 1 nor 5
            Ok(Self {
                first: self.first,
                second: self.second,
                third: self.third + mesh_unit,
            })
        }
    }

    /// Returns the greatest [`MeshCoord`] less than `self`.
    ///
    /// # Errors
    ///
    /// If `unit` is [`MeshUnit::Five`] although `self.third` is either `0` or `5`,
    /// or `self` is `MeshCoord { first: 0, second: 0, third: 0 }`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn main() -> Result<()> {
    /// assert_eq!(
    ///     MeshCoord::try_new(0, 0, 1)?.try_next_down(&MeshUnit::One)?,
    ///     MeshCoord::try_new(0, 0, 0)?
    /// );
    /// assert_eq!(
    ///     MeshCoord::try_new(0, 0, 5)?.try_next_down(&MeshUnit::Five)?,
    ///     MeshCoord::try_new(0, 0, 0)?
    /// );
    /// # Ok(())}
    /// ```
    pub fn try_next_down(&self, unit: &MeshUnit) -> Result<Self> {
        if unit.is_five() && !self.is_multiple_5() {
            return Err(Error::new_mesh_coord(MeshCoordErrorKind::MeshUnit));
        }

        let mesh_unit: u8 = unit.into();
        // 9 for MeshUnit::One and 5 for MeshUnit::Five
        let bound = 10 - mesh_unit;

        if self.third.eq(&0) {
            if self.second.eq(&0) {
                if self.first.eq(&0) {
                    Err(Error::new_mesh_coord(MeshCoordErrorKind::NegOverflow))
                } else {
                    // `first` is not 0
                    Ok(Self {
                        first: self.first - 1,
                        second: 7,
                        third: bound,
                    })
                }
            } else {
                // `second` is not 0
                Ok(Self {
                    first: self.first,
                    second: self.second - 1,
                    third: bound,
                })
            }
        } else {
            // `third` is not 0
            Ok(Self {
                first: self.first,
                second: self.second,
                third: self.third - mesh_unit,
            })
        }
    }
}

/// Represents mesh node (node shortly), a pair of [`MeshCoord`]s.
///
/// We note that this supports non-negative latitude and longitude only.
///
/// # Example
///
/// ```
/// # use jgdtrans::*;
/// # use jgdtrans::mesh::*;
/// # fn main() -> Result<()> {
/// // Construct from latitude and longitude, altitude ignores
/// let point = Point::try_new(36.10377479, 140.087855041, 0.0)?;
/// let node = MeshNode::try_from_point(&point, &MeshUnit::One)?;
/// assert_eq!(node.to_meshcode(), 54401027);
/// // The result depends on the selection of the mesh unit
/// let node = MeshNode::try_from_point(&point, &MeshUnit::Five)?;
/// assert_eq!(node.to_meshcode(), 54401005);
///
/// // Construct from meshcode
/// let node: MeshNode = 54401027.try_into()?;
/// // The position where the MeshNode locates
/// assert_eq!(node.to_point(), Point::try_new(36.1, 140.0875, 0.0)?);
/// # Ok(())}
/// ```
#[derive(Debug, PartialEq, PartialOrd, Eq, Hash, Ord, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct MeshNode {
    /// The mesh coord of latitude
    pub(crate) latitude: MeshCoord,
    /// The mesh coord of longitude
    ///
    /// This must satisfy `MeshCoord {first: 0, second: 0, third: 0}` <= and <= `MeshCoord {first: 80, second: 0, third: 0}`
    pub(crate) longitude: MeshCoord,
}

impl TryFrom<((u8, u8, u8), (u8, u8, u8))> for MeshNode {
    type Error = Error;

    /// Makes a [`MeshNode`] from a doublet of digits triplets
    fn try_from(value: ((u8, u8, u8), (u8, u8, u8))) -> Result<Self> {
        let latitude: MeshCoord = value.0.try_into()?;
        let longitude: MeshCoord = value.1.try_into()?;
        let node = Self::try_new(latitude, longitude)?;

        Ok(node)
    }
}

impl TryFrom<(MeshCoord, MeshCoord)> for MeshNode {
    type Error = Error;

    /// Makes a [`MeshNode`] from a [`MeshCoord`] doublet
    fn try_from(value: (MeshCoord, MeshCoord)) -> Result<Self> {
        Self::try_new(value.0, value.1)
    }
}

impl TryFrom<u32> for MeshNode {
    type Error = Error;

    /// Makes a [`MeshNode`] from a meshcode
    fn try_from(value: u32) -> Result<Self> {
        Self::try_from_meshcode(&value)
    }
}

impl FromStr for MeshNode {
    type Err = Error;

    /// Makes a [`MeshNode`] from a meshcode
    fn from_str(s: &str) -> Result<Self> {
        let i = s
            .parse::<u32>()
            .map_err(|err| Error::new_parse_mesh_node(ParseMeshNodeErrorKind::Parse(err)))?;
        Self::try_from_meshcode(&i)
    }
}

impl From<MeshNode> for u32 {
    /// Makes a meshcode of [`MeshNode`]
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
    /// If `longitude` is out-of-range.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn main() -> Result<()> {
    /// let latitude = MeshCoord::try_new(54, 1, 2)?;
    /// let longitude = MeshCoord::try_new(40, 0, 7)?;
    ///
    /// let node = MeshNode::try_new(latitude.clone(), longitude.clone())?;
    /// assert_eq!(node.latitude(), &latitude);
    /// assert_eq!(node.longitude(), &longitude);
    /// # Ok(())}
    /// ```
    pub fn try_new(latitude: MeshCoord, longitude: MeshCoord) -> Result<Self> {
        if longitude.gt(&MeshCoord {
            first: 80,
            second: 0,
            third: 0,
        }) {
            return Err(Error::new_mesh_node(MeshNodeErrorKind::Overflow));
        };

        Ok(Self {
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
    /// # fn main() -> Result<()> {
    /// let latitude = MeshCoord::try_new(54, 1, 2)?;
    /// let longitude = MeshCoord::try_new(40, 0, 7)?;
    ///
    /// let node = MeshNode::try_new(latitude.clone(), longitude)?;
    /// assert_eq!(node.latitude(), &latitude);
    /// # Ok(())}
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
    /// # fn main() -> Result<()> {
    /// let latitude = MeshCoord::try_new(54, 1, 2)?;
    /// let longitude = MeshCoord::try_new(40, 0, 7)?;
    ///
    /// let node = MeshNode::try_new(latitude, longitude.clone())?;
    /// assert_eq!(node.longitude(), &longitude);
    /// # Ok(())}
    /// ```
    pub fn longitude(&self) -> &MeshCoord {
        &self.longitude
    }

    /// Makes the nearest north-west [`MeshNode`] of `point`.
    ///
    /// This does not depends on [`point.altitude`](Point::altitude).
    ///
    /// # Errors
    ///
    /// If [`point.latitude`](Point::longitude) and/or [`point.longitude`](Point::longitude)
    /// is negative.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn main() -> Result<()> {
    /// let point = Point::try_new(36.10377479, 140.087855041, 0.0)?;
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
    /// # Ok(())}
    /// ```
    pub fn try_from_point(point: &Point, unit: &MeshUnit) -> Result<Self> {
        let latitude = MeshCoord::try_from_latitude(&point.latitude, unit).map_err(|err| {
            Error::new_parse_mesh_node(ParseMeshNodeErrorKind::Overflow(Some(err)))
        })?;
        let longitude = MeshCoord::try_from_longitude(&point.longitude, unit).map_err(|err| {
            Error::new_parse_mesh_node(ParseMeshNodeErrorKind::Overflow(Some(err)))
        })?;

        Ok(Self {
            latitude,
            longitude,
        })
    }

    /// Makes a [`MeshNode`] represented by meshcode `code`.
    ///
    /// This is inverse of [`MeshNode::to_meshcode()`].
    ///
    /// # Errors
    ///
    /// If `code` is invalid.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn main() -> Result<()> {
    /// assert_eq!(
    ///     MeshNode::try_from_meshcode(&54401027)?,
    ///     MeshNode::try_new(
    ///         MeshCoord::try_new(54, 1, 2)?,
    ///         MeshCoord::try_new(40, 0, 7)?
    ///     )?
    /// );
    /// # Ok(())}
    /// ```
    pub fn try_from_meshcode(meshcode: &u32) -> Result<Self> {
        if meshcode.gt(&99_99_99_99) {
            return Err(Error::new_parse_mesh_node(
                ParseMeshNodeErrorKind::Overflow(None),
            ));
        }

        macro_rules! div_rem {
            ($n:ident, $m:literal) => {
                ($n / $m, $n % $m)
            };
        }

        // code <= 99_99_9_9_9_9
        // lat_first, lng_first <= 99
        let (lat_first, rest) = div_rem!(meshcode, 1_000_000_u32);
        let (lng_first, rest) = div_rem!(rest, 10_000_u32);

        // lat_second, lng_second <= 9
        let (lat_second, rest) = div_rem!(rest, 1000_u32);
        let (lng_second, rest) = div_rem!(rest, 100_u32);

        // lat_third, lng_third <= 9
        let (lat_third, lng_third) = div_rem!(rest, 10_u32);

        let latitude = MeshCoord::try_new(lat_first as u8, lat_second as u8, lat_third as u8)
            .map_err(|err| {
                Error::new_parse_mesh_node(ParseMeshNodeErrorKind::Overflow(Some(err)))
            })?;
        let longitude = MeshCoord::try_new(lng_first as u8, lng_second as u8, lng_third as u8)
            .map_err(|err| {
                Error::new_parse_mesh_node(ParseMeshNodeErrorKind::Overflow(Some(err)))
            })?;

        Self::try_new(latitude, longitude)
            .map_err(|err| Error::new_parse_mesh_node(ParseMeshNodeErrorKind::Overflow(Some(err))))
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
    /// # fn main() -> Result<()> {
    /// let node = MeshNode::try_new(
    ///     MeshCoord::try_new(54, 1, 2)?,
    ///     MeshCoord::try_new(40, 0, 7)?
    /// )?;
    ///
    /// assert_eq!(node.to_meshcode(), 54401027);
    /// # Ok(())}
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
    /// ```rust
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn main() -> Result<()> {
    /// let node = MeshNode::try_new(
    ///     MeshCoord::try_new(54, 1, 2)?,
    ///     MeshCoord::try_new(40, 0, 7)?
    /// )?;
    ///
    /// assert_eq!(node.to_point(), Point::try_new(36.1, 140.0875, 0.0)?);
    /// # Ok(())}
    /// ```
    pub fn to_point(&self) -> Point {
        Point::new(
            self.latitude.to_latitude(),
            self.longitude.to_longitude(),
            0.0,
        )
    }
}

/// Represents unit mesh cell (mesh cell or cell shortly), a quadruplet of [`MeshNode`]s (and [`MeshUnit`]).
///
/// This has no other [`MeshNode`]s inside `self` in the unit.
///
/// The cell is, roughly, a square with `unit` \[km\] length edges.
///
/// # Example
///
/// ```
/// # use jgdtrans::*;
/// # use jgdtrans::mesh::*;
/// # fn main() -> Result<()> {
/// // Construct from latitude and longitude, altitude ignores
/// // (The result depends on the selection of the mesh unit)
/// let point = Point::try_new(36.10377479, 140.087855041, 0.0)?;
/// let cell = MeshCell::try_from_point(&point, MeshUnit::One)?;
/// assert_eq!(cell.sw(), &MeshNode::try_from_meshcode(&54401027)?);
/// assert_eq!(cell.se(), &MeshNode::try_from_meshcode(&54401028)?);
/// assert_eq!(cell.nw(), &MeshNode::try_from_meshcode(&54401037)?);
/// assert_eq!(cell.ne(), &MeshNode::try_from_meshcode(&54401038)?);
///
/// // Construct from node
/// let node: MeshNode = 54401027.try_into()?;
/// assert_eq!(MeshCell::try_from_sw_node(node, MeshUnit::One)?, cell);
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
/// let (latitude, longitude) = cell.position(&cell.sw().to_point());
/// assert!((0.0 - latitude).abs() < 1e-12);
/// assert!((0.0 - longitude).abs() < 1e-12);
/// // the north-east node is (1, 1)
/// let (latitude, longitude) = cell.position(&cell.ne().to_point());
/// assert!((1.0 - latitude).abs() < 1e-12);
/// assert!((1.0 - longitude).abs() < 1e-12);
/// # Ok(())}
/// ```
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct MeshCell {
    /// The south-west node of the cell
    pub(crate) sw: MeshNode,
    /// The south-east node of the cell
    pub(crate) se: MeshNode,
    /// The north-west node of the cell
    pub(crate) nw: MeshNode,
    /// The north-east node of the cell
    pub(crate) ne: MeshNode,
    /// The mesh unit which is consistent with nodes
    pub(crate) unit: MeshUnit,
}

impl MeshCell {
    /// Makes a [`MeshCell`].
    ///
    /// # Errors
    ///
    /// If `unit` is inconsistent with nodes,
    /// or the nodes does not construct a unit mesh cell
    /// with `unit`.
    ///
    ///
    /// # Example
    ///
    /// ```rust
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn main() -> Result<()> {
    /// let sw = MeshNode::try_from_meshcode(&54401027)?;
    /// let se = MeshNode::try_from_meshcode(&54401028)?;
    /// let nw = MeshNode::try_from_meshcode(&54401037)?;
    /// let ne = MeshNode::try_from_meshcode(&54401038)?;
    /// let cell = MeshCell::try_new(sw.clone(), se.clone(), nw.clone(), ne.clone(), MeshUnit::One)?;
    ///
    /// assert_eq!(cell.sw(), &sw);
    /// assert_eq!(cell.se(), &se);
    /// assert_eq!(cell.nw(), &nw);
    /// assert_eq!(cell.ne(), &ne);
    /// assert_eq!(cell.unit(), &MeshUnit::One);
    /// # Ok(())}
    /// ```
    pub fn try_new(
        sw: MeshNode,
        se: MeshNode,
        nw: MeshNode,
        ne: MeshNode,
        unit: MeshUnit,
    ) -> Result<Self> {
        // consistentcy on unit v.s. the third
        macro_rules! is_unit_five {
            ($coord:expr) => {
                !$coord.latitude.is_multiple_5() || !$coord.longitude.is_multiple_5()
            };
        }

        if unit.is_five()
            && (is_unit_five!(sw) || is_unit_five!(se) || is_unit_five!(nw) || is_unit_five!(ne))
        {
            return Err(Error::new_mesh_cell(MeshCellErrorKind::MeshUnit));
        };

        let lat_next = sw
            .latitude
            .try_next_up(&unit)
            .map_err(|_| Error::new_mesh_cell(MeshCellErrorKind::Overflow))?;
        let lng_next = sw
            .longitude
            .try_next_up(&unit)
            .map_err(|_| Error::new_mesh_cell(MeshCellErrorKind::Overflow))?;

        if lat_next.ne(&nw.latitude) || sw.longitude.ne(&nw.longitude) {
            return Err(Error::new_mesh_cell(MeshCellErrorKind::NortthWestNode));
        }
        if sw.latitude.ne(&se.latitude) || lng_next.ne(&se.longitude) {
            return Err(Error::new_mesh_cell(MeshCellErrorKind::SouthEastNode));
        }
        if lat_next.ne(&ne.latitude) || lng_next.ne(&ne.longitude) {
            return Err(Error::new_mesh_cell(MeshCellErrorKind::NouthEastNode));
        }

        Ok(Self {
            sw,
            se,
            nw,
            ne,
            unit,
        })
    }

    /// Returns the south-west node of `self`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn main() -> Result<()> {
    /// let sw = MeshNode::try_from_meshcode(&54401027)?;
    /// let se = MeshNode::try_from_meshcode(&54401028)?;
    /// let nw = MeshNode::try_from_meshcode(&54401037)?;
    /// let ne = MeshNode::try_from_meshcode(&54401038)?;
    /// let cell = MeshCell::try_new(sw.clone(), se, nw, ne, MeshUnit::One)?;
    ///
    /// assert_eq!(cell.sw(), &sw);
    /// # Ok(())}
    /// ```
    pub fn sw(&self) -> &MeshNode {
        &self.sw
    }

    /// Returns the south-east node of `self`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn main() -> Result<()> {
    /// let sw = MeshNode::try_from_meshcode(&54401027)?;
    /// let se = MeshNode::try_from_meshcode(&54401028)?;
    /// let nw = MeshNode::try_from_meshcode(&54401037)?;
    /// let ne = MeshNode::try_from_meshcode(&54401038)?;
    /// let cell = MeshCell::try_new(sw, se.clone(), nw, ne, MeshUnit::One)?;
    ///
    /// assert_eq!(cell.se(), &se);
    /// # Ok(())}
    /// ```
    pub fn se(&self) -> &MeshNode {
        &self.se
    }

    /// Returns the north-west node of `self`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn main() -> Result<()> {
    /// let sw = MeshNode::try_from_meshcode(&54401027)?;
    /// let se = MeshNode::try_from_meshcode(&54401028)?;
    /// let nw = MeshNode::try_from_meshcode(&54401037)?;
    /// let ne = MeshNode::try_from_meshcode(&54401038)?;
    /// let cell = MeshCell::try_new(sw, se, nw.clone(), ne, MeshUnit::One)?;
    ///
    /// assert_eq!(cell.nw(), &nw);
    /// # Ok(())}
    /// ```
    pub fn nw(&self) -> &MeshNode {
        &self.nw
    }

    /// Returns the north-east node of `self`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn main() -> Result<()> {
    /// let sw = MeshNode::try_from_meshcode(&54401027)?;
    /// let se = MeshNode::try_from_meshcode(&54401028)?;
    /// let nw = MeshNode::try_from_meshcode(&54401037)?;
    /// let ne = MeshNode::try_from_meshcode(&54401038)?;
    /// let cell = MeshCell::try_new(sw, se, nw, ne.clone(), MeshUnit::One)?;
    ///
    /// assert_eq!(cell.ne(), &ne);
    /// # Ok(())}
    /// ```
    pub fn ne(&self) -> &MeshNode {
        &self.ne
    }

    /// Returns the unit of `self`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn main() -> Result<()> {
    /// let sw = MeshNode::try_from_meshcode(&54401027)?;
    /// let se = MeshNode::try_from_meshcode(&54401028)?;
    /// let nw = MeshNode::try_from_meshcode(&54401037)?;
    /// let ne = MeshNode::try_from_meshcode(&54401038)?;
    /// let cell = MeshCell::try_new(sw, se, nw, ne, MeshUnit::One)?;
    ///
    /// assert_eq!(cell.unit(), &MeshUnit::One);
    /// # Ok(())}
    /// ```
    pub fn unit(&self) -> &MeshUnit {
        &self.unit
    }

    /// Makes a [`MeshCell`] with the south-east [`MeshNode`] which represented by meshcode `code`.
    ///
    /// # Errors
    ///
    /// If the meshcode `code` is invalid,
    /// `unit` is inconsistent with meshcode,
    /// or one of nodes constructing the cell is out-of-range.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn main() -> Result<()> {
    /// assert_eq!(
    ///     MeshCell::try_from_meshcode(&54401027, MeshUnit::One)?,
    ///     MeshCell::try_new(
    ///         // sw
    ///         MeshNode::try_from_meshcode(&54401027)?,
    ///         // se
    ///         MeshNode::try_from_meshcode(&54401028)?,
    ///         // nw
    ///         MeshNode::try_from_meshcode(&54401037)?,
    ///         // ne
    ///         MeshNode::try_from_meshcode(&54401038)?,
    ///         // unit
    ///         MeshUnit::One
    ///     )?
    /// );
    /// # Ok(())}
    /// ```
    pub fn try_from_meshcode(meshcode: &u32, unit: MeshUnit) -> Result<Self> {
        let sw = MeshNode::try_from_meshcode(meshcode).map_err(Error::new_parse_mesh_cell)?;
        Self::try_from_sw_node(sw, unit).map_err(Error::new_parse_mesh_cell)
    }

    /// Makes a [`MeshCell`] that has `node` as a south-west node.
    ///
    /// # Errors
    ///
    /// If `unit` is inconsistent with `node`,
    /// or one of nodes constructing the cell is out-of-range.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn main() -> Result<()> {
    /// let code = 54401027;
    /// let node = MeshNode::try_from_meshcode(&54401027)?;
    ///
    /// assert_eq!(
    ///     MeshCell::try_from_sw_node(node, MeshUnit::One)?,
    ///     MeshCell::try_from_meshcode(&54401027, MeshUnit::One)?
    /// );
    /// # Ok(())}
    /// ```
    pub fn try_from_sw_node(node: MeshNode, unit: MeshUnit) -> Result<Self> {
        let next_lat_coord = node
            .latitude
            .try_next_up(&unit)
            .map_err(Error::new_parse_mesh_cell)?;
        let next_lng_coord = node
            .longitude
            .try_next_up(&unit)
            .map_err(Error::new_parse_mesh_cell)?;

        // Call MeshNode::try_new
        // to check next_coord_lat
        let se = MeshNode::try_new(node.latitude.clone(), next_lng_coord.clone())
            .map_err(Error::new_parse_mesh_cell)?;
        let nw = MeshNode::try_new(next_lat_coord.clone(), node.longitude.clone())
            .map_err(Error::new_parse_mesh_cell)?;
        let ne = MeshNode::try_new(next_lat_coord, next_lng_coord)
            .map_err(Error::new_parse_mesh_cell)?;

        Ok(Self {
            sw: node,
            se,
            nw,
            ne,
            unit,
        })
    }

    /// Makes a [`MeshCell`] which contains a [`Point`].
    ///
    /// The result does not depends on [`point.altitude`](Point::altitude).
    ///
    /// # Errors
    ///
    /// If [`point.latitude`](Point::latitude) and/or [`point.longitude`](Point::longitude)
    /// is negative,
    /// or one of nodes constructing the cell is out-of-range.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn main() -> Result<()> {
    /// let point: Point = Point::try_new(36.10377479, 140.087855041, 0.0)?;
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
    /// # Ok(())}
    /// ```
    pub fn try_from_point(point: &Point, unit: MeshUnit) -> Result<Self> {
        let node = MeshNode::try_from_point(point, &unit).map_err(Error::new_parse_mesh_cell)?;
        Self::try_from_sw_node(node, unit).map_err(Error::new_parse_mesh_cell)
    }

    /// Return the position in the cell.
    ///
    /// This returns from 0.0 to 1.0 for each latitude and longitude
    /// if `point` is inside of `self`.
    ///
    /// We note that the result is a (latitude, longitude) pair,
    /// not a (right-handed) (y, x) pair.
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn main() -> Result<()> {
    /// // sample latitude and longitude
    /// let point = Point::try_new(36.10377479, 140.087855041, 0.0)?;
    ///
    /// let cell = MeshCell::try_from_point(&point, MeshUnit::One)?;
    /// // the south-west of the cell is (0, 0), origin
    /// let (latitude, longitude) = cell.position(&cell.sw().to_point());
    /// assert!((0.0 - latitude).abs() < 1e-12);
    /// assert!((0.0 - longitude).abs() < 1e-12);
    /// // the south-east is (0, 1)
    /// let (latitude, longitude) = cell.position(&cell.se().to_point());
    /// assert!((0.0 - latitude).abs() < 1e-12);
    /// assert!((1.0 - longitude).abs() < 1e-12);
    /// // the north-west is (1, 0)
    /// let (latitude, longitude) = cell.position(&cell.nw().to_point());
    /// assert!((1.0 - latitude).abs() < 1e-12);
    /// assert!((0.0 - longitude).abs() < 1e-12);
    /// // the north-east is (1, 1)
    /// let (latitude, longitude) = cell.position(&cell.ne().to_point());
    /// assert!((1.0 - latitude).abs() < 1e-12);
    /// assert!((1.0 - longitude).abs() < 1e-12);
    /// # Ok(())}
    /// ```
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::*;
    /// # fn main() -> Result<()> {
    /// let point = Point::try_new(36.10377479, 140.087855041, 0.0)?;
    ///
    /// let cell = MeshCell::try_from_point(&point, MeshUnit::One)?;
    /// assert_eq!(
    ///     cell.position(&point),
    ///     (0.4529748000001632, 0.028403280000475206)
    /// );
    ///
    /// // the reuslt depends on unit
    /// let cell = MeshCell::try_from_point(&point, MeshUnit::Five)?;
    /// assert_eq!(
    ///     cell.position(&point),
    ///     (0.4905949600000099, 0.405680656000186)
    /// );
    /// # Ok(())}
    /// ```
    pub fn position(&self, point: &Point) -> (f64, f64) {
        let lat = point.latitude - self.sw.latitude.to_latitude();
        let lng = point.longitude - self.sw.longitude.to_longitude();

        // The cell stretches 1.5 times in the latitude direction
        // compared to the longitude direction,
        // then here uses 120 = 1.5 * 80.
        match self.unit {
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
            assert!(MeshCoord::try_new(100, 0, 0).is_err());
            assert!(MeshCoord::try_new(99, 8, 0).is_err());
            assert!(MeshCoord::try_new(99, 7, 10).is_err());
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
            assert!(MeshCoord::try_from_latitude(&f64::NAN, &MeshUnit::One).is_err());
            assert!(MeshCoord::try_from_latitude(&0.0f64.next_down(), &MeshUnit::One).is_err());
            assert!(MeshCoord::try_from_latitude(&66.666666666666666666, &MeshUnit::One).is_err());

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
            assert!(MeshCoord::try_from_longitude(&f64::NAN, &MeshUnit::One).is_err());
            assert!(MeshCoord::try_from_longitude(&100.0f64.next_down(), &MeshUnit::One).is_err());
            assert!(MeshCoord::try_from_longitude(&180.0f64.next_up(), &MeshUnit::One).is_err());

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
                .is_err());
            assert!(MeshCoord::try_new(99, 7, 9)
                .unwrap()
                .try_next_up(&MeshUnit::One)
                .is_err());
            assert!(MeshCoord::try_new(99, 7, 5)
                .unwrap()
                .try_next_up(&MeshUnit::Five)
                .is_err());

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
                .is_err());
            assert!(MeshCoord::try_new(0, 0, 0)
                .unwrap()
                .try_next_down(&MeshUnit::One)
                .is_err());

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
                assert!(temp.is_ok());
                coord = coord.try_next_up(&MeshUnit::One).unwrap();
            }

            while coord.lt(&MeshCoord::try_new(99, 7, 9).unwrap()) {
                let temp = MeshNode::try_new(MeshCoord::try_new(0, 0, 0).unwrap(), coord.clone());
                assert!(temp.is_err());
                coord = coord.try_next_up(&MeshUnit::One).unwrap();
            }
            assert!(MeshNode::try_new(MeshCoord::try_new(0, 0, 0).unwrap(), coord,).is_err());
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
            let point = Point::try_new(36.103774791666666, 140.08785504166664, 10.0).unwrap();

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
            assert!(MeshNode::try_from_meshcode(&54401827).is_err());
            assert!(MeshNode::try_from_meshcode(&54408027).is_err());
            assert!(MeshNode::try_from_meshcode(&54801021).is_err());
            assert!(MeshNode::try_from_meshcode(&54801120).is_err());
            assert!(MeshNode::try_from_meshcode(&54811020).is_err());
            assert!(MeshNode::try_from_meshcode(&100000000).is_err());

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
                Point::try_new(36.1, 140.0875, 0.0).unwrap()
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
            // longtitude
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
            .is_ok());
            assert!(MeshCell::try_new(
                MeshNode::try_from_meshcode(&54401005).unwrap(),
                MeshNode::try_from_meshcode(&54401100).unwrap(),
                MeshNode::try_from_meshcode(&54401055).unwrap(),
                MeshNode::try_from_meshcode(&54401150).unwrap(),
                MeshUnit::Five
            )
            .is_ok());

            // error
            // incorrect unit
            assert!(MeshCell::try_new(
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshNode::try_from_meshcode(&54401028).unwrap(),
                MeshNode::try_from_meshcode(&54401037).unwrap(),
                MeshNode::try_from_meshcode(&54401038).unwrap(),
                MeshUnit::Five
            )
            .is_err());
            assert!(MeshCell::try_new(
                MeshNode::try_from_meshcode(&54401005).unwrap(),
                MeshNode::try_from_meshcode(&54401100).unwrap(),
                MeshNode::try_from_meshcode(&54401055).unwrap(),
                MeshNode::try_from_meshcode(&54401150).unwrap(),
                MeshUnit::One
            )
            .is_err());

            // not a unit cell
            // longitude
            assert!(MeshCell::try_new(
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshNode::try_from_meshcode(&54401037).unwrap(),
                MeshNode::try_from_meshcode(&54401038).unwrap(),
                MeshUnit::One
            )
            .is_err());
            assert!(MeshCell::try_new(
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshNode::try_from_meshcode(&54401028).unwrap(),
                MeshNode::try_from_meshcode(&54401036).unwrap(),
                MeshNode::try_from_meshcode(&54401038).unwrap(),
                MeshUnit::One
            )
            .is_err());
            assert!(MeshCell::try_new(
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshNode::try_from_meshcode(&54401028).unwrap(),
                MeshNode::try_from_meshcode(&54401037).unwrap(),
                MeshNode::try_from_meshcode(&54401037).unwrap(),
                MeshUnit::One
            )
            .is_err());

            // latitude
            assert!(MeshCell::try_new(
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshNode::try_from_meshcode(&54401018).unwrap(),
                MeshNode::try_from_meshcode(&54401037).unwrap(),
                MeshNode::try_from_meshcode(&54401038).unwrap(),
                MeshUnit::One
            )
            .is_err());
            assert!(MeshCell::try_new(
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshNode::try_from_meshcode(&54401028).unwrap(),
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshNode::try_from_meshcode(&54401038).unwrap(),
                MeshUnit::One
            )
            .is_err());
            assert!(MeshCell::try_new(
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshNode::try_from_meshcode(&54401028).unwrap(),
                MeshNode::try_from_meshcode(&54401037).unwrap(),
                MeshNode::try_from_meshcode(&54401028).unwrap(),
                MeshUnit::One
            )
            .is_err());
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

            assert_eq!(cell.sw(), &MeshNode::try_from_meshcode(&54401027).unwrap());
            assert_eq!(cell.se(), &MeshNode::try_from_meshcode(&54401028).unwrap());
            assert_eq!(cell.nw(), &MeshNode::try_from_meshcode(&54401037).unwrap());
            assert_eq!(cell.ne(), &MeshNode::try_from_meshcode(&54401038).unwrap());
            assert_eq!(cell.unit(), &MeshUnit::One);
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
            assert!(MeshCell::try_from_meshcode(&54401027, MeshUnit::Five).is_err());
        }

        #[test]
        fn test_try_from_sw_node() {
            assert_eq!(
                MeshCell::try_from_sw_node(
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
                MeshCell::try_from_sw_node(
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
            assert!(MeshCell::try_from_sw_node(
                MeshNode::try_from_meshcode(&54401027).unwrap(),
                MeshUnit::Five
            )
            .is_err());
        }

        #[test]
        fn test_try_from_point() {
            let point = Point::try_new(36.10377479, 140.087855041, 10.0).unwrap();

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
            let point = Point::try_new(36.10377479, 140.087855041, 10.0).unwrap();

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
