use std::ops::{Add, Sub};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::{
    error::{self, Error, Result},
    mesh::{MeshCell, MeshNode, MeshUnit},
    transformer::Correction,
    utils,
};

/// Represents a position on the Earth, a triplet latitude, longitude and altitude.
///
/// Latitude takes values from -90.0 to 90.0,
/// and longitude does from -180.0 to 180.0.
///
/// # Example
///
/// ```
/// # use jgdtrans::*;
/// # use jgdtrans::transformer::Correction;
/// # fn main() -> Result<()> {
/// // Construct
/// let point = Point::try_new(35.0, 145.0, 5.0)?;
/// assert_eq!(point.latitude(), &35.0);
/// assert_eq!(point.longitude(), &145.0);
/// assert_eq!(point.altitude(), &5.0);
///
/// // Construct with "rounding" angles
/// let point = Point::new(145.0, -215.0, 5.0);
/// assert_eq!(point.latitude(), &35.0);
/// assert_eq!(point.longitude(), &145.0);
/// assert_eq!(point.altitude(), &5.0);
///
/// // Add/sub Correction
/// let result = point + Correction::new(1.0, 1.0, 1.0);
/// assert_eq!(result, Point::try_new(36.0, 146.0, 6.0)?);
/// let result = result - Correction::new(1.0, 1.0, 1.0);
/// assert_eq!(result, point);
/// # Ok(())}
/// ```
#[derive(Debug, PartialEq, Copy, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Point {
    /// The latitude \[deg\] of the point which satisfies -90.0 <= and <= 90.0.
    pub(crate) latitude: f64,
    /// The longitude \[deg\] of the point which satisfies -180.0 <= and <= 180.0.
    pub(crate) longitude: f64,
    /// The altitude \[m\] of the point.
    pub(crate) altitude: f64,
}

impl From<(f64, f64)> for Point {
    /// see [`Point::new()`], defaulting 0.0 for altitude
    fn from(rhs: (f64, f64)) -> Self {
        Self::new(rhs.0, rhs.1, 0.0)
    }
}

impl From<(f64, f64, f64)> for Point {
    /// see [`Point::new()`]
    fn from(rhs: (f64, f64, f64)) -> Self {
        Self::new(rhs.0, rhs.1, rhs.2)
    }
}

impl From<MeshNode> for Point {
    /// see [`Point::from_node()`]
    fn from(value: MeshNode) -> Self {
        Self::from_node(&value)
    }
}

impl TryFrom<u32> for Point {
    type Error = Error;

    /// see [`Point::try_from_meshcode()`]
    fn try_from(value: u32) -> Result<Self> {
        Self::try_from_meshcode(&value)
    }
}

impl Add<Correction> for Point {
    type Output = Point;

    fn add(self, rhs: Correction) -> Self::Output {
        Self::new(
            self.latitude + rhs.latitude,
            self.longitude + rhs.longitude,
            self.altitude + rhs.altitude,
        )
    }
}

impl Sub<Correction> for Point {
    type Output = Point;

    fn sub(self, rhs: Correction) -> Self::Output {
        Self::new(
            self.latitude - rhs.latitude,
            self.longitude - rhs.longitude,
            self.altitude - rhs.altitude,
        )
    }
}

impl Point {
    /// Makes a [`Point`] with "rounding".
    ///
    /// This "rounds" `latitude` into -90.0 <= and <= 90.0
    /// and does `longitude` into -180.0 <= and <= 180.0.
    /// "Rounding" may be interesting (the Earth is round).
    ///
    /// We note that `latitude` and `longitude` is DD notation,
    /// use [`utils::DMS`] ([`utils::to_dms`] and [`utils::from_dms`]) for converting to/from DMS notation.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # fn main() -> Result<()> {
    /// let point = Point::new(35.0, 145.0, 5.0);
    /// assert_eq!(point.latitude(), &35.0);
    /// assert_eq!(point.longitude(), &145.0);
    /// assert_eq!(point.altitude(), &5.0);
    ///
    /// // "Rounding"
    /// let point = Point::new(90.0 + 20.0, 180.0 + 20.0, 0.0);
    /// assert_eq!(point.latitude(), &70.0);
    /// assert_eq!(point.longitude(), &-160.0);
    /// assert_eq!(point.altitude(), &0.0);
    /// # Ok(())}
    /// ```
    pub fn new(latitude: f64, longitude: f64, altitude: f64) -> Self {
        Self {
            latitude: utils::round_latitude(&latitude),
            longitude: utils::round_longitude(&longitude),
            altitude,
        }
    }

    /// Makes a [`Point`] with checking.
    ///
    /// # Errors
    ///
    /// If `latitude` and/or `longitude` is out-of-range,
    /// `latitude` must satisfies -90.0 <= and <= 90.0
    /// and `longitude` does -180.0 <= and <= 180.0.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # fn main() -> Result<()> {
    /// let point = Point::try_new(35.0, 145.0, 5.0)?;
    /// assert_eq!(
    ///     point,
    ///     Point::new(35.0, 145.0, 5.0)
    /// );
    ///
    /// // If out-of-range, returns Err
    /// let point = Point::try_new(91.0, 145.0, 5.0);
    /// assert!(point.is_err());
    /// let point = Point::try_new(35.0, 181.0, 5.0);
    /// assert!(point.is_err());
    /// # Ok(())}
    /// ```
    pub fn try_new(latitude: f64, longitude: f64, altitude: f64) -> Result<Self> {
        if latitude.lt(&-90.) || 90.0.lt(&latitude) {
            return Err(Error {
                err: Box::new(error::ErrorImpl::OutOfRangePosition {
                    kind: error::OutOfRangePositionKind::Latitude,
                    low: -90.,
                    high: 90.,
                }),
            });
        } else if longitude.lt(&-180.) || 180.0.lt(&longitude) {
            return Err(Error {
                err: Box::new(error::ErrorImpl::OutOfRangePosition {
                    kind: error::OutOfRangePositionKind::Longitude,
                    low: -180.,
                    high: 180.,
                }),
            });
        }

        Ok(Self {
            latitude,
            longitude,
            altitude,
        })
    }

    /// Returns the latitude of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # fn main() -> Result<()> {
    /// let point = Point::try_new(35.0, 145.0, 5.0)?;
    ///
    /// assert_eq!(point.latitude(), &35.0);
    /// # Ok(())}
    /// ```
    pub fn latitude(&self) -> &f64 {
        &self.latitude
    }

    /// Returns the longitude of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # fn main() -> Result<()> {
    /// let point = Point::try_new(35.0, 145.0, 5.0)?;
    ///
    /// assert_eq!(point.longitude(), &145.0);
    /// # Ok(())}
    /// ```
    pub fn longitude(&self) -> &f64 {
        &self.longitude
    }

    /// Returns the altitude of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # fn main() -> Result<()> {
    /// let point = Point::try_new(35.0, 145.0, 5.0)?;
    ///
    /// assert_eq!(point.altitude(), &5.0);
    /// # Ok(())}
    /// ```
    pub fn altitude(&self) -> &f64 {
        &self.altitude
    }

    /// Makes a [`Point`] where a node, represented by meshcode `code`, locates.
    ///
    /// The resulting altitude is 0.0.
    ///
    /// # Errors
    ///
    /// If invalid meshcode given.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # fn main() -> Result<()> {
    /// assert_eq!(
    ///     Point::try_from_meshcode(&54401027)?,
    ///     Point::new(36.1, 140.0875, 0.0)
    /// );
    /// # Ok(())}
    /// ```
    pub fn try_from_meshcode(code: &u32) -> Result<Self> {
        let node = &MeshNode::try_from_meshcode(code)?;
        Ok(Self::from_node(node))
    }

    /// Makes a [`Point`] where the `node` locates.
    ///
    /// The resulting altitude is 0.0.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshNode;
    /// # fn main() -> Result<()> {
    /// let node = MeshNode::try_from_meshcode(&54401027)?;
    /// assert_eq!(
    ///     Point::from_node(&node),
    ///     Point::new(36.1, 140.0875, 0.0)
    /// );
    /// # Ok(())}
    /// ```
    pub fn from_node(node: &MeshNode) -> Self {
        let latitude = node.latitude.to_latitude();
        let longitude = node.longitude.to_longitude();

        debug_assert!(latitude.ge(&-90.0) && latitude.le(&90.0));
        debug_assert!(longitude.ge(&-180.0) && longitude.le(&180.0));

        Self {
            latitude,
            longitude,
            altitude: 0.,
        }
    }

    /// Returns a meshcode represents the nearest south-east mesh node of `self`.
    ///
    /// The result does not depends on [`altitude`](Point::altitude).
    ///
    /// # Errors
    ///
    /// If [`latitude`](Point::latitude) and/or [`longitude`](Point::longitude) is negative.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::{MeshNode, MeshUnit};
    /// # fn main() -> Result<()> {
    /// let point = Point::new(36.10377479, 140.087855041, 50.0);
    ///
    /// assert_eq!(
    ///     point.try_to_meshcode(&MeshUnit::One)?,
    ///     54401027
    /// );
    /// assert_eq!(
    ///     point.try_to_meshcode(&MeshUnit::Five)?,
    ///     54401005
    /// );
    /// # Ok(())}
    /// ```
    pub fn try_to_meshcode(&self, unit: &MeshUnit) -> Result<u32> {
        let node = self.try_to_node(unit)?;
        Ok(node.to_meshcode())
    }

    /// Returns a nearest south-east [`MeshNode`] of `self`
    ///
    /// The result does not depend on [`altitude`](Point::altitude).
    ///
    /// # Errors
    ///
    /// If [`latitude`](Point::latitude) and/or [`longitude`](Point::longitude) is negative.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::{MeshNode, MeshUnit};
    /// # fn main() -> Result<()> {
    /// let point = Point::new(36.10377479, 140.087855041, 5.0);
    ///
    /// assert_eq!(
    ///     point.try_to_node(&MeshUnit::One)?,
    ///     MeshNode::try_from_meshcode(&54401027)?,
    /// );
    /// assert_eq!(
    ///     point.try_to_node(&MeshUnit::Five)?,
    ///     MeshNode::try_from_meshcode(&54401005)?,
    /// );
    /// # Ok(())}
    /// ```
    pub fn try_to_node(&self, unit: &MeshUnit) -> Result<MeshNode> {
        MeshNode::try_from_point(self, unit)
    }

    /// Returns a [`MeshCell`] containing `self` in.
    ///
    /// # Errors
    ///
    /// If [`latitude`](Point::latitude) and/or [`longitude`](Point::longitude) is negative,
    /// or such [`MeshCell`] is not found.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::{MeshCell, MeshUnit};
    /// # fn main() -> Result<()> {
    /// let point = Point::new(36.10377479, 140.087855041, 10.0);
    ///
    /// assert_eq!(
    ///     point.try_to_cell(MeshUnit::One)?,
    ///     MeshCell::try_from_meshcode(&54401027, MeshUnit::One)?,
    /// );
    /// assert_eq!(
    ///     point.try_to_cell(MeshUnit::Five)?,
    ///     MeshCell::try_from_meshcode(&54401005, MeshUnit::Five)?,
    /// );
    /// # Ok(())}
    /// ```
    pub fn try_to_cell(&self, unit: MeshUnit) -> Result<MeshCell> {
        MeshCell::try_from_point(self, unit)
    }
}
