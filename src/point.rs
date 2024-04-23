//! Provides [`Point`].
use std::ops::{Add, AddAssign, Sub, SubAssign};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::mesh::{MeshCell, MeshNode, MeshUnit};
use crate::transformer::Correction;

/// Returns the normalized latitude into -90.0 <= and <= 90.0.
#[inline(always)]
fn normalize_latitude(t: &f64) -> f64 {
    if t.is_nan() || t.ge(&-90.) && t.le(&90.0) {
        *t
    } else {
        match t % 360.0 {
            s if s.lt(&-270.0) || s.gt(&270.0) => s - f64::copysign(360.0, s),
            s if s.lt(&-90.0) || s.gt(&90.0) => f64::copysign(180.0, s) - s,
            s => s,
        }
    }
}

/// Returns the normalize longitude -180.0 <= and <= 180.0.
#[inline(always)]
fn normalize_longitude(t: &f64) -> f64 {
    if t.is_nan() || t.ge(&-180.0) && t.le(&180.0) {
        *t
    } else {
        match t % 360.0 {
            s if s.lt(&-180.0) || s.gt(&180.0) => s - f64::copysign(360.0, s),
            s => s,
        }
    }
}

/// Represents a position on the Earth, a triplet latitude, longitude and altitude.
///
/// # Example
///
/// ```
/// # use jgdtrans::*;
/// # use jgdtrans::transformer::Correction;
/// // Construct
/// let point = Point::new(35.0, 145.0, 5.0);
///
/// assert_eq!(point.latitude, 35.0);
/// assert_eq!(point.longitude, 145.0);
/// assert_eq!(point.altitude, 5.0);
///
/// // Add/sub Correction
/// let result = &point + Correction::new(1.0, 1.0, 1.0);
/// assert_eq!(result, Point::new(36.0, 146.0, 6.0));
///
/// let result = &result - Correction::new(1.0, 1.0, 1.0);
/// assert_eq!(result, point);
/// ```
#[derive(Debug, PartialEq, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Point {
    /// The latitude \[deg\] of the point
    pub latitude: f64,
    /// The longitude \[deg\] of the point
    pub longitude: f64,
    /// The altitude \[m\] of the point.
    pub altitude: f64,
}

impl From<(f64, f64)> for Point {
    /// see [`Point::new()`], defaulting 0.0 for altitude.
    #[inline]
    fn from(rhs: (f64, f64)) -> Self {
        Self::new(rhs.0, rhs.1, 0.0)
    }
}

impl From<(f64, f64, f64)> for Point {
    /// see [`Point::new()`].
    #[inline]
    fn from(rhs: (f64, f64, f64)) -> Self {
        Self::new(rhs.0, rhs.1, rhs.2)
    }
}

impl From<MeshNode> for Point {
    /// see [`Point::from_node()`].
    #[inline]
    fn from(value: MeshNode) -> Self {
        Self::from_node(&value)
    }
}

impl Add<Correction> for Point {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Correction) -> Self::Output {
        Self::Output::new(
            self.latitude + rhs.latitude,
            self.longitude + rhs.longitude,
            self.altitude + rhs.altitude,
        )
    }
}

impl Add<&Correction> for Point {
    type Output = Self;

    #[inline]
    fn add(self, rhs: &Correction) -> Self::Output {
        Self::Output::new(
            self.latitude + rhs.latitude,
            self.longitude + rhs.longitude,
            self.altitude + rhs.altitude,
        )
    }
}

impl Add<Correction> for &Point {
    type Output = Point;

    #[inline]
    fn add(self, rhs: Correction) -> Self::Output {
        Self::Output::new(
            self.latitude + rhs.latitude,
            self.longitude + rhs.longitude,
            self.altitude + rhs.altitude,
        )
    }
}

impl Add<&Correction> for &Point {
    type Output = Point;

    #[inline]
    fn add(self, rhs: &Correction) -> Self::Output {
        Self::Output::new(
            self.latitude + rhs.latitude,
            self.longitude + rhs.longitude,
            self.altitude + rhs.altitude,
        )
    }
}

impl AddAssign<Correction> for Point {
    #[inline]
    fn add_assign(&mut self, rhs: Correction) {
        self.latitude += rhs.latitude;
        self.longitude += rhs.longitude;
        self.altitude += rhs.altitude;
    }
}

impl AddAssign<&Correction> for Point {
    #[inline]
    fn add_assign(&mut self, rhs: &Correction) {
        self.latitude += rhs.latitude;
        self.longitude += rhs.longitude;
        self.altitude += rhs.altitude;
    }
}

impl Sub<Correction> for Point {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Correction) -> Self::Output {
        Self::Output::new(
            self.latitude - rhs.latitude,
            self.longitude - rhs.longitude,
            self.altitude - rhs.altitude,
        )
    }
}

impl Sub<&Correction> for Point {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: &Correction) -> Self::Output {
        Self::Output::new(
            self.latitude - rhs.latitude,
            self.longitude - rhs.longitude,
            self.altitude - rhs.altitude,
        )
    }
}

impl Sub<Correction> for &Point {
    type Output = Point;

    #[inline]
    fn sub(self, rhs: Correction) -> Self::Output {
        Self::Output::new(
            self.latitude - rhs.latitude,
            self.longitude - rhs.longitude,
            self.altitude - rhs.altitude,
        )
    }
}

impl Sub<&Correction> for &Point {
    type Output = Point;

    #[inline]
    fn sub(self, rhs: &Correction) -> Self::Output {
        Self::Output::new(
            self.latitude - rhs.latitude,
            self.longitude - rhs.longitude,
            self.altitude - rhs.altitude,
        )
    }
}

impl SubAssign<Correction> for Point {
    #[inline]
    fn sub_assign(&mut self, rhs: Correction) {
        self.latitude -= rhs.latitude;
        self.longitude -= rhs.longitude;
        self.altitude -= rhs.altitude;
    }
}

impl SubAssign<&Correction> for Point {
    #[inline]
    fn sub_assign(&mut self, rhs: &Correction) {
        self.latitude -= rhs.latitude;
        self.longitude -= rhs.longitude;
        self.altitude -= rhs.altitude;
    }
}

impl Point {
    /// Makes a [`Point`].
    ///
    /// This does not check any values.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// let point = Point::new(35.0, 145.0, 5.0);
    ///
    /// assert_eq!(point.latitude, 35.0);
    /// assert_eq!(point.longitude, 145.0);
    /// assert_eq!(point.altitude, 5.0);
    /// ```
    #[inline]
    pub const fn new(latitude: f64, longitude: f64, altitude: f64) -> Self {
        Self {
            latitude,
            longitude,
            altitude,
        }
    }

    /// Makes a [`Point`] with checking.
    ///
    /// `latitude` satisfies -90.0 <= and <= 90.0
    /// and `longitude` does -180.0 <= and <= 180.0.
    ///
    /// # Errors
    ///
    /// Returns [`None`] when `latitude` and/or `longitude` is out-of-bounds,
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # fn wrapper() -> Option<()> {
    /// let point = Point::try_new(35.0, 145.0, 5.0)?;
    ///
    /// assert_eq!(point.latitude, 35.0);
    /// assert_eq!(point.longitude, 145.0);
    /// assert_eq!(point.altitude, 5.0);
    ///
    /// assert_eq!(Point::try_new(91.0, 145.0, 5.0), None);
    /// assert_eq!(Point::try_new(35.0, 181.0, 5.0), None);
    /// assert_eq!(Point::try_new(f64::NAN, 145.0, 5.0), None);
    /// assert_eq!(Point::try_new(35.0, f64::NAN, 5.0), None);
    /// assert_eq!(Point::try_new(35.0, 145.0, f64::NAN), None);
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    pub fn try_new(latitude: f64, longitude: f64, altitude: f64) -> Option<Self> {
        if latitude.lt(&-90.)
            || 90.0.lt(&latitude)
            || longitude.lt(&-180.)
            || 180.0.lt(&longitude)
            || latitude.is_nan()
            || longitude.is_nan()
            || altitude.is_nan()
        {
            return None;
        };

        Some(Self::new(latitude, longitude, altitude))
    }

    /// Makes a normalized [`Point`] from `self`.
    ///
    /// The result has normalized [`latitude`](Point::latitude)
    /// and [`longitude`](Point::longitude) which value -90.0 <= and <= 90.0,
    /// and -180.0 <= and <= 180.0 respectively.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// let point = Point::new(100.0, 200.0, 5.0);
    ///
    /// assert_eq!(
    ///     point.normalize(),
    ///     Point::new(80.0, -160.0, 5.0)
    /// );
    /// ```
    #[inline]
    pub fn normalize(&self) -> Self {
        Self {
            latitude: normalize_latitude(&self.latitude),
            longitude: normalize_longitude(&self.longitude),
            altitude: self.altitude,
        }
    }

    /// Makes a [`Point`] where the `meshcode` indicates.
    ///
    /// The resulting altitude is 0.0.
    ///
    /// # Errors
    ///
    /// Returns [`None`] when an invalid meshcode given.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # fn wrapper() -> Option<()> {
    /// let point = Point::try_from_meshcode(&54401027)?;
    ///
    /// assert_eq!(point.latitude, 36.1);
    /// assert_eq!(point.longitude, 140.0875);
    /// assert_eq!(point.altitude, 0.0);
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    pub fn try_from_meshcode(meshcode: &u32) -> Option<Self> {
        MeshNode::try_from_meshcode(meshcode).map(|node| Self::from_node(&node))
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
    /// # fn wrapper() -> Option<()> {
    /// let node = MeshNode::try_from_meshcode(&54401027)?;
    /// let point = Point::from_node(&node);
    ///
    /// assert_eq!(point.latitude, 36.1);
    /// assert_eq!(point.longitude, 140.0875);
    /// assert_eq!(point.altitude, 0.0);
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    pub fn from_node(node: &MeshNode) -> Self {
        let latitude = node.latitude.to_latitude();
        let longitude = node.longitude.to_longitude();
        Self::new(latitude, longitude, 0.)
    }

    /// Returns a meshcode represents the nearest south-east mesh node of `self`.
    ///
    /// The result is independent of [`altitude`](Point::altitude).
    ///
    /// # Errors
    ///
    /// Returns [`None`] when [`latitude`](Point::latitude)
    /// and/or [`longitude`](Point::longitude) is out-of-bounds.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::{MeshNode, MeshUnit};
    /// # fn wrapper() -> Option<()> {
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
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    pub fn try_to_meshcode(&self, mesh_unit: &MeshUnit) -> Option<u32> {
        self.try_to_node(mesh_unit).map(|node| node.to_meshcode())
    }

    /// Returns the nearest south-east [`MeshNode`] of `self`.
    ///
    /// The result is independent of [`altitude`](Point::altitude).
    ///
    /// # Errors
    ///
    /// Returns [`None`] when [`latitude`](Point::latitude)
    /// and/or [`longitude`](Point::longitude) is out-of-bounds.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::{MeshNode, MeshUnit};
    /// let point = Point::new(36.10377479, 140.087855041, 5.0);
    ///
    /// assert_eq!(
    ///     point.try_to_node(&MeshUnit::One),
    ///     MeshNode::try_from_meshcode(&54401027),
    /// );
    /// assert_eq!(
    ///     point.try_to_node(&MeshUnit::Five),
    ///     MeshNode::try_from_meshcode(&54401005),
    /// );
    /// ```
    #[inline]
    pub fn try_to_node(&self, mesh_unit: &MeshUnit) -> Option<MeshNode> {
        MeshNode::try_from_point(self, mesh_unit)
    }

    /// Returns a minimal [`MeshCell`] containing `self`.
    ///
    /// # Errors
    ///
    /// Returns [`None`] when it cannot construct a unit cell.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::{MeshCell, MeshUnit};
    /// # fn wrapper() -> Option<()> {
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
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    pub fn try_to_cell(&self, mesh_unit: MeshUnit) -> Option<MeshCell> {
        MeshCell::try_from_point(self, mesh_unit)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_normalize() {
        for (e, v) in [
            (0., 0.),
            (-0., -0.),
            (20.0, 20.0),
            (-20.0, -20.0),
            (0.0, 360.0),
            (-90.0, 270.0),
            (0.0, 180.0),
            (90.0, 90.0),
            (-0.0, -360.0),
            (90.0, -270.0),
            (-0.0, -180.0),
            (-90.0, -90.0),
            (20.0, 380.),
            (-70.0, 290.),
            (-20.0, 200.),
            (70.0, 110.),
            (-20.0, -380.),
            (70.0, -290.),
            (20.0, -200.),
            (-70.0, -110.),
        ] {
            assert_eq!(Point::new(v, 0.0, 0.0).normalize(), Point::new(e, 0.0, 0.0));
        }

        for (e, v) in [
            (0.0, 0.0),
            (-0.0, -0.0),
            (20.0, 20.0),
            (-20.0, -20.0),
            (0.0, 360.0),
            (-90.0, 270.0),
            (180.0, 180.0),
            (90.0, 90.0),
            (-0.0, -360.0),
            (90.0, -270.0),
            (-180.0, -180.0),
            (-90.0, -90.0),
            (20.0, 380.),
            (-70.0, 290.),
            (-160.0, 200.),
            (110.0, 110.),
            (-20.0, -380.),
            (70.0, -290.),
            (160.0, -200.),
            (-110.0, -110.),
        ] {
            assert_eq!(Point::new(0.0, v, 0.0).normalize(), Point::new(0.0, e, 0.0));
        }

        let actual = Point::new(f64::NAN, f64::NAN, f64::NAN).normalize();
        assert!(actual.latitude.is_nan());
        assert!(actual.longitude.is_nan());
        assert!(actual.altitude.is_nan());
    }
}
