#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::mesh::{MeshCoord, MeshTryFromError, MeshUnit};
use crate::Point;

/// Represents mesh node, a pair of [`MeshCoord`]s.
///
/// We note that this supports non-negative latitude and longitude only.
///
/// # Example
///
/// ```
/// # use jgdtrans::*;
/// # use jgdtrans::mesh::*;
/// #
/// fn wrapper() -> Option<()> {
/// // Construct from latitude and longitude, altitude ignores
/// let point = Point::new(36.10377479, 140.087855041, 0.0);
/// let node = MeshNode::try_from_point(&point, &MeshUnit::One)?;
/// assert_eq!(node.to_meshcode(), 54401027);
///
/// // The result depends on the mesh_unit
/// let node = MeshNode::try_from_point(&point, &MeshUnit::Five)?;
/// assert_eq!(node.to_meshcode(), 54401005);
///
/// // Construct from meshcode
/// let node = MeshNode::try_from_meshcode(&54401027)?;
///
/// // The position where the MeshNode locates
/// assert_eq!(node.to_point(), Point::new(36.1, 140.0875, 0.0));
/// # Some(())}
/// # fn main() {wrapper();()}
/// ```
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct MeshNode {
    /// The mesh coord of latitude
    pub(crate) latitude: MeshCoord,
    /// The mesh coord of longitude
    ///
    /// This satisfies <= `MeshCoord { first: 80, second: 0, third: 0 }`
    pub(crate) longitude: MeshCoord,
}

impl<T1, T2> TryFrom<(T1, T2)> for MeshNode
where
    T1: TryInto<MeshCoord, Error = MeshTryFromError>,
    T2: TryInto<MeshCoord, Error = MeshTryFromError>,
{
    type Error = MeshTryFromError;

    /// Makes a [`MeshNode`], see [`MeshNode::try_new`].
    #[inline]
    fn try_from(value: (T1, T2)) -> Result<Self, Self::Error> {
        let latitude: MeshCoord = value.0.try_into().map_err(|_| Self::Error::new())?;
        let longitude: MeshCoord = value.1.try_into().map_err(|_| Self::Error::new())?;
        Self::try_new(latitude, longitude).ok_or(Self::Error::new())
    }
}

impl TryFrom<&u32> for MeshNode {
    type Error = MeshTryFromError;

    /// Makes a [`MeshNode`] from meshcode, see [`MeshNode::try_from_meshcode`].
    #[inline]
    fn try_from(value: &u32) -> Result<Self, Self::Error> {
        Self::try_from_meshcode(value).ok_or(Self::Error::new())
    }
}

impl From<MeshNode> for u32 {
    /// Makes a meshcode from [`MeshNode`], see [`MeshNode::to_meshcode`].
    #[inline]
    fn from(value: MeshNode) -> Self {
        value.to_meshcode()
    }
}

impl MeshNode {
    /// Smallest [`MeshNode`] value.
    ///
    /// Equals to `MeshNode { latitude: MeshCoord { first: 0, second: 0, third: 0 }, longitude: MeshCoord { first: 0, second: 0, third: 0 } }`.
    pub const MIN: MeshNode = MeshNode {
        latitude: MeshCoord {
            first: 0,
            second: 0,
            third: 0,
        },
        longitude: MeshCoord {
            first: 0,
            second: 0,
            third: 0,
        },
    };

    /// Largest [`MeshNode`] value.
    ///
    /// Equals to `MeshNode { latitude: MeshCoord { first: 99, second: 7, third: 9 }, longitude: MeshCoord { first: 80, second: 0, third: 0 } }`.
    pub const MAX: MeshNode = MeshNode {
        latitude: MeshCoord {
            first: 99,
            second: 7,
            third: 9,
        },
        longitude: MeshCoord {
            first: 80,
            second: 0,
            third: 0,
        },
    };

    /// Makes a [`MeshNode`].
    ///
    /// `longitude` satisfies <= `MeshCoord { first: 80, second: 0, third: 0 }`.
    ///
    /// # Errors
    ///
    /// Returns [`None`] when `longitude` is out-of-bounds.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::mesh::*;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// let latitude = MeshCoord::try_new(54, 1, 2)?;
    /// let longitude = MeshCoord::try_new(40, 0, 7)?;
    ///
    /// let node = MeshNode::try_new(latitude.clone(), longitude.clone())?;
    ///
    /// assert_eq!(node.latitude(), &latitude);
    /// assert_eq!(node.longitude(), &longitude);
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    pub const fn try_new(latitude: MeshCoord, longitude: MeshCoord) -> Option<Self> {
        // TODO: use Ord::gt (longitude.gt(&Self::MAX.longitude))
        //       when `feature(const_trait_impl)` stable
        if longitude.first > Self::MAX.longitude.first
            || (longitude.first == Self::MAX.longitude.first
                && !(longitude.second == Self::MAX.longitude.second
                    && longitude.third == Self::MAX.longitude.third))
        {
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
    /// # use jgdtrans::mesh::*;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// let latitude = MeshCoord::try_new(54, 1, 2)?;
    /// let longitude = MeshCoord::try_new(40, 0, 7)?;
    ///
    /// let node = MeshNode::try_new(latitude.clone(), longitude)?;
    ///
    /// assert_eq!(node.latitude(), &latitude);
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    pub const fn latitude(&self) -> &MeshCoord {
        &self.latitude
    }

    /// Returns the longitude coordinate of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::mesh::*;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// let latitude = MeshCoord::try_new(54, 1, 2)?;
    /// let longitude = MeshCoord::try_new(40, 0, 7)?;
    ///
    /// let node = MeshNode::try_new(latitude, longitude.clone())?;
    ///
    /// assert_eq!(node.longitude(), &longitude);
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    pub const fn longitude(&self) -> &MeshCoord {
        &self.longitude
    }

    /// Returns `true` if `self` is compatible to the `mesh_unit`.
    ///
    /// This always returns `true` when [`MeshUnit::One`] given.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::mesh::*;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// let node = MeshNode::try_from_meshcode(&54401027)?;
    ///
    /// assert_eq!(node.is_mesh_unit(&MeshUnit::One), true);
    /// assert_eq!(node.is_mesh_unit(&MeshUnit::Five), false);
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    pub const fn is_mesh_unit(&self, mesh_unit: &MeshUnit) -> bool {
        self.latitude.is_mesh_unit(mesh_unit) && self.longitude.is_mesh_unit(mesh_unit)
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
    /// #
    /// fn wrapper() -> Option<()> {
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
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
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
    /// # use jgdtrans::mesh::*;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// assert_eq!(
    ///     MeshNode::try_from_meshcode(&54401027)?,
    ///     MeshNode::try_new(
    ///         MeshCoord::try_new(54, 1, 2)?,
    ///         MeshCoord::try_new(40, 0, 7)?
    ///     )?
    /// );
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    pub const fn try_from_meshcode(meshcode: &u32) -> Option<Self> {
        #[allow(clippy::inconsistent_digit_grouping)]
        if *meshcode >= 10000_00_00 {
            return None;
        }

        macro_rules! div_rem {
            ($n:expr, $m:literal) => {
                ($n / $m, $n % $m)
            };
        }

        // code < 10000_00_00
        // lat_first, lng_first < 100
        #[allow(clippy::inconsistent_digit_grouping)]
        let (lat_first, rest) = div_rem!(*meshcode, 100_00_00_u32);
        #[allow(clippy::inconsistent_digit_grouping)]
        let (lng_first, rest) = div_rem!(rest, 100_00_u32);

        // lat_second, lng_second < 8
        let (lat_second, rest) = div_rem!(rest, 10_00_u32);
        let (lng_second, rest) = div_rem!(rest, 100_u32);

        // lat_third, lng_third < 10
        let (lat_third, lng_third) = div_rem!(rest, 10_u32);

        // TODO: use `?` when `feature(const_trait_impl)` stable
        let latitude = match MeshCoord::try_new(lat_first as u8, lat_second as u8, lat_third as u8)
        {
            Some(r) => r,
            None => return None,
        };
        let longitude = match MeshCoord::try_new(lng_first as u8, lng_second as u8, lng_third as u8)
        {
            Some(r) => r,
            None => return None,
        };

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
    /// # use jgdtrans::mesh::*;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// let node = MeshNode::try_new(
    ///     MeshCoord::try_new(54, 1, 2)?,
    ///     MeshCoord::try_new(40, 0, 7)?
    /// )?;
    ///
    /// assert_eq!(node.to_meshcode(), 54401027);
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    pub const fn to_meshcode(&self) -> u32 {
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
    /// #
    /// fn wrapper() -> Option<()> {
    /// let node = MeshNode::try_new(
    ///     MeshCoord::try_new(54, 1, 2)?,
    ///     MeshCoord::try_new(40, 0, 7)?
    /// )?;
    ///
    /// assert_eq!(node.to_point(), Point::new(36.1, 140.0875, 0.0));
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    pub fn to_point(&self) -> Point {
        Point {
            latitude: self.latitude.to_latitude(),
            longitude: self.longitude.to_longitude(),
            altitude: 0.0,
        }
    }
}

#[cfg(test)]
mod test {
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
        assert!(MeshNode::try_new(MeshCoord::try_new(0, 0, 0).unwrap(), coord).is_none());
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
                MeshCoord::try_new(40, 0, 7).unwrap(),
            )
            .unwrap()
        );

        assert_eq!(
            MeshNode::try_from_point(&point, &MeshUnit::Five).unwrap(),
            MeshNode::try_new(
                MeshCoord::try_new(54, 1, 0).unwrap(),
                MeshCoord::try_new(40, 0, 5).unwrap(),
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
                MeshCoord::try_new(40, 0, 7).unwrap(),
            )
            .unwrap()
        );
        assert_eq!(
            MeshNode::try_from_meshcode(&0).unwrap(),
            MeshNode::try_new(
                MeshCoord::try_new(0, 0, 0).unwrap(),
                MeshCoord::try_new(0, 0, 0).unwrap(),
            )
            .unwrap()
        );
    }

    #[test]
    fn test_to_meshcode() {
        assert_eq!(
            MeshNode::try_new(
                MeshCoord::try_new(54, 1, 2).unwrap(),
                MeshCoord::try_new(40, 0, 7).unwrap(),
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
                MeshCoord::try_new(40, 0, 7).unwrap(),
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

    #[test]
    fn test_try_from() {
        let coord = MeshCoord::try_new(0, 0, 0).unwrap();

        assert_eq!(
            MeshNode::try_new(coord.clone(), coord.clone()).unwrap(),
            MeshNode::try_from(((0, 0, 0), (0, 0, 0))).unwrap()
        );
    }
}
