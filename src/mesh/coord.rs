use crate::internal::mul_add;
use crate::mesh::{MeshTryFromError, MeshUnit};

/// Represents mesh coordinate, namely, discrete latitude and/or longitude.
///
/// This supports non-negative latitude and longitude only.
///
/// This has three digits, _first_, _second_ and _third_.
/// The first takes values from 0 to 99, the second does from 0 to 7
/// and the third does from 0 to 9 inclusive.
///
/// We note that the third digit takes either 0 or 5 only
/// on the mesh with mesh unit [`MeshUnit::Five`].
///
/// # Example
///
/// ```
/// # use jgdtrans::mesh::*;
/// #
/// # fn wrapper() -> Option<()> {
/// // The selection of MeshCoord depends on mesh unit
/// // Every fifth MeshCoord is taken, when MeshUnit::Five given
/// let coord = MeshCoord::try_from_latitude(&36.103774791666666, &MeshUnit::One)?;
/// assert_eq!(coord, MeshCoord::new(54, 1, 2)?);
/// let coord = MeshCoord::try_from_latitude(&36.103774791666666, &MeshUnit::Five)?;
/// assert_eq!(coord, MeshCoord::new(54, 1, 0)?);
///
/// // Increment/decrement (not in-place)
/// let coord = MeshCoord::new(54, 1, 2)?;
/// assert_eq!(coord.next_up(&MeshUnit::One)?, MeshCoord::new(54, 1, 3)?);
/// assert_eq!(coord.next_down(&MeshUnit::One)?, MeshCoord::new(54, 1, 1)?);
///
/// // Unit must be consistent with MeshCoord,
/// // otherwise it returns None.
/// assert_eq!(coord.next_up(&MeshUnit::Five), None);
/// # Some(())}
/// # fn main() {wrapper();()}
/// ```
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MeshCoord {
    /// Takes 0 to 99 inclusive.
    pub(crate) first: u8,
    /// Takes 0 to 7 inclusive.
    pub(crate) second: u8,
    /// Takes 0 to 9 inclusive.
    pub(crate) third: u8,
}

impl TryFrom<(u8, u8, u8)> for MeshCoord {
    type Error = MeshTryFromError;

    /// Makes a [`MeshCoord`], see [`MeshCoord::new`].
    #[inline]
    fn try_from(value: (u8, u8, u8)) -> Result<Self, Self::Error> {
        Self::new(value.0, value.1, value.2).ok_or(Self::Error::new())
    }
}

impl MeshCoord {
    /// Smallest [`MeshCoord`] value.
    ///
    /// Equals to `MeshCoord { first: 0, second: 0, third: 0 }.`
    pub const MIN: MeshCoord = Self {
        first: 0,
        second: 0,
        third: 0,
    };

    /// Largest [`MeshCoord`] value.
    ///
    /// Equals to `MeshCoord { first: 99, second: 7, third: 9 }.`
    pub const MAX: MeshCoord = Self {
        first: 99,
        second: 7,
        third: 9,
    };

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
    /// # use jgdtrans::mesh::MeshCoord;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// let coord = MeshCoord::new(1, 2, 3)?;
    ///
    /// assert_eq!(coord.first(), &1);
    /// assert_eq!(coord.second(), &2);
    /// assert_eq!(coord.third(), &3);
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    #[must_use = "method returns a new `MeshCoord` and does not mutate the original value"]
    pub const fn new(first: u8, second: u8, third: u8) -> Option<Self> {
        if first > Self::MAX.first || second > Self::MAX.second || third > Self::MAX.third {
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
    /// # use jgdtrans::mesh::MeshCoord;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// let coord = MeshCoord::new(1, 2, 3)?;
    ///
    /// assert_eq!(coord.first(), &1);
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    #[must_use]
    pub const fn first(&self) -> &u8 {
        &self.first
    }

    /// Returns the second digit (`0..8`) of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::mesh::MeshCoord;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// let coord = MeshCoord::new(1, 2, 3)?;
    ///
    /// assert_eq!(coord.second(), &2);
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    #[must_use]
    pub const fn second(&self) -> &u8 {
        &self.second
    }

    /// Returns the third digit (`0..10`) of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::mesh::MeshCoord;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// let coord = MeshCoord::new(1, 2, 3)?;
    ///
    /// assert_eq!(coord.third(), &3);
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    #[must_use]
    pub const fn third(&self) -> &u8 {
        &self.third
    }

    /// Returns `true` if `self` is compatible to the `mesh_unit`.
    ///
    /// This always returns `true` when `mesh_unit` is [`MeshUnit::One`].
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::mesh::*;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// let coord = MeshCoord::new(1, 2, 3)?;
    ///
    /// assert_eq!(coord.is_mesh_unit(&MeshUnit::One), true);
    /// assert_eq!(coord.is_mesh_unit(&MeshUnit::Five), false);
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_mesh_unit(&self, mesh_unit: &MeshUnit) -> bool {
        match mesh_unit {
            MeshUnit::One => true,
            MeshUnit::Five => (self.third % mesh_unit.to_u8()) == 0,
        }
    }

    fn from_degree(degree: &f64, mesh_unit: &MeshUnit) -> Self {
        assert!((0.0..=180.0).contains(degree));

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
    /// # use jgdtrans::mesh::*;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// let degree = 36.103774791666666;
    ///
    /// assert_eq!(
    ///     MeshCoord::try_from_latitude(&degree, &MeshUnit::One)?,
    ///     MeshCoord::new(54, 1, 2)?
    /// );
    /// assert_eq!(
    ///     MeshCoord::try_from_latitude(&degree, &MeshUnit::Five)?,
    ///     MeshCoord::new(54, 1, 0)?
    /// );
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    #[must_use]
    pub fn try_from_latitude(degree: &f64, mesh_unit: &MeshUnit) -> Option<Self> {
        if degree.is_nan() {
            return None;
        };

        let value = {
            let value = 3.0 * degree / 2.0;

            // Minimum add-hook trick to ensure the identity,
            // 1. MeshCoord::try_from_latitude(&coord.to_latitude(), &MeshUnit::One)
            // 2. MeshCoord::try_from_longitude(&coord.to_longitude(), &MeshUnit::One)
            if (degree.to_bits() % 2) == 1 {
                value.next_up()
            } else {
                value
            }
        };

        if !(0.0..=100.0).contains(&value) {
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
    /// # use jgdtrans::mesh::*;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// let degree = 140.08785504166664;
    ///
    /// assert_eq!(
    ///     MeshCoord::try_from_longitude(&degree, &MeshUnit::One)?,
    ///     MeshCoord::new(40, 0, 7)?
    /// );
    /// assert_eq!(
    ///     MeshCoord::try_from_longitude(&degree, &MeshUnit::Five)?,
    ///     MeshCoord::new(40, 0, 5)?
    /// );
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[must_use]
    pub fn try_from_longitude(degree: &f64, mesh_unit: &MeshUnit) -> Option<Self> {
        if !(100.0..=180.0).contains(degree) || degree.is_nan() {
            return None;
        };

        Some(Self::from_degree(degree, mesh_unit))
    }

    #[inline]
    fn to_degree(&self) -> f64 {
        // self.first as f64 + self.second as f64 / 8. + self.third as f64 / 80.
        let r = mul_add!(self.second as f64, 1. / 8., self.first as f64);
        mul_add!(self.third as f64, 1. / 80., r)
    }

    /// Returns the latitude that `self` converts into.
    ///
    /// This does not check that `self` represents latitude.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::mesh::*;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// let degree = 36.103774791666666;
    ///
    /// // MeshCoord is a component of the greatest node less than `degree`
    /// let coord = MeshCoord::try_from_latitude(&degree, &MeshUnit::One)?;
    /// assert_eq!(coord.to_latitude(), 36.1);
    ///
    /// let coord = MeshCoord::try_from_latitude(&degree, &MeshUnit::Five)?;
    /// assert_eq!(coord.to_latitude(), 36.083333333333336);
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    #[must_use]
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
    /// # use jgdtrans::mesh::*;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// let degree = 140.08785504166664;
    ///
    /// // MeshCoord is a component of the greatest node less than `degree`
    /// let coord = MeshCoord::try_from_longitude(&degree, &MeshUnit::One)?;
    /// assert_eq!(coord.to_longitude(), 140.0875);
    ///
    /// let coord = MeshCoord::try_from_longitude(&degree, &MeshUnit::Five)?;
    /// assert_eq!(coord.to_longitude(), 140.0625);
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[inline]
    #[must_use]
    pub fn to_longitude(&self) -> f64 {
        100. + self.to_degree()
    }

    /// Returns the smallest [`MeshCoord`] greater than `self`.
    ///
    /// # Errors
    ///
    /// Returns [`None`] when `self` is incompatible to `mesh_unit`
    /// or `self` is `MeshCoord { first: 99, second: 7, third: 9 }`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::mesh::*;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// let coord = MeshCoord::new(0, 0, 0)?;
    ///
    /// assert_eq!(
    ///     coord.next_up(&MeshUnit::One)?,
    ///     MeshCoord::new(0, 0, 1)?
    /// );
    /// assert_eq!(
    ///     coord.next_up(&MeshUnit::Five)?,
    ///     MeshCoord::new(0, 0, 5)?
    /// );
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[must_use]
    pub const fn next_up(&self, mesh_unit: &MeshUnit) -> Option<Self> {
        if !self.is_mesh_unit(mesh_unit) {
            return None;
        }

        // 10 - u8::from(mesh_unit)
        let bound = match mesh_unit {
            MeshUnit::One => 9,
            MeshUnit::Five => 5,
        };

        if self.third == bound {
            if self.second == Self::MAX.second {
                if self.first == Self::MAX.first {
                    None
                } else {
                    // `first` is not 99
                    Some(Self {
                        first: self.first + 1,
                        second: Self::MIN.second,
                        third: Self::MIN.third,
                    })
                }
            } else {
                // `second` is not 7
                Some(Self {
                    first: self.first,
                    second: self.second + 1,
                    third: Self::MIN.third,
                })
            }
        } else {
            // `third` is not 1 nor 5
            Some(Self {
                first: self.first,
                second: self.second,
                third: self.third + mesh_unit.to_u8(),
            })
        }
    }

    /// Returns the greatest [`MeshCoord`] less than `self`.
    ///
    /// # Errors
    ///
    /// Returns [`None`] when `self` is incompatible to `mesh_unit`
    /// or `self` is `MeshCoord { first: 0, second: 0, third: 0 }`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::mesh::*;
    /// #
    /// # fn wrapper() -> Option<()> {
    /// assert_eq!(
    ///     MeshCoord::new(0, 0, 1)?.next_down(&MeshUnit::One)?,
    ///     MeshCoord::new(0, 0, 0)?
    /// );
    /// assert_eq!(
    ///     MeshCoord::new(0, 0, 5)?.next_down(&MeshUnit::Five)?,
    ///     MeshCoord::new(0, 0, 0)?
    /// );
    /// # Some(())}
    /// # fn main() {wrapper();()}
    /// ```
    #[must_use]
    pub const fn next_down(&self, mesh_unit: &MeshUnit) -> Option<Self> {
        if !self.is_mesh_unit(mesh_unit) {
            return None;
        }

        // 10 - u8::from(mesh_unit)
        let bound = match mesh_unit {
            MeshUnit::One => 9,
            MeshUnit::Five => 5,
        };

        if self.third == Self::MIN.third {
            if self.second == Self::MIN.second {
                if self.first == Self::MIN.first {
                    None
                } else {
                    // `first` is not 0
                    Some(Self {
                        first: self.first - 1,
                        second: Self::MAX.second,
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
                third: self.third - mesh_unit.to_u8(),
            })
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_try_new() {
        assert!(MeshCoord::new(100, 0, 0).is_none());
        assert!(MeshCoord::new(99, 8, 0).is_none());
        assert!(MeshCoord::new(99, 7, 10).is_none());
    }

    #[test]
    fn test_try_from() {
        let coord: Result<MeshCoord, _> = (0, 0, 0).try_into();
        assert!(coord.is_ok());

        let coord: Result<MeshCoord, _> = (100, 0, 0).try_into();
        assert!(coord.is_err());

        let coord: Result<MeshCoord, _> = (99, 8, 0).try_into();
        assert!(coord.is_err());

        let coord: Result<MeshCoord, _> = (99, 7, 10).try_into();
        assert!(coord.is_err());
    }

    #[test]
    fn test_getter() {
        let coord = MeshCoord::new(99, 7, 9).unwrap();
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
            MeshCoord::new(0, 0, 0).unwrap()
        );
        assert_eq!(
            MeshCoord::try_from_latitude(&66.66666666666665, &MeshUnit::One).unwrap(),
            MeshCoord::new(99, 7, 9).unwrap()
        );

        // healthy
        assert_eq!(
            MeshCoord::try_from_latitude(&36.103774791666666, &MeshUnit::One).unwrap(),
            MeshCoord::new(54, 1, 2).unwrap()
        );
        assert_eq!(
            MeshCoord::try_from_latitude(&36.103774791666666, &MeshUnit::Five).unwrap(),
            MeshCoord::new(54, 1, 0).unwrap()
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
            MeshCoord::new(0, 0, 0).unwrap()
        );
        assert_eq!(
            MeshCoord::try_from_longitude(&180.0, &MeshUnit::One).unwrap(),
            MeshCoord::new(80, 0, 0).unwrap()
        );

        // healthy
        assert_eq!(
            MeshCoord::try_from_longitude(&140.08785504166664, &MeshUnit::One).unwrap(),
            MeshCoord::new(40, 0, 7).unwrap()
        );
        assert_eq!(
            MeshCoord::try_from_longitude(&140.08785504166664, &MeshUnit::Five).unwrap(),
            MeshCoord::new(40, 0, 5).unwrap()
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
        assert!(MeshCoord::new(0, 7, 2)
            .unwrap()
            .next_up(&MeshUnit::Five)
            .is_none());
        assert!(MeshCoord::new(99, 7, 9)
            .unwrap()
            .next_up(&MeshUnit::One)
            .is_none());
        assert!(MeshCoord::new(99, 7, 5)
            .unwrap()
            .next_up(&MeshUnit::Five)
            .is_none());

        // healty
        assert_eq!(
            MeshCoord::new(0, 0, 0)
                .unwrap()
                .next_up(&MeshUnit::One)
                .unwrap(),
            MeshCoord::new(0, 0, 1).unwrap(),
        );
        assert_eq!(
            MeshCoord::new(0, 0, 0)
                .unwrap()
                .next_up(&MeshUnit::Five)
                .unwrap(),
            MeshCoord::new(0, 0, 5).unwrap(),
        );

        // healty: carry
        assert_eq!(
            MeshCoord::new(0, 0, 9)
                .unwrap()
                .next_up(&MeshUnit::One)
                .unwrap(),
            MeshCoord::new(0, 1, 0).unwrap(),
        );
        assert_eq!(
            MeshCoord::new(0, 7, 9)
                .unwrap()
                .next_up(&MeshUnit::One)
                .unwrap(),
            MeshCoord::new(1, 0, 0).unwrap(),
        );

        assert_eq!(
            MeshCoord::new(0, 0, 5)
                .unwrap()
                .next_up(&MeshUnit::Five)
                .unwrap(),
            MeshCoord::new(0, 1, 0).unwrap(),
        );
        assert_eq!(
            MeshCoord::new(0, 7, 5)
                .unwrap()
                .next_up(&MeshUnit::Five)
                .unwrap(),
            MeshCoord::new(1, 0, 0).unwrap(),
        );
    }

    #[test]
    fn test_try_next_down() {
        // error
        assert!(MeshCoord::new(0, 7, 2)
            .unwrap()
            .next_down(&MeshUnit::Five)
            .is_none());
        assert!(MeshCoord::new(0, 0, 0)
            .unwrap()
            .next_down(&MeshUnit::One)
            .is_none());

        // healty
        assert_eq!(
            MeshCoord::new(0, 0, 1)
                .unwrap()
                .next_down(&MeshUnit::One)
                .unwrap(),
            MeshCoord::new(0, 0, 0).unwrap(),
        );
        assert_eq!(
            MeshCoord::new(0, 0, 5)
                .unwrap()
                .next_down(&MeshUnit::Five)
                .unwrap(),
            MeshCoord::new(0, 0, 0).unwrap(),
        );

        // healty: carry
        assert_eq!(
            MeshCoord::new(0, 1, 0)
                .unwrap()
                .next_down(&MeshUnit::One)
                .unwrap(),
            MeshCoord::new(0, 0, 9).unwrap(),
        );
        assert_eq!(
            MeshCoord::new(1, 0, 0)
                .unwrap()
                .next_down(&MeshUnit::One)
                .unwrap(),
            MeshCoord::new(0, 7, 9).unwrap(),
        );

        assert_eq!(
            MeshCoord::new(0, 1, 0)
                .unwrap()
                .next_down(&MeshUnit::Five)
                .unwrap(),
            MeshCoord::new(0, 0, 5).unwrap(),
        );
        assert_eq!(
            MeshCoord::new(1, 0, 0)
                .unwrap()
                .next_down(&MeshUnit::Five)
                .unwrap(),
            MeshCoord::new(0, 7, 5).unwrap(),
        );
    }

    #[test]
    fn test_identity_on_from_to() {
        // latitude
        let bound = MeshCoord::new(99, 7, 9).unwrap();
        let mut coord = MeshCoord::new(0, 0, 0).unwrap();
        while coord != bound {
            assert_eq!(
                coord,
                MeshCoord::try_from_latitude(&coord.to_latitude(), &MeshUnit::One).unwrap(),
            );
            coord = coord.next_up(&MeshUnit::One).unwrap();
        }
        assert_eq!(
            coord,
            MeshCoord::try_from_latitude(&coord.to_latitude(), &MeshUnit::One).unwrap(),
        );

        // longitude
        let bound = MeshCoord::new(80, 0, 0).unwrap();
        let mut coord = MeshCoord::new(0, 0, 0).unwrap();
        while coord != bound {
            assert_eq!(
                coord,
                MeshCoord::try_from_longitude(&coord.to_longitude(), &MeshUnit::One).unwrap(),
            );
            coord = coord.next_up(&MeshUnit::One).unwrap();
        }
        assert_eq!(
            coord,
            MeshCoord::try_from_longitude(&coord.to_longitude(), &MeshUnit::One).unwrap(),
        );
    }
}
