use crate::mesh::MeshUnit;
use crate::vector::{f64x2, u32x2, u8x2, F64x2};
use crate::Point;

/// For unchecked transformation.
#[derive(Debug)]
pub(crate) struct MeshCode((u8, u8, u8), (u8, u8, u8));

impl MeshCode {
    /// See [`MeshCoord::try_from_latitude`], [`MeshCoord::try_from_longitude`] and [`MeshCoord::from_degree`].
    #[inline]
    pub(crate) fn from_point(point: &Point, mesh_unit: &MeshUnit) -> Self {
        let latitude = {
            let temp = 3.0 * point.latitude / 2.0;
            if (point.latitude.to_bits() % 2).eq(&1) {
                temp.next_up()
            } else {
                temp
            }
        };

        let longitude = point.longitude;

        let integer = f64x2!(latitude, longitude).floor().as_u32();
        let first = integer % u32x2!(100);
        let second =
            (f64x2!(8.) * f64x2!(latitude, longitude)).floor().as_u32() - u32x2!(8) * integer;
        let third = (f64x2!(80.) * f64x2!(latitude, longitude)).floor().as_u32()
            - u32x2!(80) * integer
            - u32x2!(10) * second;

        Self(
            (
                first[0] as u8,
                second[0] as u8,
                match mesh_unit {
                    MeshUnit::One => third[0] as u8,
                    MeshUnit::Five => {
                        if third[0] < 5 {
                            0
                        } else {
                            5
                        }
                    }
                },
            ),
            (
                first[1] as u8,
                second[1] as u8,
                match mesh_unit {
                    MeshUnit::One => third[1] as u8,
                    MeshUnit::Five => {
                        if third[1] < 5 {
                            0
                        } else {
                            5
                        }
                    }
                },
            ),
        )
    }

    /// See [`MeshNode::to_meshcode`].
    #[inline]
    pub(crate) const fn to_u32(&self) -> u32 {
        (self.0 .0 as u32 * 100 + self.1 .0 as u32) * 10_000
            + (self.0 .1 as u32 * 10 + self.1 .1 as u32) * 100
            + (self.0 .2 as u32 * 10 + self.1 .2 as u32)
    }

    /// See [`MeshCoord::to_latitude`], [`MeshCoord::to_longitude`] and [`MeshCoord::to_degree`].
    #[inline]
    fn to_pos(&self) -> F64x2 {
        let temp = u8x2!(self.0 .1, self.1 .1)
            .cast::<f64>()
            .fma(f64x2!(1. / 8.), u8x2!(self.0 .0, self.1 .0).cast::<f64>());
        let temp = u8x2!(self.0 .2, self.1 .2)
            .cast::<f64>()
            .fma(f64x2!(1. / 80.), temp);

        f64x2!(2. * temp[0] / 3., 100. + temp[1])
    }

    /// See [`MeshCell::position`].
    #[inline]
    pub(crate) fn position(&self, point: &Point, mesh_unit: &MeshUnit) -> (f64, f64) {
        let pos = f64x2!(point.latitude, point.longitude) - self.to_pos();

        match mesh_unit {
            MeshUnit::One => f64x2!(120., 80.) * pos,
            MeshUnit::Five => f64x2!(24., 16.) * pos,
        }
        .into()
    }

    /// See [`MeshCoord::try_next_up`].
    #[inline]
    pub(crate) const fn next_east(&self, mesh_unit: &MeshUnit) -> Self {
        let bound = match mesh_unit {
            MeshUnit::One => 9,
            MeshUnit::Five => 5,
        };

        if self.1 .2 == bound {
            if self.1 .1 == 7 {
                Self(self.0, (self.1 .0 + 1, 0, 0))
            } else {
                Self(self.0, (self.1 .0, self.1 .1 + 1, 0))
            }
        } else {
            Self(
                self.0,
                (self.1 .0, self.1 .1, self.1 .2 + mesh_unit.as_u8()),
            )
        }
    }

    /// See [`MeshCoord::try_next_up`].
    #[inline]
    pub(crate) const fn next_north(&self, mesh_unit: &MeshUnit) -> Self {
        let bound = match mesh_unit {
            MeshUnit::One => 9,
            MeshUnit::Five => 5,
        };

        if self.0 .2 == bound {
            if self.0 .1 == 7 {
                Self((self.0 .0 + 1, 0, 0), self.1)
            } else {
                Self((self.0 .0, self.0 .1 + 1, 0), self.1)
            }
        } else {
            Self(
                (self.0 .0, self.0 .1, self.0 .2 + mesh_unit.as_u8()),
                self.1,
            )
        }
    }
}
