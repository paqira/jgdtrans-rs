use crate::mesh::MeshUnit;
use crate::{fma, Point};

/// For unchecked transformation.
#[derive(Debug)]
pub(crate) struct MeshCode(
    /// latitude
    (u8, u8, u8),
    /// longitude
    (u8, u8, u8),
);

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

        let integer = [latitude.floor() as u32, longitude.floor() as u32];
        let first = integer.map(|v| v % 100);
        let second = [
            (8. * latitude).floor() as u32 - 8 * integer[0],
            (8. * longitude).floor() as u32 - 8 * integer[1],
        ];
        let third = [
            (80. * latitude).floor() as u32 - 80 * integer[0] - 10 * second[0],
            (80. * longitude).floor() as u32 - 80 * integer[1] - 10 * second[1],
        ];

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
    fn to_pos(&self) -> [f64; 2] {
        // f64 exactly represents 1/8 and 1/80
        // thus we can use. e.g., mul 1/80 instead of div 80
        let temp = [
            fma(self.0 .1 as f64, 1. / 8., self.0 .0 as f64),
            fma(self.1 .1 as f64, 1. / 8., self.1 .0 as f64),
        ];
        let temp = [
            fma(self.0 .2 as f64, 1. / 80., temp[0]),
            fma(self.1 .2 as f64, 1. / 80., temp[1]),
        ];

        [2. * temp[0] / 3., 100. + temp[1]]
    }

    /// See [`MeshCell::position`].
    #[inline]
    pub(crate) fn position(&self, point: &Point, mesh_unit: &MeshUnit) -> (f64, f64) {
        let [lat, lng] = self.to_pos();

        let x = point.longitude - lng;
        let y = point.latitude - lat;

        match mesh_unit {
            MeshUnit::One => (120. * y, 80. * x),
            MeshUnit::Five => (24. * y, 16. * x),
        }
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
                (self.1 .0, self.1 .1, self.1 .2 + mesh_unit.to_u8()),
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
                (self.0 .0, self.0 .1, self.0 .2 + mesh_unit.to_u8()),
                self.1,
            )
        }
    }
}
