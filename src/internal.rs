macro_rules! impl_ops {
    ($t:ident, $m:ident, $s:ident, $rhs:ident) => {
        impl $t<$rhs> for $s {
            type Output = $s;

            #[inline]
            fn $m(self, rhs: $rhs) -> Self::Output {
                Self::Output::new_unchecked(
                    $t::$m(self.latitude, rhs.latitude),
                    $t::$m(self.longitude, rhs.longitude),
                    $t::$m(self.altitude, rhs.altitude),
                )
                .normalize()
            }
        }

        impl $t<&$rhs> for $s {
            type Output = $s;

            #[inline]
            fn $m(self, rhs: &$rhs) -> Self::Output {
                Self::Output::new_unchecked(
                    $t::$m(self.latitude, rhs.latitude),
                    $t::$m(self.longitude, rhs.longitude),
                    $t::$m(self.altitude, rhs.altitude),
                )
                .normalize()
            }
        }

        impl $t<$rhs> for &$s {
            type Output = $s;

            #[inline]
            fn $m(self, rhs: $rhs) -> Self::Output {
                Self::Output::new_unchecked(
                    $t::$m(self.latitude, rhs.latitude),
                    $t::$m(self.longitude, rhs.longitude),
                    $t::$m(self.altitude, rhs.altitude),
                )
                .normalize()
            }
        }

        impl $t<&$rhs> for &$s {
            type Output = $s;

            #[inline]
            fn $m(self, rhs: &$rhs) -> Self::Output {
                Self::Output::new_unchecked(
                    $t::$m(self.latitude, rhs.latitude),
                    $t::$m(self.longitude, rhs.longitude),
                    $t::$m(self.altitude, rhs.altitude),
                )
                .normalize()
            }
        }
    };
}

macro_rules! impl_assign_ops {
    ($t:ident, $m:ident, $s:ident, $rhs:ident) => {
        impl $t<$rhs> for $s {
            #[inline]
            fn $m(&mut self, rhs: $rhs) {
                $t::$m(&mut self.latitude, rhs.latitude);
                $t::$m(&mut self.longitude, rhs.longitude);
                $t::$m(&mut self.altitude, rhs.altitude);
                *self = self.normalize();
            }
        }

        impl $t<&$rhs> for $s {
            #[inline]
            fn $m(&mut self, rhs: &$rhs) {
                $t::$m(&mut self.latitude, rhs.latitude);
                $t::$m(&mut self.longitude, rhs.longitude);
                $t::$m(&mut self.altitude, rhs.altitude);
                *self = self.normalize();
            }
        }
    };
}

pub(crate) use impl_assign_ops;
pub(crate) use impl_ops;
