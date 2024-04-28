macro_rules! impl_ops {
    ($t:ident, $m:ident, $s:ident, $rhs:ident) => {
        impl $t<$rhs> for $s {
            type Output = $s;

            #[inline]
            fn $m(self, rhs: $rhs) -> Self::Output {
                Self::Output::new(
                    $t::$m(self.latitude, rhs.latitude),
                    $t::$m(self.longitude, rhs.longitude),
                    $t::$m(self.altitude, rhs.altitude),
                )
            }
        }

        impl $t<&$rhs> for $s {
            type Output = $s;

            #[inline]
            fn $m(self, rhs: &$rhs) -> Self::Output {
                Self::Output::new(
                    $t::$m(self.latitude, rhs.latitude),
                    $t::$m(self.longitude, rhs.longitude),
                    $t::$m(self.altitude, rhs.altitude),
                )
            }
        }

        impl $t<$rhs> for &$s {
            type Output = $s;

            #[inline]
            fn $m(self, rhs: $rhs) -> Self::Output {
                Self::Output::new(
                    $t::$m(self.latitude, rhs.latitude),
                    $t::$m(self.longitude, rhs.longitude),
                    $t::$m(self.altitude, rhs.altitude),
                )
            }
        }

        impl $t<&$rhs> for &$s {
            type Output = $s;

            #[inline]
            fn $m(self, rhs: &$rhs) -> Self::Output {
                Self::Output::new(
                    $t::$m(self.latitude, rhs.latitude),
                    $t::$m(self.longitude, rhs.longitude),
                    $t::$m(self.altitude, rhs.altitude),
                )
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
            }
        }

        impl $t<&$rhs> for $s {
            #[inline]
            fn $m(&mut self, rhs: &$rhs) {
                $t::$m(&mut self.latitude, rhs.latitude);
                $t::$m(&mut self.longitude, rhs.longitude);
                $t::$m(&mut self.altitude, rhs.altitude);
            }
        }
    };
}

macro_rules! mul_add {
    ($a:expr, $b:expr, $c:expr) => {
        if cfg!(target_feature = "fma") {
            f64::mul_add($a, $b, $c)
        } else {
            $a * $b + $c
        }
    };
}

pub(crate) use impl_assign_ops;
pub(crate) use impl_ops;
pub(crate) use mul_add;
