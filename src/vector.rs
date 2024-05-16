use std::ops::{Add, Div, Index, Mul, Neg, Sub};

#[derive(Debug, Clone, Copy)]
pub(crate) struct F64x2(f64, f64);

#[derive(Debug, Clone, Copy)]
pub(crate) struct F64x3(f64, f64, f64);

macro_rules! f64x2 {
    ($a:expr, $b:expr) => {
        F64x2::from([$a, $b])
    };
    ($a:expr) => {
        F64x2::splat($a)
    };
}

macro_rules! f64x3 {
    ($a:expr, $b:expr, $c:expr) => {
        F64x3::from([$a, $b, $c])
    };
    ($a:expr) => {
        F64x3::splat($a)
    };
}

impl F64x2 {
    #[inline(always)]
    pub(crate) fn splat(a: f64) -> Self {
        Self(a, a)
    }

    #[inline(always)]
    pub(crate) fn fma(self, a: Self, b: Self) -> Self {
        use crate::internal::mul_add;
        Self(mul_add!(self.0, a.0, b.0), mul_add!(self.1, a.1, b.1))
    }

    #[inline(always)]
    pub(crate) fn abs(self) -> Self {
        Self(self.0.abs(), self.1.abs())
    }

    #[inline(always)]
    pub(crate) fn reverse(self) -> Self {
        Self(self.1, self.0)
    }

    #[inline(always)]
    pub(crate) fn product(self) -> f64 {
        self.0 * self.1
    }

    #[inline(always)]
    pub(crate) fn lt(self, other: Self) -> bool {
        self.0.lt(&other.0) && self.1.lt(&other.1)
    }
}

impl From<[f64; 2]> for F64x2 {
    #[inline(always)]
    fn from(value: [f64; 2]) -> Self {
        Self(value[0], value[1])
    }
}

impl Index<usize> for F64x2 {
    type Output = f64;

    #[inline(always)]
    fn index(&self, index: usize) -> &Self::Output {
        match index {
            0 => &self.0,
            1 => &self.1,
            _ => unreachable!(),
        }
    }
}

impl F64x3 {
    #[inline(always)]
    pub(crate) fn splat(a: f64) -> Self {
        Self(a, a, a)
    }

    #[inline(always)]
    pub(crate) fn fma(self, a: Self, b: Self) -> Self {
        use crate::internal::mul_add;
        Self(
            mul_add!(self.0, a.0, b.0),
            mul_add!(self.1, a.1, b.1),
            mul_add!(self.2, a.2, b.2),
        )
    }
}

impl From<[f64; 3]> for F64x3 {
    #[inline(always)]
    fn from(value: [f64; 3]) -> Self {
        Self(value[0], value[1], value[2])
    }
}

impl Index<usize> for F64x3 {
    type Output = f64;

    #[inline(always)]
    fn index(&self, index: usize) -> &Self::Output {
        match index {
            0 => &self.0,
            1 => &self.1,
            2 => &self.2,
            _ => unreachable!(),
        }
    }
}

macro_rules! impl_uni_ops_f64x2 {
    ($t:ident, $m:ident, $s:ident) => {
        impl $t for $s {
            type Output = $s;

            #[inline(always)]
            fn $m(self) -> Self::Output {
                $s($t::$m(self.0), $t::$m(self.1))
            }
        }
    };
}

macro_rules! impl_uni_ops_f64x3 {
    ($t:ident, $m:ident, $s:ident) => {
        impl $t for $s {
            type Output = $s;

            #[inline(always)]
            fn $m(self) -> Self::Output {
                $s($t::$m(self.0), $t::$m(self.1), $t::$m(self.2))
            }
        }
    };
}

macro_rules! impl_ops_f64x2 {
    ($t:ident, $m:ident, $s:ident, $rhs:ident) => {
        impl $t<$rhs> for $s {
            type Output = Self;

            #[inline(always)]
            fn $m(self, rhs: $rhs) -> Self::Output {
                $s($t::$m(self.0, rhs.0), $t::$m(self.1, rhs.1))
            }
        }

        impl $t<&$rhs> for $s {
            type Output = Self;

            #[inline(always)]
            fn $m(self, rhs: &$rhs) -> Self::Output {
                $s($t::$m(self.0, rhs.0), $t::$m(self.1, rhs.1))
            }
        }
    };
}

macro_rules! impl_ops_f64x3 {
    ($t:ident, $m:ident, $s:ident, $rhs:ident) => {
        impl $t<$rhs> for $s {
            type Output = Self;

            #[inline(always)]
            fn $m(self, rhs: $rhs) -> Self::Output {
                $s(
                    $t::$m(self.0, rhs.0),
                    $t::$m(self.1, rhs.1),
                    $t::$m(self.2, rhs.2),
                )
            }
        }

        impl $t<&$rhs> for $s {
            type Output = Self;

            #[inline(always)]
            fn $m(self, rhs: &$rhs) -> Self::Output {
                $s(
                    $t::$m(self.0, rhs.0),
                    $t::$m(self.1, rhs.1),
                    $t::$m(self.2, rhs.2),
                )
            }
        }
    };
}

impl_uni_ops_f64x2!(Neg, neg, F64x2);
impl_uni_ops_f64x3!(Neg, neg, F64x3);

impl_ops_f64x2!(Add, add, F64x2, F64x2);
impl_ops_f64x2!(Sub, sub, F64x2, F64x2);
impl_ops_f64x2!(Mul, mul, F64x2, F64x2);
impl_ops_f64x2!(Div, div, F64x2, F64x2);

impl_ops_f64x3!(Add, add, F64x3, F64x3);
impl_ops_f64x3!(Sub, sub, F64x3, F64x3);
impl_ops_f64x3!(Mul, mul, F64x3, F64x3);
impl_ops_f64x3!(Div, div, F64x3, F64x3);

pub(crate) use f64x2;
pub(crate) use f64x3;
