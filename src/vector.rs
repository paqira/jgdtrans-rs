use std::ops::{Add, Div, Index, Mul, Neg, Rem, Sub};

#[derive(Debug, Clone, Copy)]
pub(crate) struct Pair<T>(T, T);

#[derive(Debug, Clone, Copy)]
pub(crate) struct Triple<T>(T, T, T);

pub(crate) type F64x2 = Pair<f64>;
pub(crate) type F64x3 = Triple<f64>;

macro_rules! u8x2 {
    ($a:expr, $b:expr) => {{
        use crate::vector::Pair;
        Pair::from([$a, $b])
    }};
    ($a:expr) => {{
        use crate::vector::Pair;
        Pair::splat($a)
    }};
}

macro_rules! u32x2 {
    ($a:expr, $b:expr) => {{
        use crate::vector::Pair;
        Pair::from([$a, $b])
    }};
    ($a:expr) => {{
        use crate::vector::Pair;
        Pair::splat($a)
    }};
}

macro_rules! f64x2 {
    ($a:expr, $b:expr) => {{
        use crate::vector::Pair;
        Pair::from([$a, $b])
    }};
    ($a:expr) => {{
        use crate::vector::Pair;
        Pair::splat($a)
    }};
}

macro_rules! f64x3 {
    ($a:expr, $b:expr, $c:expr) => {{
        use crate::vector::Triple;
        Triple::from([$a, $b, $c])
    }};
    ($a:expr) => {{
        use crate::vector::Triple;
        Triple::splat($a)
    }};
}

impl<T> Pair<T> {
    #[inline(always)]
    pub(crate) const fn splat(a: T) -> Self
    where
        T: Clone + Copy,
    {
        Self(a, a)
    }

    #[inline(always)]
    pub(crate) fn cast<K>(&self) -> Pair<K>
    where
        T: Clone,
        K: From<T>,
    {
        Pair(K::from(self.0.clone()), K::from(self.1.clone()))
    }
}

impl<T> Triple<T> {
    #[inline(always)]
    pub(crate) const fn splat(a: T) -> Self
    where
        T: Clone + Copy,
    {
        Self(a, a, a)
    }
}

impl<T> From<[T; 2]> for Pair<T>
where
    T: Clone,
{
    #[inline(always)]
    fn from(value: [T; 2]) -> Self {
        Self(value[0].clone(), value[1].clone())
    }
}

impl<T> From<[T; 3]> for Triple<T>
where
    T: Clone,
{
    #[inline(always)]
    fn from(value: [T; 3]) -> Self {
        Self(value[0].clone(), value[1].clone(), value[2].clone())
    }
}

impl<T> Index<usize> for Pair<T> {
    type Output = T;

    #[inline(always)]
    fn index(&self, index: usize) -> &Self::Output {
        match index {
            0 => &self.0,
            1 => &self.1,
            _ => unreachable!(),
        }
    }
}

impl<T> Index<usize> for Triple<T> {
    type Output = T;

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

impl<T> From<Pair<T>> for (T, T) {
    #[inline(always)]
    fn from(value: Pair<T>) -> Self {
        (value.0, value.1)
    }
}

impl<T> From<Triple<T>> for (T, T, T) {
    #[inline(always)]
    fn from(value: Triple<T>) -> Self {
        (value.0, value.1, value.2)
    }
}

impl Pair<f64> {
    #[inline(always)]
    pub(crate) const fn as_u32(self) -> Pair<u32> {
        Pair(self.0 as u32, self.1 as u32)
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
    pub(crate) fn floor(self) -> Self {
        Self(self.0.floor(), self.1.floor())
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

impl Triple<f64> {
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

macro_rules! impl_unary_ops_to_pair {
    ($t:ident::$m:ident) => {
        impl<T> $t for Pair<T>
        where
            T: $t<Output = T>,
        {
            type Output = Self;

            #[inline(always)]
            fn $m(self) -> Self::Output {
                Self($t::$m(self.0), $t::$m(self.1))
            }
        }
    };
}

macro_rules! impl_unary_ops_to_triple {
    ($t:ident::$m:ident) => {
        impl<T> $t for Triple<T>
        where
            T: $t<Output = T>,
        {
            type Output = Self;

            #[inline(always)]
            fn $m(self) -> Self::Output {
                Self($t::$m(self.0), $t::$m(self.1), $t::$m(self.2))
            }
        }
    };
}

macro_rules! impl_bin_ops_to_pair {
    ($t:ident::$m:ident) => {
        impl<T> $t<Pair<T>> for Pair<T>
        where
            T: $t<Output = T>,
        {
            type Output = Self;

            #[inline(always)]
            fn $m(self, rhs: Self) -> Self::Output {
                Self($t::$m(self.0, rhs.0), $t::$m(self.1, rhs.1))
            }
        }

        impl<T> $t<&Pair<T>> for Pair<T>
        where
            T: Clone + $t<Output = T>,
        {
            type Output = Pair<T>;

            #[inline(always)]
            fn $m(self, rhs: &Self) -> Self::Output {
                Self($t::$m(self.0, rhs.0.clone()), $t::$m(self.1, rhs.1.clone()))
            }
        }
    };
}

macro_rules! impl_bin_ops_to_triple {
    ($t:ident::$m:ident) => {
        impl<T> $t<Triple<T>> for Triple<T>
        where
            T: $t<Output = T>,
        {
            type Output = Self;

            #[inline(always)]
            fn $m(self, rhs: Self) -> Self::Output {
                Self(
                    $t::$m(self.0, rhs.0),
                    $t::$m(self.1, rhs.1),
                    $t::$m(self.2, rhs.2),
                )
            }
        }

        impl<T> $t<&Triple<T>> for Triple<T>
        where
            T: Clone + $t<Output = T>,
        {
            type Output = Triple<T>;

            #[inline(always)]
            fn $m(self, rhs: &Self) -> Self::Output {
                Self(
                    $t::$m(self.0, rhs.0.clone()),
                    $t::$m(self.1, rhs.1.clone()),
                    $t::$m(self.2, rhs.2.clone()),
                )
            }
        }
    };
}

impl_unary_ops_to_pair!(Neg::neg);
impl_unary_ops_to_triple!(Neg::neg);

impl_bin_ops_to_pair!(Add::add);
impl_bin_ops_to_pair!(Sub::sub);
impl_bin_ops_to_pair!(Mul::mul);
impl_bin_ops_to_pair!(Div::div);
impl_bin_ops_to_pair!(Rem::rem);

impl_bin_ops_to_triple!(Add::add);
impl_bin_ops_to_triple!(Sub::sub);
impl_bin_ops_to_triple!(Mul::mul);
impl_bin_ops_to_triple!(Div::div);
impl_bin_ops_to_triple!(Rem::rem);

pub(crate) use f64x2;
pub(crate) use f64x3;
pub(crate) use u32x2;
pub(crate) use u8x2;
