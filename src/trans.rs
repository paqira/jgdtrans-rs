use std::collections::HashMap;
use std::error::Error;
use std::fmt::{Display, Formatter};
use std::hash::BuildHasher;

use crate::internal::mul_add;
use crate::mesh::{MeshCell, MeshCode, MeshUnit};
use crate::vector::{f64x2, f64x3, F64x2, F64x3};
use crate::{Correction, Parameter, Point, Transformer};

type Result<T> = std::result::Result<T, TransformError>;

struct Interpol<'a> {
    sw: &'a Parameter,
    se: &'a Parameter,
    nw: &'a Parameter,
    ne: &'a Parameter,
}

impl<'a> Interpol<'a> {
    #[inline(always)]
    fn from<S>(parameter: &'a HashMap<u32, Parameter, S>, cell: &MeshCell) -> Result<Self>
    where
        S: BuildHasher,
    {
        macro_rules! get {
            ($meshcode:ident, $corner:expr) => {
                parameter
                    .get(&$meshcode)
                    .ok_or(TransformError::new_pnf($meshcode, $corner))
            };
        }

        let meshcode = cell.south_west.to_meshcode();
        let sw = get!(meshcode, MeshCellCorner::SouthWest)?;

        let meshcode = cell.south_east.to_meshcode();
        let se = get!(meshcode, MeshCellCorner::SouthEast)?;

        let meshcode = cell.north_west.to_meshcode();
        let nw = get!(meshcode, MeshCellCorner::NorthWest)?;

        let meshcode = cell.north_east.to_meshcode();
        let ne = get!(meshcode, MeshCellCorner::NorthEast)?;

        Ok(Self { sw, se, nw, ne })
    }

    #[inline(always)]
    fn from_unchecked<S>(
        parameter: &'a HashMap<u32, Parameter, S>,
        code: &MeshCode,
        mesh_unit: &MeshUnit,
    ) -> Result<Self>
    where
        S: BuildHasher,
    {
        let east = code.next_east(mesh_unit);
        let north = code.next_north(mesh_unit);
        let north_east = north.next_east(mesh_unit);

        macro_rules! get {
            ($meshcode:ident, $corner:expr) => {
                parameter
                    .get(&$meshcode)
                    .ok_or(TransformError::new_pnf($meshcode, $corner))
            };
        }

        let meshcode = code.to_u32();
        let sw = get!(meshcode, MeshCellCorner::SouthWest)?;

        let meshcode = east.to_u32();
        let se = get!(meshcode, MeshCellCorner::SouthEast)?;

        let meshcode = north.to_u32();
        let nw = get!(meshcode, MeshCellCorner::NorthWest)?;

        let meshcode = north_east.to_u32();
        let ne = get!(meshcode, MeshCellCorner::NorthEast)?;

        Ok(Self { sw, se, nw, ne })
    }

    #[inline(always)]
    pub(crate) fn interpol_horizontal(&self, x: f64, y: f64, scale: f64) -> F64x2 {
        macro_rules! take {
            ($corner:ident) => {
                f64x2!(self.$corner.longitude, self.$corner.latitude)
            };
        }

        let (dx, dy) = (1. - x, 1. - y);
        let (xy, xdy, dxy, dxdy) = (x * y, x * dy, dx * y, dx * dy);

        let temp = take!(sw) * f64x2!(dxdy);
        let temp = take!(se).fma(f64x2!(xdy), temp);
        let temp = take!(nw).fma(f64x2!(dxy), temp);
        take!(ne).fma(f64x2!(xy), temp) * f64x2!(scale)
    }

    #[inline(always)]
    pub(crate) fn interpol(&self, x: f64, y: f64, scale: f64) -> F64x3 {
        macro_rules! take {
            ($corner:ident) => {
                f64x3!(
                    self.$corner.longitude,
                    self.$corner.latitude,
                    self.$corner.altitude
                )
            };
        }

        let (dx, dy) = (1. - x, 1. - y);
        let (xy, xdy, dxy, dxdy) = (x * y, x * dy, dx * y, dx * dy);

        let temp = take!(sw) * f64x3!(dxdy);
        let temp = take!(se).fma(f64x3!(xdy), temp);
        let temp = take!(nw).fma(f64x3!(dxy), temp);
        let temp = take!(ne).fma(f64x3!(xy), temp);

        temp * f64x3!(scale, scale, 1.0)
    }

    /// Diagonal part, (fy_y, fx_x), notes, first component is fy_y
    #[inline(always)]
    pub(crate) fn minus_fzz(&self, zn: F64x2, dzn: F64x2, scale: f64) -> F64x2 {
        macro_rules! comp {
            ($a:ident, $b:ident) => {
                f64x2!(self.$a.latitude, self.$b.longitude)
            };
        }

        let temp = (comp!(ne, ne) - comp!(se, nw)) * zn;
        let temp = (comp!(nw, se) - comp!(sw, sw)).fma(dzn, temp);
        temp.fma(f64x2!(scale), f64x2!(1.))
    }

    // Anti-diagonal part, (fx_y, fy_x)
    #[inline(always)]
    pub(crate) fn minus_fzw(&self, zn: F64x2, dzn: F64x2, scale: f64) -> F64x2 {
        macro_rules! comp {
            ($a:ident, $b:ident) => {
                f64x2!(self.$a.longitude, self.$b.latitude)
            };
        }

        let temp = (comp!(ne, ne) - comp!(se, nw)) * zn;
        (comp!(nw, se) - comp!(sw, sw)).fma(dzn, temp) * f64x2!(scale)
    }
}

impl<#[cfg(not(feature = "serde"))] S, #[cfg(feature = "serde")] S: Default> Transformer<S>
where
    S: BuildHasher,
{
    /// Returns the forward-transformed position.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] when fails to transform.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::collections::HashMap;
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// #
    /// // from SemiDynaEXE2023.par
    /// let tf = Transformer::new(
    ///     Format::SemiDynaEXE,
    ///     HashMap::from([
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///         (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
    ///         (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
    ///     ])
    /// );
    ///
    /// let point = Point::new(36.10377479, 140.087855041, 2.34);
    /// let result = tf.forward(&point)?;
    ///
    /// assert_eq!(result.latitude, 36.103773017086695);
    /// assert_eq!(result.longitude, 140.08785924333452);
    /// assert_eq!(result.altitude, 2.4363138578103);
    ///
    /// // Transformer::forward is equivalent to
    /// assert_eq!(result, &point + tf.forward_corr(&point)?);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[inline]
    pub fn forward(&self, point: &Point) -> Result<Point> {
        self.forward_corr(point).map(|corr| point + corr)
    }

    /// Returns the backward-transformed position compatible to the GIAJ web app/APIs.
    ///
    /// This is compatible to the GIAJ web app/APIs,
    /// and is **not** exact as the original as.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] when the transformation fails.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::collections::HashMap;
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// #
    /// // from SemiDynaEXE2023.par
    /// let tf = Transformer::new(
    ///     Format::SemiDynaEXE,
    ///     HashMap::from([
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///         (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
    ///         (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
    ///     ])
    /// );
    ///
    /// let point = Point::new(36.103773017086695, 140.08785924333452, 2.4363138578103);
    /// let result = tf.backward_compat(&point)?;
    ///
    /// assert_eq!(result.latitude, 36.10377479000002);  // exact: 36.10377479
    /// assert_eq!(result.longitude, 140.087855041);  // exact: 140.087855041
    /// assert_eq!(result.altitude, 2.339999999578243);  // exact: 2.34
    ///
    /// // Transformer::backward_compat is equivalent to
    /// assert_eq!(result, &point + tf.backward_compat_corr(&point)?);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[inline]
    pub fn backward_compat(&self, point: &Point) -> Result<Point> {
        self.backward_compat_corr(point).map(|corr| point + corr)
    }

    /// Returns the backward-transformed position.
    ///
    /// Returns [`Err`] when the error from the exact solution
    /// is larger than [`Transformer::MAX_ERROR`],
    /// that is, the result's error is suppressed under [`Transformer::MAX_ERROR`].
    ///
    /// Notes, the error is less than 1e-9 \[deg\], which is
    /// error of the GIAJ latitude and longitude parameter.
    /// This implies that altitude's error is less than 1e-5 \[m\],
    /// which is error of the GIAJ altitude parameter.
    ///
    /// This is not compatible to the GIAJ web app/APIs, but more accurate.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] when the transformation fails.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::collections::HashMap;
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// #
    /// // from SemiDynaEXE2023.par
    /// let tf = Transformer::new(
    ///     Format::SemiDynaEXE,
    ///     HashMap::from([
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///         (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
    ///         (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
    ///     ])
    /// );
    ///
    /// // In this case, no error remains
    /// let point = Point::new(36.103773017086695, 140.08785924333452, 2.4363138578103);
    /// let result = tf.backward(&point)?;
    ///
    /// assert_eq!(result.latitude, 36.10377479);  // exact: 36.10377479
    /// assert_eq!(result.longitude, 140.087855041);  // exact: 140.087855041
    /// assert_eq!(result.altitude, 2.34);  // exact: 2.34
    ///
    /// // Transformer::backward is equivalent to
    /// assert_eq!(result, &point + tf.backward_corr(&point)?);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[inline]
    pub fn backward(&self, point: &Point) -> Result<Point> {
        self.backward_corr(point).map(|corr| point + corr)
    }

    /// Unchecked forward-transformation.
    ///
    /// This does not check the bounds of `point`.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] when the transformation fails.
    ///
    /// # Safety
    ///
    /// Behavior is not specified on fail to resolve [`MeshCell`] from `point`.
    /// The safe range of `point` depends on parameter,
    /// practically, it is safe when 10 < `point.latitude()` < 60,
    /// and 110 <`point.longitude()` < 165 hold.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::collections::HashMap;
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// #
    /// // from SemiDynaEXE2023.par
    /// let tf = Transformer::new(
    ///     Format::SemiDynaEXE,
    ///     HashMap::from([
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///         (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
    ///         (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
    ///     ])
    /// );
    ///
    /// let point = Point::new(36.10377479, 140.087855041, 2.34);
    ///
    /// // Equivalent to Transformer::forward except checking
    /// assert_eq!(
    ///     tf.forward_unchecked(&point)?,
    ///     tf.forward(&point)?
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[inline]
    pub fn forward_unchecked(&self, point: &Point) -> Result<Point> {
        self.forward_corr_unchecked(point).map(|corr| point + corr)
    }

    /// Unchecked backward-transformation compatible to the GIAJ web app/APIs.
    ///
    /// This does not check the bounds of `point`.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] when the transformation fails.
    ///
    /// # Safety
    ///
    /// Behavior is not specified on fail to resolve [`MeshCell`] from `point`.
    /// The safe range of `point` depends on parameter,
    /// practically, it is safe when 10 < `point.latitude()` < 60,
    /// and 110 <`point.longitude()` < 165 hold.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::collections::HashMap;
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// #
    /// // from SemiDynaEXE2023.par
    /// let tf = Transformer::new(
    ///     Format::SemiDynaEXE,
    ///     HashMap::from([
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///         (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
    ///         (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
    ///     ])
    /// );
    ///
    /// let point = Point::new(36.103773017086695, 140.08785924333452, 2.4363138578103);
    ///
    /// // Equivalent to Transformer::backward_compat except checking
    /// assert_eq!(
    ///     tf.backward_compat_unchecked(&point)?,
    ///     tf.backward_compat(&point)?
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[inline]
    pub fn backward_compat_unchecked(&self, point: &Point) -> Result<Point> {
        self.backward_compat_corr_unchecked(point)
            .map(|corr| point + corr)
    }

    /// Unchecked backward-transformation.
    ///
    /// This does not check the bounds of `point`.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] when the transformation fails.
    ///
    /// # Safety
    ///
    /// Behavior is not specified on fail to resolve [`MeshCell`] from `point`.
    /// The safe range of `point` depends on parameter,
    /// practically, it is safe when 10 < `point.latitude()` < 60,
    /// and 110 <`point.longitude()` < 165 hold.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::collections::HashMap;
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// #
    /// // from SemiDynaEXE2023.par
    /// let tf = Transformer::new(
    ///     Format::SemiDynaEXE,
    ///     HashMap::from([
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///         (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
    ///         (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
    ///     ])
    /// );
    ///
    /// let point = Point::new(36.103773017086695, 140.08785924333452, 2.4363138578103);
    ///
    /// // Equivalent to Transformer::backward except checking
    /// assert_eq!(
    ///     tf.backward_unchecked(&point)?,
    ///     tf.backward(&point)?
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[inline]
    pub fn backward_unchecked(&self, point: &Point) -> Result<Point> {
        self.backward_corr_unchecked(point).map(|corr| point + corr)
    }

    /// Return the correction of the forward-transformation.
    ///
    /// See [`Transformer::forward`] for detail.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] when solving correction fails.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::collections::HashMap;
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// #
    /// // from SemiDynaEXE2023.par
    /// let tf = Transformer::new(
    ///     Format::SemiDynaEXE,
    ///     HashMap::from([
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///         (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
    ///         (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
    ///     ])
    /// );
    ///
    /// let origin = Point::new(36.10377479, 140.087855041, 0.0);
    /// let corr = tf.forward_corr(&origin)?;
    ///
    /// assert_eq!(corr.latitude, -1.7729133100878255e-6);
    /// assert_eq!(corr.longitude, 4.202334510058886e-6);
    /// assert_eq!(corr.altitude, 0.09631385781030005);
    ///
    /// assert_eq!(&origin + corr, tf.forward(&origin)?);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[inline]
    pub fn forward_corr(&self, point: &Point) -> Result<Correction> {
        let cell = MeshCell::try_from_point(point, self.format.mesh_unit())
            .ok_or(TransformError::new_oob())?;

        // Interpolation
        let interpol = Interpol::from(&self.parameter, &cell)?;

        // y: latitude, x: longitude
        let (y, x) = cell.position(point);

        const SCALE: f64 = 0.0002777777777777778; // 1. / 3600.

        let r = interpol.interpol(x, y, SCALE);

        Ok(Correction {
            latitude: r[1],
            longitude: r[0],
            altitude: r[2],
        })
    }

    /// Return the correction of the backward-transformation compatible to the GIAJ web app/APIs.
    ///
    /// See [`Transformer::backward_compat`] for detail.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] when solving correction fails.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::collections::HashMap;
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// #
    /// // from SemiDynaEXE2023.par
    /// let tf = Transformer::new(
    ///     Format::SemiDynaEXE,
    ///     HashMap::from([
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///         (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
    ///         (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
    ///     ])
    /// );
    ///
    /// let origin = Point::new(36.103773017086695, 140.08785924333452, 0.0);
    /// let corr = tf.backward_compat_corr(&origin)?;
    ///
    /// assert_eq!(corr.latitude, 1.7729133219831587e-6);
    /// # if cfg!(target_feature = "fma") {
    /// # assert_eq!(corr.longitude, -4.202334509042612e-6);
    /// # } else {
    /// assert_eq!(corr.longitude, -4.202334509042613e-6);
    /// # };
    /// assert_eq!(corr.altitude, -0.0963138582320569);
    ///
    /// assert_eq!(&origin + corr, tf.backward_compat(&origin)?);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn backward_compat_corr(&self, point: &Point) -> Result<Correction> {
        const DELTA: f64 = 1. / 300.; // 12. / 3600.

        let corr = Correction {
            latitude: -DELTA,
            longitude: DELTA,
            altitude: 0.0,
        };

        let temporal = point + corr;

        let corr = self.forward_corr(&temporal)?;
        let reference = point - corr;

        // actual correction
        let corr = self.forward_corr(&reference)?;
        Ok(Correction {
            latitude: -corr.latitude,
            longitude: -corr.longitude,
            altitude: -corr.altitude,
        })
    }

    /// Return the correction on the backward-transformation.
    ///
    /// See [`Transformer::backward`] for detail.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] when solving correction fails.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::collections::HashMap;
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// #
    /// // from SemiDynaEXE2023.par
    /// let tf = Transformer::new(
    ///     Format::SemiDynaEXE,
    ///     HashMap::from([
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///         (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
    ///         (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
    ///     ])
    /// );
    ///
    /// let origin = Point::new(36.103773017086695, 140.08785924333452, 0.0);
    /// let corr = tf.backward_corr(&origin)?;
    ///
    /// assert_eq!(corr.latitude, 1.7729133100878255e-6);
    /// assert_eq!(corr.longitude, -4.202334510058886e-6);
    /// assert_eq!(corr.altitude, -0.09631385781030005);
    ///
    /// assert_eq!(&origin + corr, tf.backward(&origin)?);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn backward_corr(&self, point: &Point) -> Result<Correction> {
        // Newton's Method

        const SCALE: f64 = 0.0002777777777777778; // 1. / 3600.
        const ITERATION: usize = 4;

        let p = f64x2!(point.longitude, point.latitude);
        let mut zn = f64x2!(point.longitude, point.latitude);

        for _ in 0..ITERATION {
            let current = Point::new(zn[1], zn[0], 0.0);

            let cell = MeshCell::try_from_point(&current, self.format.mesh_unit())
                .ok_or(TransformError::new_oob())?;

            let interpol = Interpol::from(&self.parameter, &cell)?;

            let (y, x) = cell.position(&current);

            let drift = interpol.interpol_horizontal(x, y, SCALE);

            let fz = p - (zn + drift);

            let dzn = f64x2!(1.) - zn;

            // (fy_y, fx_x)
            let minus_fzz = interpol.minus_fzz(zn, dzn, SCALE);

            // (fx_y, fy_x)
            let minus_fzw = interpol.minus_fzw(zn, dzn, SCALE);

            // and its determinant
            let det = mul_add!(minus_fzz[0], minus_fzz[1], -minus_fzw.product());

            // update zn
            // original, reduce sign flipping
            // zn = (fzz * fz - fzw * fz.reverse()).fma(f64x2!(-1./det), zn);
            zn = (minus_fzz * fz - minus_fzw * fz.reverse()).fma(f64x2!(1. / det), zn);

            let temp = Point::new(zn[1], zn[0], 0.0);
            let corr = self.forward_corr(&temp)?;

            let delta = p - (zn + f64x2!(corr.longitude, corr.latitude));

            if delta.abs().lt(f64x2!(Self::MAX_ERROR)) {
                return Ok(Correction {
                    latitude: -corr.latitude,
                    longitude: -corr.longitude,
                    altitude: -corr.altitude,
                });
            }
        }

        Err(TransformError::new_cnf())
    }

    /// Unchecked returning the correction of the forward-transformation.
    ///
    /// This does not check the bounds of `point`.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] when solving correction fails.
    ///
    /// # Safety
    ///
    /// Behavior is not specified on fail to resolve [`MeshCell`] from `point`.
    /// The safe range of `point` depends on parameter,
    /// practically, it is safe when 10 < `point.latitude()` < 60,
    /// and 110 <`point.longitude()` < 165 hold.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::collections::HashMap;
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// #
    /// // from SemiDynaEXE2023.par
    /// let tf = Transformer::new(
    ///     Format::SemiDynaEXE,
    ///     HashMap::from([
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///         (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
    ///         (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
    ///     ])
    /// );
    ///
    /// let origin = Point::new(36.10377479, 140.087855041, 0.0);
    /// let corr = tf.forward_corr(&origin)?;
    ///
    /// // Equivalent to Transformer::forward_corr except checking
    /// assert_eq!(
    ///     tf.forward_corr_unchecked(&origin)?,
    ///     tf.forward_corr(&origin)?
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[inline]
    pub fn forward_corr_unchecked(&self, point: &Point) -> Result<Correction> {
        let mesh_unit = self.format.mesh_unit();

        let code = MeshCode::from_point(point, &mesh_unit);

        // Interpolation
        let interpol = Interpol::from_unchecked(&self.parameter, &code, &mesh_unit)?;

        // y: latitude, x: longitude
        let (y, x) = code.position(point, &mesh_unit);

        const SCALE: f64 = 0.0002777777777777778; // 1. / 3600.

        let r = interpol.interpol(x, y, SCALE);

        Ok(Correction {
            latitude: r[1],
            longitude: r[0],
            altitude: r[2],
        })
    }

    /// Unchecked returning the correction of the backward-transformation compatible to the GIAJ web app/APIs.
    ///
    /// This does not check the bounds of `point`.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] when solving correction fails.
    ///
    /// # Safety
    ///
    /// Behavior is not specified on fail to resolve [`MeshCell`] from `point`.
    /// The safe range of `point` depends on parameter,
    /// practically, it is safe when 10 < `point.latitude()` < 60,
    /// and 110 <`point.longitude()` < 165 hold.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::collections::HashMap;
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// #
    /// // from SemiDynaEXE2023.par
    /// let tf = Transformer::new(
    ///     Format::SemiDynaEXE,
    ///     HashMap::from([
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///         (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
    ///         (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
    ///     ])
    /// );
    ///
    /// let origin = Point::new(36.103773017086695, 140.08785924333452, 0.0);
    ///
    /// // Equivalent to Transformer::backward_compat_corr except checking
    /// assert_eq!(
    ///     tf.backward_compat_corr_unchecked(&origin)?,
    ///     tf.backward_compat_corr(&origin)?,
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn backward_compat_corr_unchecked(&self, point: &Point) -> Result<Correction> {
        const DELTA: f64 = 1. / 300.; // 12. / 3600.

        let corr = Correction {
            latitude: -DELTA,
            longitude: DELTA,
            altitude: 0.0,
        };

        let temporal = point + corr;

        let corr = self.forward_corr_unchecked(&temporal)?;
        let reference = point - corr;

        // actual correction
        let corr = self.forward_corr_unchecked(&reference)?;
        Ok(Correction {
            latitude: -corr.latitude,
            longitude: -corr.longitude,
            altitude: -corr.altitude,
        })
    }

    /// Unchecked returning the correction of the backward-transformation.
    ///
    /// This does not check the bounds of `point`.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] when solving correction fails.
    ///
    /// # Safety
    ///
    /// Behavior is not specified on fail to resolve [`MeshCell`] from `point`.
    /// The safe range of `point` depends on parameter,
    /// practically, it is safe when 10 < `point.latitude()` < 60,
    /// and 110 <`point.longitude()` < 165 hold.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::collections::HashMap;
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// #
    /// // from SemiDynaEXE2023.par
    /// let tf = Transformer::new(
    ///     Format::SemiDynaEXE,
    ///     HashMap::from([
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///         (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
    ///         (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
    ///     ])
    /// );
    ///
    /// let origin = Point::new(36.103773017086695, 140.08785924333452, 0.0);
    ///
    /// // Equivalent to Transformer::backward_corr except checking
    /// assert_eq!(
    ///     tf.backward_corr_unchecked(&origin)?,
    ///     tf.backward_corr(&origin)?
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn backward_corr_unchecked(&self, point: &Point) -> Result<Correction> {
        // See backward_corr for detail
        let mesh_unit = self.format.mesh_unit();

        const SCALE: f64 = 0.0002777777777777778; // 1. / 3600.
        const ITERATION: usize = 4;

        let p = f64x2!(point.longitude, point.latitude);
        let mut zn = f64x2!(point.longitude, point.latitude);

        for _ in 0..ITERATION {
            let current = Point::new(zn[1], zn[0], 0.0);

            let code = MeshCode::from_point(&current, &mesh_unit);

            let interpol = Interpol::from_unchecked(&self.parameter, &code, &mesh_unit)?;

            let (y, x) = code.position(&current, &mesh_unit);

            let drift = interpol.interpol_horizontal(x, y, SCALE);

            let fz = p - (zn + drift);

            let dzn = f64x2!(1.) - zn;

            // (fy_y, fx_x)
            let minus_fzz = interpol.minus_fzz(zn, dzn, SCALE);

            // (fx_y, fy_x)
            let minus_fzw = interpol.minus_fzw(zn, dzn, SCALE);

            // and its determinant
            let det = mul_add!(minus_fzz[0], minus_fzz[1], -minus_fzw.product());

            // update zn
            // original, reduce sign flipping
            // zn = (fzz * fz - fzw * fz.reverse()).fma(f64x2!(-1./det), zn);
            zn = (minus_fzz * fz - minus_fzw * fz.reverse()).fma(f64x2!(1. / det), zn);

            let temp = Point::new(zn[1], zn[0], 0.0);
            let corr = self.forward_corr_unchecked(&temp)?;

            let delta = p - (zn + f64x2!(corr.longitude, corr.latitude));

            if delta.abs().lt(f64x2!(Self::MAX_ERROR)) {
                return Ok(Correction {
                    latitude: -corr.latitude,
                    longitude: -corr.longitude,
                    altitude: -corr.altitude,
                });
            }
        }

        Err(TransformError::new_cnf())
    }
}

//
// Error
//

/// An error which can be returned on coordinate transforming.
///
/// This error is used as the error type for the [`Transformer::forward`],
/// [`Transformer::forward_corr`] etc.
#[derive(Debug, PartialEq, Eq)]
pub struct TransformError {
    kind: TransformErrorKind,
}

/// An error kind used by [`TransformError`].
#[derive(Debug, PartialEq, Eq)]
pub enum TransformErrorKind {
    ParameterNotFound {
        /// Meshcode where the parameter not found
        meshcode: u32,
        /// Corner of the [`MeshCell`] where the parameter not found
        corner: MeshCellCorner,
    },
    CorrectionNotFound,
    OutOfBounds,
}

/// An error corner of mesh used by [`TransformErrorKind`].
#[derive(Debug, PartialEq, Eq)]
pub enum MeshCellCorner {
    NorthWest,
    NorthEast,
    SouthWest,
    SouthEast,
}

impl TransformError {
    #[cold]
    const fn new_pnf(meshcode: u32, corner: MeshCellCorner) -> Self {
        Self {
            kind: TransformErrorKind::ParameterNotFound { meshcode, corner },
        }
    }

    #[cold]
    const fn new_cnf() -> Self {
        Self {
            kind: TransformErrorKind::CorrectionNotFound,
        }
    }

    #[cold]
    const fn new_oob() -> Self {
        Self {
            kind: TransformErrorKind::OutOfBounds,
        }
    }

    /// Returns the detailed cause.
    pub const fn kind(&self) -> &TransformErrorKind {
        &self.kind
    }
}

impl Error for TransformError {}

impl Display for TransformError {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        match &self.kind {
            TransformErrorKind::ParameterNotFound { meshcode, corner } => {
                write!(f, "parameter not found: {} at {}", meshcode, corner)
            }
            TransformErrorKind::CorrectionNotFound => f.write_str("correction not found"),
            TransformErrorKind::OutOfBounds => {
                f.write_str("position is out-of-bounds of transformation")
            }
        }
    }
}

impl Display for MeshCellCorner {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        match self {
            Self::NorthWest => f.write_str("north-west"),
            Self::NorthEast => f.write_str("north-east"),
            Self::SouthWest => f.write_str("south-west"),
            Self::SouthEast => f.write_str("south-east"),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{Format, TransformerBuilder};

    use super::*;

    mod test_transformer {
        use super::*;

        const TKY2JGD: [(u32, (f64, f64, f64)); 7] = [
            // forward
            (54401027, (11.49105, -11.80078, 0.0)),
            (54401027, (11.49105, -11.80078, 0.0)),
            (54401037, (11.48732, -11.80198, 0.0)),
            (54401028, (11.49096, -11.80476, 0.0)),
            (54401038, (11.48769, -11.80555, 0.0)),
            // backward
            (54401047, (11.48373, -11.80318, 0.0)),
            (54401048, (11.48438, -11.80689, 0.0)),
        ];

        #[allow(non_upper_case_globals)]
        const PatchJGD_HV: [(u32, (f64, f64, f64)); 6] = [
            // forward
            (57413454, (-0.05984, 0.22393, -1.25445)),
            (57413464, (-0.06011, 0.22417, -1.24845)),
            (57413455, (-0.0604, 0.2252, -1.29)),
            (57413465, (-0.06064, 0.22523, -1.27667)),
            // backward
            (57413474, (-0.06037, 0.22424, -0.35308)),
            (57413475, (-0.06089, 0.22524, 0.0)),
        ];

        #[allow(non_upper_case_globals)]
        const SemiDynaEXE: [(u32, (f64, f64, f64)); 4] = [
            (54401005, (-0.00622, 0.01516, 0.0946)),
            (54401055, (-0.0062, 0.01529, 0.08972)),
            (54401100, (-0.00663, 0.01492, 0.10374)),
            (54401150, (-0.00664, 0.01506, 0.10087)),
        ];

        #[test]
        #[allow(non_snake_case)]
        fn test_vs_TKY2JGD_web_app() {
            // v.s. web

            let tf = TransformerBuilder::new()
                .format(Format::TKY2JGD)
                .parameters(TKY2JGD)
                .build();

            const DELTA: f64 = 0.00000001;

            // 国土地理院
            let origin = Point::new(36.103774791666666, 140.08785504166664, 0.0);
            let actual = tf.forward(&origin).unwrap();

            assert!((36.106966281 - actual.latitude).abs() < DELTA);
            assert!((140.084576867 - actual.longitude).abs() < DELTA);
            assert_eq!(0.0, actual.altitude);

            let origin = Point::new(36.10696628160147, 140.08457686629436, 0.0);
            let actual = tf.backward_compat(&origin).unwrap();
            assert!((36.103774792 - actual.latitude).abs() < DELTA);
            assert!((140.087855042 - actual.longitude).abs() < DELTA);
            assert_eq!(0.0, actual.altitude);
        }

        #[test]
        #[allow(non_snake_case)]
        fn test_vs_PatchJGD_HV_web_app() {
            // v.s. web

            let tf = TransformerBuilder::new()
                .format(Format::PatchJGD_HV)
                .parameters(PatchJGD_HV)
                .build();

            const DELTA: f64 = 0.00000001;

            // 金華山黄金山神社
            let origin = Point::new(38.2985120586605, 141.5559006163195, 0.);
            let actual = tf.forward(&origin).unwrap();
            assert!((38.298495306 - actual.latitude).abs() < DELTA);
            assert!((141.555963019 - actual.longitude).abs() < DELTA);
            assert!((-1.263 - actual.altitude).abs() < 0.001);

            let origin = Point::new(38.29849530463122, 141.55596301776936, 0.0);
            let actual = tf.backward_compat(&origin).unwrap();
            assert!((38.298512058 - actual.latitude).abs() < DELTA);
            assert!((141.555900614 - actual.longitude).abs() < DELTA);
            assert!((1.264 - actual.altitude).abs() < 0.001);
        }

        #[test]
        #[allow(non_snake_case)]
        fn test_vs_SemiDynaEXE_web_app() {
            // v.s. web

            let tf = TransformerBuilder::new()
                .format(Format::SemiDynaEXE)
                .parameters(SemiDynaEXE)
                .build();

            const DELTA: f64 = 0.00000001;

            // 国土地理院
            let origin = Point::new(36.103774791666666, 140.08785504166664, 0.);
            let actual = tf.forward(&origin).unwrap();
            assert!((36.103773019 - actual.latitude).abs() < DELTA);
            assert!((140.087859244 - actual.longitude).abs() < DELTA);
            assert!((0.096 - actual.altitude).abs() < 0.001);

            let origin = Point::new(36.10377301875336, 140.08785924400115, 0.);
            let actual = tf.backward_compat(&origin).unwrap();
            assert!((36.103774792 - actual.latitude).abs() < DELTA);
            assert!((140.087855042 - actual.longitude).abs() < DELTA);
            assert!((-0.096 - actual.altitude).abs() < 0.001);
        }

        #[test]
        #[allow(non_snake_case)]
        fn test_vs_SemiDynaEXE_exact_result() {
            // v.s. exact (decimal trans)

            let tf = TransformerBuilder::new()
                .format(Format::SemiDynaEXE)
                .parameters(SemiDynaEXE)
                .build();

            const DELTA: f64 = 0.0000000000001;

            // 国土地理院
            let origin = Point::new(36.103774791666666, 140.08785504166664, 0.0);
            let actual = tf.forward(&origin).unwrap();
            assert!((36.10377301875335 - actual.latitude).abs() < DELTA);
            assert!((140.08785924400115 - actual.longitude).abs() < DELTA);
            assert!((0.09631385775572238 - actual.altitude).abs() < DELTA);

            let actual = tf.backward_compat(&actual).unwrap();
            assert!((36.10377479166668 - actual.latitude).abs() < DELTA);
            assert!((140.08785504166664 - actual.longitude).abs() < DELTA);
            assert!((-4.2175864502150125955e-10 - actual.altitude).abs() < DELTA);
        }

        #[test]
        fn test_forward_and_corr_unchecked() {
            // unchecked should return same result as checked

            // TKY2JGD
            let tf = TransformerBuilder::new()
                .format(Format::TKY2JGD)
                .parameters(TKY2JGD)
                .build();

            let origin = Point::new(36.103774791666666, 140.08785504166664, 0.0);
            assert_eq!(
                tf.forward_unchecked(&origin).unwrap(),
                tf.forward(&origin).unwrap()
            );
            assert_eq!(
                tf.forward_corr_unchecked(&origin).unwrap(),
                tf.forward_corr(&origin).unwrap()
            );

            // SemiDynaEXE
            let tf = TransformerBuilder::new()
                .format(Format::SemiDynaEXE)
                .parameters(SemiDynaEXE)
                .build();

            let origin = Point::new(36.103774791666666, 140.08785504166664, 0.0);
            assert_eq!(
                tf.forward_unchecked(&origin).unwrap(),
                tf.forward(&origin).unwrap()
            );
            assert_eq!(
                tf.forward_corr_unchecked(&origin).unwrap(),
                tf.forward_corr(&origin).unwrap()
            );
        }

        #[test]
        fn test_backward_compat_and_corr_unchecked() {
            // unchecked should return same result as checked

            // TKY2JGD
            let tf = TransformerBuilder::new()
                .format(Format::TKY2JGD)
                .parameters(TKY2JGD)
                .build();

            let origin = Point::new(36.103774791666666, 140.08785504166664, 0.0);
            assert_eq!(
                tf.backward_compat_unchecked(&origin).unwrap(),
                tf.backward_compat(&origin).unwrap()
            );
            assert_eq!(
                tf.backward_compat_corr_unchecked(&origin).unwrap(),
                tf.backward_compat_corr(&origin).unwrap()
            );

            // SemiDynaEXE
            let tf = TransformerBuilder::new()
                .format(Format::SemiDynaEXE)
                .parameters(SemiDynaEXE)
                .build();

            let origin = Point::new(36.103774791666666, 140.08785504166664, 0.0);
            assert_eq!(
                tf.backward_compat_unchecked(&origin).unwrap(),
                tf.backward_compat(&origin).unwrap()
            );
            assert_eq!(
                tf.backward_compat_corr_unchecked(&origin).unwrap(),
                tf.backward_compat_corr(&origin).unwrap()
            );
        }

        #[test]
        fn test_backward_checked_and_corr_unchecked() {
            // unchecked should return same result as checked

            // TKY2JGD
            let tf = TransformerBuilder::new()
                .format(Format::TKY2JGD)
                .parameters(TKY2JGD)
                .build();

            let origin = Point::new(36.103774791666666, 140.08785504166664, 0.0);
            assert_eq!(
                tf.backward_unchecked(&origin).unwrap(),
                tf.backward(&origin).unwrap()
            );
            assert_eq!(
                tf.backward_corr_unchecked(&origin).unwrap(),
                tf.backward_corr(&origin).unwrap()
            );

            // SemiDynaEXE
            let tf = TransformerBuilder::new()
                .format(Format::SemiDynaEXE)
                .parameters(SemiDynaEXE)
                .build();

            let origin = Point::new(36.103774791666666, 140.08785504166664, 0.0);
            assert_eq!(
                tf.backward_unchecked(&origin).unwrap(),
                tf.backward(&origin).unwrap()
            );
            assert_eq!(
                tf.backward_corr_unchecked(&origin).unwrap(),
                tf.backward_corr(&origin).unwrap()
            );
        }
    }

    // To detect regression when change codes
    // The expected is snapshots of 2a4a555c
    // that is no fma, no x / 2 to x * 0.5, and no vector.rs impl.
    // Few upl different does not affect actual transformation result *practically*,
    // because they will be rounded (Japan locates 10 < lat and 100 < lng).
    mod test_sampling {
        use super::*;

        macro_rules! assert_1ulp {
            ($a:expr, $e:expr) => {
                assert!(
                    $e.latitude.next_down() <= $a.latitude && $a.latitude <= $e.latitude.next_up(),
                    "left: {} ({:#x}), right: {} ({:#x})",
                    $a.latitude,
                    $a.latitude.to_bits(),
                    $e.latitude,
                    $e.latitude.to_bits()
                );
                assert!(
                    $e.longitude.next_down() <= $a.longitude
                        && $a.longitude <= $e.longitude.next_up(),
                    "left: {} ({:#x}), right: {} ({:#x})",
                    $a.longitude,
                    $a.longitude.to_bits(),
                    $e.longitude,
                    $e.longitude.to_bits()
                );
                assert_eq!($a.altitude, $e.altitude);
            };
        }

        macro_rules! assert_2ulp {
            ($a:expr, $e:expr) => {
                assert!(
                    $e.latitude.next_down().next_down() <= $a.latitude
                        && $a.latitude <= $e.latitude.next_up().next_up(),
                    "e: 0x{:>08x}, a: 0x{:>08x}",
                    $e.latitude.to_bits(),
                    $a.latitude.to_bits()
                );
                assert!(
                    $e.longitude.next_down().next_down() <= $a.longitude
                        && $a.longitude <= $e.longitude.next_up().next_up(),
                    "e: 0x{:>08x}, a: 0x{:>08x}",
                    $e.longitude.to_bits(),
                    $a.longitude.to_bits()
                );
                assert_eq!($a.altitude, $e.altitude);
            };
        }

        // maximally distorted area
        mod param {
            // 硫黄島
            pub(crate) const TKY2JGD: [(u32, (f64, f64, f64)); 42] = [
                (37411203, (-9.52837, -5.16455, 0.0)),
                (37411204, (-9.48474, -5.166, 0.0)),
                (37411205, (-9.44931, -5.17455, 0.0)),
                (37411213, (-9.50037, -5.15423, 0.0)),
                (37411214, (-9.46621, -5.15711, 0.0)),
                (37411215, (-9.43059, -5.16765, 0.0)),
                (37411216, (-9.40825, -5.18744, 0.0)),
                (37411223, (-9.47502, -5.1445, 0.0)),
                (37411224, (-9.44259, -5.14566, 0.0)),
                (37411225, (-9.40722, -5.15792, 0.0)),
                (37411226, (-9.38735, -5.18644, 0.0)),
                (37411227, (-9.38775, -5.21138, 0.0)),
                (37411233, (-9.45369, -5.13668, 0.0)),
                (37411234, (-9.42005, -5.13407, 0.0)),
                (37411235, (-9.38247, -5.14378, 0.0)),
                (37411236, (-9.364, -5.18873, 0.0)),
                (37411237, (-9.37762, -5.21806, 0.0)),
                (37411243, (-9.43773, -5.13258, 0.0)),
                (37411244, (-9.40413, -5.12776, 0.0)),
                (37411245, (-9.36214, -5.12119, 0.0)),
                (37411246, (-9.33996, -5.20052, 0.0)),
                (37411247, (-9.37717, -5.22604, 0.0)),
                (37411253, (-9.4277, -5.13309, 0.0)),
                (37411254, (-9.39791, -5.13202, 0.0)),
                (37411255, (-9.36825, -5.14449, 0.0)),
                (37411256, (-9.36051, -5.19407, 0.0)),
                (37411257, (-9.39197, -5.23339, 0.0)),
                (37411263, (-9.42283, -5.13711, 0.0)),
                (37411264, (-9.3986, -5.14132, 0.0)),
                (37411265, (-9.37843, -5.15845, 0.0)),
                (37411266, (-9.37533, -5.1934, 0.0)),
                (37411267, (-9.38992, -5.22429, 0.0)),
                (37411273, (-9.42162, -5.14271, 0.0)),
                (37411274, (-9.40246, -5.15024, 0.0)),
                (37411275, (-9.38809, -5.1673, 0.0)),
                (37411276, (-9.38547, -5.19356, 0.0)),
                (37411277, (-9.3923, -5.2181, 0.0)),
                (37411283, (-9.42275, -5.14855, 0.0)),
                (37411284, (-9.40749, -5.15758, 0.0)),
                (37411285, (-9.39659, -5.17323, 0.0)),
                (37411286, (-9.39344, -5.19417, 0.0)),
                (37411287, (-9.39669, -5.2141, 0.0)),
            ];

            // 金剛寺
            #[allow(non_upper_case_globals)]
            pub(crate) const PatchJGD: [(u32, (f64, f64, f64)); 20] = [
                (57413434, (-0.05924, 0.22287, 0.0)),
                (57413435, (-0.05974, 0.2238, 0.0)),
                (57413436, (-0.06018, 0.22434, 0.0)),
                (57413437, (-0.06057, 0.22463, 0.0)),
                (57413444, (-0.05955, 0.22348, 0.0)),
                (57413445, (-0.06007, 0.22451, 0.0)),
                (57413446, (-0.0605, 0.22497, 0.0)),
                (57413447, (-0.06088, 0.22518, 0.0)),
                (57413454, (-0.05984, 0.22393, 0.0)),
                (57413455, (-0.0604, 0.2252, 0.0)),
                (57413456, (-0.0608, 0.22545, 0.0)),
                (57413457, (-0.06117, 0.22562, 0.0)),
                (57413464, (-0.06011, 0.22417, 0.0)),
                (57413465, (-0.06064, 0.22523, 0.0)),
                (57413466, (-0.06107, 0.22572, 0.0)),
                (57413467, (-0.06146, 0.22595, 0.0)),
                (57413474, (-0.06037, 0.22424, 0.0)),
                (57413475, (-0.06089, 0.22524, 0.0)),
                (57413476, (-0.06134, 0.22585, 0.0)),
                (57413477, (-0.06173, 0.22617, 0.0)),
            ];
        }

        // randomly sampling points
        mod origin {
            use super::*;

            pub(crate) const TKY2JGD: [Point; 40] = [
                Point::new(24.798290751134598, 141.3092768564055, 0.0),
                Point::new(24.776992362241682, 141.2957020875077, 0.0),
                Point::new(24.788118554416414, 141.29898410056833, 0.0),
                Point::new(24.798235275783192, 141.3266731395085, 0.0),
                Point::new(24.798058446159867, 141.31321388872777, 0.0),
                Point::new(24.796644681979227, 141.3228919280988, 0.0),
                Point::new(24.793579980932243, 141.32424155831634, 0.0),
                Point::new(24.786255806314095, 141.30818909716402, 0.0),
                Point::new(24.78993679066769, 141.32869108860442, 0.0),
                Point::new(24.788834601117944, 141.32468254434286, 0.0),
                Point::new(24.79874479040802, 141.33546685599055, 0.0),
                Point::new(24.796000572815707, 141.33166238497353, 0.0),
                Point::new(24.793671689443524, 141.30768027721874, 0.0),
                Point::new(24.797617850757536, 141.3164020097272, 0.0),
                Point::new(24.76987596694603, 141.31577548648312, 0.0),
                Point::new(24.773162494661474, 141.33025776990172, 0.0),
                Point::new(24.77648478415442, 141.3078617313661, 0.0),
                Point::new(24.78002879231921, 141.30817494436678, 0.0),
                Point::new(24.79862854689639, 141.31198846489906, 0.0),
                Point::new(24.793770393958578, 141.2965315249094, 0.0),
                Point::new(24.785969281563226, 141.32229963191577, 0.0),
                Point::new(24.79093502301227, 141.30627968578676, 0.0),
                Point::new(24.77554194881383, 141.32051272892983, 0.0),
                Point::new(24.79809948351226, 141.3170321747806, 0.0),
                Point::new(24.79313940841349, 141.329310015945, 0.0),
                Point::new(24.799331821736533, 141.319467447338, 0.0),
                Point::new(24.78453600572179, 141.3233174144879, 0.0),
                Point::new(24.79245500153927, 141.32383477232435, 0.0),
                Point::new(24.7853452020542, 141.31235212566133, 0.0),
                Point::new(24.796000054489724, 141.3046077435609, 0.0),
                Point::new(24.795676247270556, 141.33077800568157, 0.0),
                Point::new(24.78574286806258, 141.30707955610401, 0.0),
                Point::new(24.769350256959537, 141.3169685630857, 0.0),
                Point::new(24.773545879608932, 141.3217284222138, 0.0),
                Point::new(24.794711546614124, 141.3161942411729, 0.0),
                Point::new(24.793539358633474, 141.33239060465922, 0.0),
                Point::new(24.779619552875534, 141.32559975003764, 0.0),
                Point::new(24.77739829743626, 141.30236135418414, 0.0),
                Point::new(24.773121933792915, 141.31296442626453, 0.0),
                Point::new(24.79577846634706, 141.32130844832952, 0.0),
            ];

            #[allow(non_upper_case_globals)]
            pub(crate) const PatchJGD: [Point; 40] = [
                Point::new(38.29366648184684, 141.57218911318597, 0.0),
                Point::new(38.29524750505648, 141.565951814976, 0.0),
                Point::new(38.28915479765745, 141.56079323763166, 0.0),
                Point::new(38.297513747823075, 141.55984791630456, 0.0),
                Point::new(38.297007281172434, 141.5746649204517, 0.0),
                Point::new(38.29829825378931, 141.56072587586758, 0.0),
                Point::new(38.282415662326834, 141.57402956317543, 0.0),
                Point::new(38.291308839971855, 141.57109017536575, 0.0),
                Point::new(38.287977577974964, 141.55866958172842, 0.0),
                Point::new(38.30091699112494, 141.5643922697493, 0.0),
                Point::new(38.29279324093365, 141.56306228386993, 0.0),
                Point::new(38.286837780670275, 141.56928026805485, 0.0),
                Point::new(38.2860438423304, 141.56801950212866, 0.0),
                Point::new(38.29792409516659, 141.5622524433344, 0.0),
                Point::new(38.30300649955924, 141.56104080525452, 0.0),
                Point::new(38.28914067031325, 141.56238204898824, 0.0),
                Point::new(38.28171743867986, 141.56765553046435, 0.0),
                Point::new(38.30157113957333, 141.56413577139742, 0.0),
                Point::new(38.30348165284211, 141.56767483299026, 0.0),
                Point::new(38.295223833911066, 141.566301690163, 0.0),
                Point::new(38.28533589095024, 141.5695980435206, 0.0),
                Point::new(38.30318722327355, 141.5765931735851, 0.0),
                Point::new(38.30177973315218, 141.5695502689466, 0.0),
                Point::new(38.28928124097101, 141.5626725130587, 0.0),
                Point::new(38.29237043182264, 141.5593835313238, 0.0),
                Point::new(38.28361764109154, 141.56394270141877, 0.0),
                Point::new(38.30262467419498, 141.57191624504966, 0.0),
                Point::new(38.29972185146991, 141.56412159071996, 0.0),
                Point::new(38.30334459979315, 141.57355894182143, 0.0),
                Point::new(38.28104546751318, 141.56899076582783, 0.0),
                Point::new(38.2945432168755, 141.56563651301778, 0.0),
                Point::new(38.29867420807941, 141.56744030102118, 0.0),
                Point::new(38.302209007855474, 141.57657802410878, 0.0),
                Point::new(38.29486900681201, 141.57558289020673, 0.0),
                Point::new(38.29349642206837, 141.57070332133043, 0.0),
                Point::new(38.286703576574766, 141.55832263592652, 0.0),
                Point::new(38.30035172054504, 141.57192705645912, 0.0),
                Point::new(38.28752088543183, 141.57277468859644, 0.0),
                Point::new(38.301609894209, 141.5673646322615, 0.0),
                Point::new(38.292785674864675, 141.56157144988188, 0.0),
            ];
        }

        #[allow(non_snake_case)]
        mod PatchJGD {
            use super::*;

            #[test]
            fn test_forward_corr_and_one_unchecked() {
                let tf = TransformerBuilder::new()
                    .format(Format::PatchJGD)
                    .parameters(param::PatchJGD)
                    .build();

                let _ = origin::PatchJGD
                    .iter()
                    .zip([
                        Correction::new(-0.0000168814518646117, 0.00006262378469612878, 0.0),
                        Correction::new(-0.000016838096116009317, 0.00006258622379442354, 0.0),
                        Correction::new(-0.000016729364806643504, 0.00006245235772614292, 0.0),
                        Correction::new(-0.0000167927912747071, 0.00006249523883252357, 0.0),
                        Correction::new(-0.000016933832772111427, 0.00006267005867786031, 0.0),
                        Correction::new(-0.000016809693706255367, 0.00006251870596206315, 0.0),
                        Correction::new(-0.000016786470254049566, 0.00006246228557241947, 0.0),
                        Correction::new(-0.00001685044470202184, 0.00006259677006272436, 0.0),
                        Correction::new(-0.000016691037655080527, 0.00006237164728172895, 0.0),
                        Correction::new(-0.00001687026026957804, 0.00006258535452990637, 0.0),
                        Correction::new(-0.000016791839127120513, 0.0000625602113400046, 0.0),
                        Correction::new(-0.00001678754837251092, 0.00006250049437271753, 0.0),
                        Correction::new(-0.000016767471766493994, 0.0000624742742034364, 0.0),
                        Correction::new(-0.000016824880426055778, 0.00006255569386298114, 0.0),
                        Correction::new(-0.000016852429524480752, 0.00006253122084345232, 0.0),
                        Correction::new(-0.00001674855576375182, 0.00006249431948380992, 0.0),
                        Correction::new(-0.000016717822382203087, 0.00006238012426291427, 0.0),
                        Correction::new(-0.00001687330504669575, 0.00006258304674313023, 0.0),
                        Correction::new(-0.00001692386752743053, 0.00006262716305232194, 0.0),
                        Correction::new(-0.000016841109776999462, 0.00006258888810224698, 0.0),
                        Correction::new(-0.000016774827854804727, 0.00006247454551726284, 0.0),
                        Correction::new(-0.000017006381402755156, 0.00006272317286004788, 0.0),
                        Correction::new(-0.00001692731399584028, 0.00006264526695962974, 0.0),
                        Correction::new(-0.000016753104465902736, 0.00006250187962000352, 0.0),
                        Correction::new(-0.000016744800638686603, 0.00006246953387593844, 0.0),
                        Correction::new(-0.00001670299149631201, 0.00006238494588595516, 0.0),
                        Correction::new(-0.000016957612292787124, 0.0000626752048905101, 0.0),
                        Correction::new(-0.000016857678372970727, 0.00006258097939396365, 0.0),
                        Correction::new(-0.000016979963121522515, 0.00006269725941925794, 0.0),
                        Correction::new(-0.000016723363460589664, 0.00006237926078210378, 0.0),
                        Correction::new(-0.000016829392082136185, 0.00006258163147387824, 0.0),
                        Correction::new(-0.000016880521445054468, 0.00006261216560671094, 0.0),
                        Correction::new(-0.000016997446168531008, 0.00006271847443216636, 0.0),
                        Correction::new(-0.000016922602155685813, 0.00006265632174901151, 0.0),
                        Correction::new(-0.000016866535038538763, 0.00006261256576411896, 0.0),
                        Correction::new(-0.000016673410292616015, 0.00006233677887217235, 0.0),
                        Correction::new(-0.000016937633047476755, 0.00006266771732002265, 0.0),
                        Correction::new(-0.000016826912478390445, 0.000062541138292727, 0.0),
                        Correction::new(-0.00001690476217566123, 0.00006261990205433083, 0.0),
                        Correction::new(-0.00001677525767741847, 0.00006253105068688413, 0.0),
                    ])
                    .map(|(o, e)| {
                        assert_1ulp!(tf.forward_corr(o).unwrap(), e);
                        assert_1ulp!(tf.forward_corr_unchecked(o).unwrap(), e);
                    })
                    .collect::<Vec<_>>();
            }

            #[test]
            fn test_backward_corr_and_one_unchecked() {
                let tf = TransformerBuilder::new()
                    .format(Format::PatchJGD)
                    .parameters(param::PatchJGD)
                    .build();

                let _ = origin::PatchJGD
                    .iter()
                    .zip([
                        Correction::new(0.000016881033241320934, -0.00006262347752156904, 0.0),
                        Correction::new(0.000016837661135768983, -0.00006258578602582213, 0.0),
                        Correction::new(0.000016728785230206754, -0.00006245106143461017, 0.0),
                        Correction::new(0.000016792180791664592, -0.00006249372206713576, 0.0),
                        Correction::new(0.000016933400794840183, -0.00006266964439879499, 0.0),
                        Correction::new(0.00001680908582386808, -0.00006251720785453752, 0.0),
                        Correction::new(0.000016786051380071508, -0.00006246199104980874, 0.0),
                        Correction::new(0.00001685006035030561, -0.00006259671684473942, 0.0),
                        Correction::new(0.000016690462698007165, -0.0000623703766068834, 0.0),
                        Correction::new(0.000016869801405394748, -0.00006258467018824143, 0.0),
                        Correction::new(0.00001679141240396685, -0.00006255984084091554, 0.0),
                        Correction::new(0.000016787144306549254, -0.00006250030108892116, 0.0),
                        Correction::new(0.000016767065456870475, -0.00006247406481154251, 0.0),
                        Correction::new(0.00001682426829999102, -0.00006255416739118313, 0.0),
                        Correction::new(0.000016851839191586866, -0.00006252978771918586, 0.0),
                        Correction::new(0.00001674797881609922, -0.0000624930400893337, 0.0),
                        Correction::new(0.000016717405241115722, -0.00006237984257960845, 0.0),
                        Correction::new(0.00001687284381628209, -0.0000625823479451207, 0.0),
                        Correction::new(0.00001692340311051274, -0.00006262644467222453, 0.0),
                        Correction::new(0.00001684067538709154, -0.00006258845504137657, 0.0),
                        Correction::new(0.000016774415964032874, -0.00006247429667354218, 0.0),
                        Correction::new(0.00001700599085834298, -0.00006272288423664311, 0.0),
                        Correction::new(0.000016926856811114192, -0.00006264459264402127, 0.0),
                        Correction::new(0.000016752721099067026, -0.00006250183317576118, 0.0),
                        Correction::new(0.000016744164989722545, -0.00006246784206592653, 0.0),
                        Correction::new(0.00001670257867884075, -0.00006238468935680436, 0.0),
                        Correction::new(0.00001695715439834229, -0.00006267452620205597, 0.0),
                        Correction::new(0.000016857218735755157, -0.00006258034278059709, 0.0),
                        Correction::new(0.0000169795042909641, -0.00006269657502812293, 0.0),
                        Correction::new(0.00001672294467487681, -0.00006237896552734444, 0.0),
                        Correction::new(0.000016828960173364332, -0.00006258121852575973, 0.0),
                        Correction::new(0.000016880071424597896, -0.00006261160653720872, 0.0),
                        Correction::new(0.000016997055584293922, -0.00006271820045696052, 0.0),
                        Correction::new(0.000016922229050867552, -0.00006265620665297306, 0.0),
                        Correction::new(0.000016866115233096053, -0.00006261224933610758, 0.0),
                        Correction::new(0.00001667284342270606, -0.00006233555586070582, 0.0),
                        Correction::new(0.00001693718265533069, -0.00006266708429165561, 0.0),
                        Correction::new(0.000016826507161269037, -0.00006254093642788775, 0.0),
                        Correction::new(0.00001690430363619336, -0.00006261921955197253, 0.0),
                        Correction::new(0.00001677462065901357, -0.00006252935123792957, 0.0),
                    ])
                    .map(|(o, e)| {
                        if cfg!(target_feature = "fma") {
                            assert_2ulp!(tf.backward_corr(o).unwrap(), e);
                            assert_2ulp!(tf.backward_corr_unchecked(o).unwrap(), e);
                        } else {
                            assert_1ulp!(tf.backward_corr(o).unwrap(), e);
                            assert_1ulp!(tf.backward_corr_unchecked(o).unwrap(), e);
                        }
                    })
                    .collect::<Vec<_>>();
            }

            #[test]
            fn test_identity() {
                // test transformation not corr

                let tf = TransformerBuilder::new()
                    .format(Format::PatchJGD)
                    .parameters(param::PatchJGD)
                    .build();

                let _ = origin::PatchJGD
                    .iter()
                    .map(|o| {
                        assert_eq!(&tf.backward(&tf.forward(o).unwrap()).unwrap(), o);
                        assert_eq!(&tf.forward(&tf.backward(o).unwrap()).unwrap(), o);
                    })
                    .collect::<Vec<_>>();
            }
        }

        #[allow(non_snake_case)]
        mod TKY2JGD {
            use super::*;

            #[test]
            fn test_forward_corr_and_one_unchecked() {
                let tf = TransformerBuilder::new()
                    .format(Format::TKY2JGD)
                    .parameters(param::TKY2JGD)
                    .build();

                let _ = origin::TKY2JGD
                    .iter()
                    .zip([
                        Correction::new(-0.0026061235422512844, -0.0014309489244044126, 0.0),
                        Correction::new(-0.002618835290300369, -0.0014260112388935016, 0.0),
                        Correction::new(-0.0026119753448954203, -0.001425117480254691, 0.0),
                        Correction::new(-0.0026040618575527644, -0.001443865415723786, 0.0),
                        Correction::new(-0.002604394281406033, -0.0014326078361994175, 0.0),
                        Correction::new(-0.0026028335486623236, -0.0014407728262463707, 0.0),
                        Correction::new(-0.002601199340478012, -0.0014419754710470886, 0.0),
                        Correction::new(-0.002604797967526684, -0.0014248122892494546, 0.0),
                        Correction::new(-0.0026016350879218175, -0.0014461593641387613, 0.0),
                        Correction::new(-0.0025982909237588702, -0.0014429850256785016, 0.0),
                        Correction::new(-0.0026076228863408683, -0.0014501194037147276, 0.0),
                        Correction::new(-0.0026056414118502905, -0.0014478727846693707, 0.0),
                        Correction::new(-0.0026059042156971494, -0.0014285023181905218, 0.0),
                        Correction::new(-0.002603927284456153, -0.0014351874807651155, 0.0),
                        Correction::new(-0.0026090619295559138, -0.0014337794025241065, 0.0),
                        Correction::new(-0.00260379206564831, -0.0014444874233470518, 0.0),
                        Correction::new(-0.002609189936705112, -0.0014270078801605962, 0.0),
                        Correction::new(-0.002606701501478843, -0.0014250520778697371, 0.0),
                        Correction::new(-0.0026049010998919204, -0.0014320785884550874, 0.0),
                        Correction::new(-0.002612766885673393, -0.0014261930013035468, 0.0),
                        Correction::new(-0.002597295847668742, -0.0014398264082119477, 0.0),
                        Correction::new(-0.0026063921720914734, -0.0014269641107310966, 0.0),
                        Correction::new(-0.002602542664255837, -0.00143682163560458, 0.0),
                        Correction::new(-0.0026040557419934217, -0.0014358744334743191, 0.0),
                        Correction::new(-0.002603596826441166, -0.0014463876344360386, 0.0),
                        Correction::new(-0.002604355125567014, -0.0014381848627093206, 0.0),
                        Correction::new(-0.002596008569565531, -0.0014415246418863037, 0.0),
                        Correction::new(-0.0026007201572384882, -0.001441531631360347, 0.0),
                        Correction::new(-0.002601132396305545, -0.0014241218135470296, 0.0),
                        Correction::new(-0.0026080985102495367, -0.0014284294432651895, 0.0),
                        Correction::new(-0.0026051196442774846, -0.0014472355651951197, 0.0),
                        Correction::new(-0.0026057136253893084, -0.0014245524301905658, 0.0),
                        Correction::new(-0.0026089743551779435, -0.001434848166382774, 0.0),
                        Correction::new(-0.002603603462876162, -0.001438143380099915, 0.0),
                        Correction::new(-0.002602828668145311, -0.0014340732746714502, 0.0),
                        Correction::new(-0.002605611000202166, -0.0014489020143559554, 0.0),
                        Correction::new(-0.0025977651215160877, -0.001443492127853303, 0.0),
                        Correction::new(-0.002613369266351838, -0.0014258897817417636, 0.0),
                        Correction::new(-0.002607597193807162, -0.0014301386682097242, 0.0),
                        Correction::new(-0.0026026200287471916, -0.001439230302737092, 0.0),
                    ])
                    .map(|(o, e)| {
                        assert_2ulp!(tf.forward_corr(o).unwrap(), e);
                        assert_2ulp!(tf.forward_corr_unchecked(o).unwrap(), e);
                    })
                    .collect::<Vec<_>>();
            }

            #[test]
            fn test_backward_corr_and_one_unchecked() {
                let tf = TransformerBuilder::new()
                    .format(Format::TKY2JGD)
                    .parameters(param::TKY2JGD)
                    .build();

                let _ = origin::TKY2JGD
                    .iter()
                    .zip([
                        Correction::new(0.002606186029597429, 0.001432486030401843, 0.0),
                        Correction::new(0.002616380795458269, 0.0014254058084066613, 0.0),
                        Correction::new(0.002610442350111168, 0.001425521971375949, 0.0),
                        Correction::new(0.00260549914609196, 0.001444711437479824, 0.0),
                        Correction::new(0.002605186943201238, 0.0014347342706107283, 0.0),
                        Correction::new(0.0026039392225462032, 0.0014420911244126585, 0.0),
                        Correction::new(0.0026027122022150516, 0.0014432251935010412, 0.0),
                        Correction::new(0.0026038873653075703, 0.0014264566950331337, 0.0),
                        Correction::new(0.0026039636291935258, 0.0014471664299068217, 0.0),
                        Correction::new(0.002600774681949701, 0.0014438215561830916, 0.0),
                        Correction::new(0.0026082458668776837, 0.001450525903824889, 0.0),
                        Correction::new(0.002606708222944097, 0.0014484637993148741, 0.0),
                        Correction::new(0.0026056949014729622, 0.0014300369860947286, 0.0),
                        Correction::new(0.002604824863285861, 0.0014370876155516577, 0.0),
                        Correction::new(0.002606341429720381, 0.0014341993844403428, 0.0),
                        Correction::new(0.0026028495537687795, 0.0014459318657103577, 0.0),
                        Correction::new(0.002606306749747543, 0.0014256245600731956, 0.0),
                        Correction::new(0.002603752984282238, 0.0014234158324080417, 0.0),
                        Correction::new(0.0026054547053366503, 0.001433956844963449, 0.0),
                        Correction::new(0.0026118477759219587, 0.0014269359340479796, 0.0),
                        Correction::new(0.0025983855227962624, 0.001441767376865146, 0.0),
                        Correction::new(0.002605858737808927, 0.0014284576545383313, 0.0),
                        Correction::new(0.002599939474381462, 0.0014386252352297493, 0.0),
                        Correction::new(0.0026049403971356994, 0.001437649695988217, 0.0),
                        Correction::new(0.0026051249119068602, 0.0014472089176628443, 0.0),
                        Correction::new(0.0026051848508354273, 0.001439626321127412, 0.0),
                        Correction::new(0.0025971190776225804, 0.0014434224114970471, 0.0),
                        Correction::new(0.0026019682735831345, 0.0014429430011320167, 0.0),
                        Correction::new(0.002601130413232378, 0.0014279236724465333, 0.0),
                        Correction::new(0.002607771278970886, 0.001429906750787098, 0.0),
                        Correction::new(0.002606310999517925, 0.001447888620287575, 0.0),
                        Correction::new(0.002604684369343261, 0.0014260134049254973, 0.0),
                        Correction::new(0.00260626221837615, 0.0014353723867724917, 0.0),
                        Correction::new(0.002600964757448706, 0.001439742194381401, 0.0),
                        Correction::new(0.0026036845541074624, 0.0014361754579083328, 0.0),
                        Correction::new(0.002606753327162285, 0.0014495313122466396, 0.0),
                        Correction::new(0.0025968757136544513, 0.0014453329417000451, 0.0),
                        Correction::new(0.0026106373557342314, 0.0014250706606104592, 0.0),
                        Correction::new(0.0026049577712024597, 0.001430299315960377, 0.0),
                        Correction::new(0.00260365921563244, 0.0014407570593193042, 0.0),
                    ])
                    .map(|(o, e)| {
                        assert_2ulp!(tf.backward_corr(o).unwrap(), e);
                        assert_2ulp!(tf.backward_corr_unchecked(o).unwrap(), e);
                    })
                    .collect::<Vec<_>>();
            }

            #[test]
            fn test_identity() {
                // test transformation not corr

                let tf = TransformerBuilder::new()
                    .format(Format::TKY2JGD)
                    .parameters(param::TKY2JGD)
                    .build();

                let _ = origin::TKY2JGD
                    .iter()
                    .map(|o| {
                        assert_eq!(&tf.backward(&tf.forward(o).unwrap()).unwrap(), o);
                        assert_eq!(&tf.forward(&tf.backward(o).unwrap()).unwrap(), o);
                    })
                    .collect::<Vec<_>>();
            }
        }
    }
}
