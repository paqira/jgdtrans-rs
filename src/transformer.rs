use std::collections::BTreeMap;
use std::error::Error;
use std::fmt::{Display, Formatter};

use crate::{Format, Point};
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::mesh::MeshCell;
use crate::par::ParseParError;

type Result<T> = std::result::Result<T, TransformError>;

#[inline]
fn bilinear_interpolation(sw: &f64, se: &f64, nw: &f64, ne: &f64, lat: &f64, lng: &f64) -> f64 {
    sw * (1. - lng) * (1. - lat) + se * lng * (1. - lat) + nw * (1. - lng) * lat + ne * lng * lat
}

/// Improved Kahan–Babuška algorithm
///
/// see: https://en.wikipedia.org/wiki/Kahan_summation_algorithm#Further_enhancements
fn ksum(vs: &[f64]) -> f64 {
    let mut sum = 0.0;
    let mut c = 0.0;
    for v in vs {
        let t = sum + *v;
        c += if sum.ge(v) {
            (sum - t) + v
        } else {
            (v - t) + sum
        };
        sum = t
    }
    sum + c
}

/// The parameter triplet.
///
/// We emphasize that the unit of latitude and longitude is \[sec\], not \[deg\].
///
/// It should fill with 0.0 instead of [`NAN`](f64::NAN)
/// if the parameter does not exist, as parsers does.
///
/// # Example
///
/// ```
/// # use jgdtrans::transformer::Parameter;
/// let parameter = Parameter::new(1., 2., 3.);
/// assert_eq!(parameter.latitude, 1.);
/// assert_eq!(parameter.longitude, 2.);
/// assert_eq!(parameter.altitude, 3.);
/// ```
#[derive(Debug, PartialEq, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Parameter {
    /// The latitude parameter \[sec\]
    pub latitude: f64,
    /// The latitude parameter \[sec\]
    pub longitude: f64,
    /// The altitude parameter \[m\]
    pub altitude: f64,
}

impl Parameter {
    /// Makes a `Parameter`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::transformer::Parameter;
    /// let parameter = Parameter::new(1., 2., 3.);
    /// assert_eq!(parameter.latitude, 1.);
    /// assert_eq!(parameter.longitude, 2.);
    /// assert_eq!(parameter.altitude, 3.);
    /// ```
    #[inline]
    pub fn new(latitude: f64, longitude: f64, altitude: f64) -> Self {
        Self {
            latitude,
            longitude,
            altitude,
        }
    }

    /// Returns $\\sqrt{\\text{latitude}^2 + \\text{longitude}^2}$.
    #[inline]
    pub fn horizontal(&self) -> f64 {
        f64::hypot(self.latitude, self.longitude)
    }
}

/// The transformation correction.
///
/// We emphasize that the unit is \[deg\], not \[sec\]
/// for latitude and longitude.
///
/// It should fill with 0.0 instead of [`NAN`](f64::NAN).
///
/// # Example
///
/// ```
/// # use jgdtrans::transformer::Correction;
/// let correction = Correction::new(1., 2., 3.);
/// assert_eq!(correction.latitude, 1.);
/// assert_eq!(correction.longitude, 2.);
/// assert_eq!(correction.altitude, 3.);
#[derive(Debug, PartialEq, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Correction {
    /// The latitude correction \[deg\].
    pub latitude: f64,
    /// The longitude correction \[deg\].
    pub longitude: f64,
    /// The altitude correction \[m\].
    pub altitude: f64,
}

impl Correction {
    /// Makes a [`Correction`].
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::transformer::Correction;
    /// let correction = Correction::new(1., 2., 3.);
    /// assert_eq!(correction.latitude, 1.);
    /// assert_eq!(correction.longitude, 2.);
    /// assert_eq!(correction.altitude, 3.);
    /// ```
    #[inline]
    pub fn new(latitude: f64, longitude: f64, altitude: f64) -> Self {
        Self {
            latitude,
            longitude,
            altitude,
        }
    }

    /// Returns $\\sqrt{\\text{latitude}^2 + \\text{longitude}^2}$.
    #[inline]
    pub fn horizontal(&self) -> f64 {
        f64::hypot(self.latitude, self.longitude)
    }
}

/// The statistics of parameter.
///
/// This is a component of the result that [`Transformer::statistics()`] returns.
#[derive(Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct StatisticData {
    /// The count.
    pub count: Option<usize>,
    /// The average (\[sec\] or \[m\]).
    pub mean: Option<f64>,
    /// The standard variance (\[sec\] or \[m\]).
    pub std: Option<f64>,
    /// $(1/n) \\sum_{i=1}^n \\left| \\text{parameter}_i \\right|$ (\[sec\] or \[m\]).
    pub abs: Option<f64>,
    /// The minimum (\[sec\] or \[m\]).
    pub min: Option<f64>,
    /// The maximum (\[sec\] or \[m\]).
    pub max: Option<f64>,
}

impl StatisticData {
    fn from_arr(vs: &[f64]) -> Self {
        if vs.is_empty() {
            return Self {
                count: None,
                mean: None,
                std: None,
                abs: None,
                min: None,
                max: None,
            };
        }

        let sum = ksum(vs);
        if sum.is_nan() {
            return Self {
                count: Some(vs.len()),
                mean: Some(f64::NAN),
                std: Some(f64::NAN),
                abs: Some(f64::NAN),
                min: Some(f64::NAN),
                max: Some(f64::NAN),
            };
        }

        let mut max = f64::MIN;
        let mut min = f64::MAX;
        let mut std: Vec<f64> = Vec::new();
        let mut abs: Vec<f64> = Vec::new();

        for v in vs.iter() {
            max = v.max(max);
            min = v.min(min);
            std.push((sum - *v).powi(2));
            abs.push(v.abs());
        }

        let length = vs.len() as f64;
        Self {
            count: Some(vs.len()),
            mean: Some(sum / length),
            std: Some((ksum(&std) / length).sqrt()),
            abs: Some(ksum(&abs) / length),
            min: Some(min),
            max: Some(max),
        }
    }
}

/// The statistical summary of parameter.
///
/// This is a result that [`Transformer::statistics()`] returns.
#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Statistics {
    /// The statistics of latitude.
    pub latitude: StatisticData,
    /// The statistics of longitude.
    pub longitude: StatisticData,
    /// The statistics of altitude.
    pub altitude: StatisticData,
}

/// The coordinate Transformer, and represents a deserializing result of par-formatted data.
///
/// If the parameters is zero, such as the unsupported components,
/// the transformations are identity transformation on such components.
/// For example, the transformation by the TKY2JGD and the PatchJGD par is
/// identity transformation on altitude, and by the PatchJGD(H) par is
/// so on latitude and longitude.
///
/// There is a builder, see [`TransformerBuilder`].
///
/// # Example
///
/// ```
/// # use jgdtrans::*;
/// # use jgdtrans::mesh::MeshUnit;
/// # use jgdtrans::transformer::Parameter;
/// # fn main() -> Result<(), TransformError> {
/// // from SemiDynaEXE2023.par
/// let tf = Transformer::new(
///     Format::SemiDynaEXE,
///     [
///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
///         (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
///         (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
///     ].into()
/// );
///
/// // forward transformation
/// let origin = Point::new(36.10377479, 140.087855041, 2.34);
/// let result = tf.forward(&origin)?;
/// assert_eq!(result.latitude, 36.103773017086695);
/// assert_eq!(result.longitude, 140.08785924333452);
/// assert_eq!(result.altitude, 2.4363138578103);
/// # Ok(())}
/// ```
#[derive(Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Transformer {
    /// The format of par file.
    pub format: Format,
    /// The transformation parameter.
    ///
    /// The entry represents single line of par-formatted file's parameter section,
    /// the key is meshcode, and the value parameter.
    pub parameter: BTreeMap<u32, Parameter>,
    /// The description, or the header of par-formatted data.
    #[cfg_attr(feature = "serde", serde(skip_serializing_if = "Option::is_none"))]
    pub description: Option<String>,
}

impl Transformer {
    /// Makes a [`Transformer`].
    ///
    /// We note that there is a builder, see [`TransformerBuilder`].
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::{Parameter, StatisticData};
    /// # fn main() -> Result<(), TransformError> {
    /// // from SemiDynaEXE2023.par
    /// let tf = Transformer::new(
    ///     Format::SemiDynaEXE,
    ///     [
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///     ].into()
    /// );
    ///
    /// assert_eq!(tf.format, Format::SemiDynaEXE);
    /// assert_eq!(tf.format.mesh_unit(), MeshUnit::Five);
    /// assert_eq!(
    ///     tf.parameter,
    ///     [
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///     ].into()
    /// );
    /// assert_eq!(tf.description, None);
    /// # Ok(())}
    /// ```
    #[inline]
    pub fn new(format: Format, parameter: BTreeMap<u32, Parameter>) -> Self {
        Self {
            format,
            parameter,
            description: None,
        }
    }

    /// Makes a [`Transformer`] with [`description`](Transformer::description).
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::{Parameter, StatisticData};
    /// # use std::collections::BTreeMap;
    /// # fn main() {
    /// let tf = Transformer::new_with_description(
    ///     Format::TKY2JGD,
    ///     BTreeMap::new(),
    ///     "My Parameter".to_string()
    /// );
    /// assert_eq!(tf.format, Format::TKY2JGD);
    /// assert_eq!(tf.format.mesh_unit(), MeshUnit::One);
    /// assert_eq!(tf.parameter, BTreeMap::new());
    /// assert_eq!(tf.description, Some("My Parameter".to_string()));
    /// # }
    /// ```
    #[inline]
    pub fn new_with_description(
        format: Format,
        parameter: BTreeMap<u32, Parameter>,
        description: String,
    ) -> Self {
        Self {
            format,
            parameter,
            description: Some(description),
        }
    }

    /// Deserialize par-formatted [`&str`] into a [`Transformer`].
    ///
    /// Use `format` argument to specify the format of `s`.
    ///
    /// This fills by 0.0 for altitude parameter when [`Format::TKY2JGD`] or [`Format::PatchJGD`] given,
    /// and for latitude and longitude when [`Format::PatchJGD_H`] or [`Format::HyokoRev`] given.
    ///
    /// ```no_run
    /// # use std::fs;
    /// # use std::error::Error;
    /// # use jgdtrans::{Transformer, Format, Point};
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// // deserialize SemiDynaEXE par file, e.g. SemiDyna2023.par
    /// let s = fs::read_to_string("SemiDyna2023.par")?;
    /// let tf = Transformer::from_str(&s, Format::SemiDynaEXE)?;
    ///
    /// // prints Format::SemiDynaEXE
    /// println!("{:?}", tf.format);
    /// // prints all parameter (long display)
    /// println!("{:?}", tf.parameter);
    /// // prints first 16 lines
    /// println!("{:?}", tf.description);
    ///
    /// // transform coordinate
    /// let point: Point = (35.0, 135.0).into();
    /// let result = tf.forward(&point);
    /// # Ok(())}
    /// ```
    ///
    /// # Errors
    ///
    /// If invalid data found.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::transformer::Parameter;
    /// # fn main() -> Result<(), ParseParError> {
    /// let s = r"<15 lines>
    /// # ...
    /// # ...
    /// # ...
    /// # ...
    /// # ...
    /// # ...
    /// # ...
    /// # ...
    /// # ...
    /// # ...
    /// # ...
    /// # ...
    /// # ...
    /// # ...
    /// MeshCode dB(sec)  dL(sec) dH(m)
    /// 12345678   0.00001   0.00002   0.00003";
    /// let tf = Transformer::from_str(&s, Format::SemiDynaEXE)?;
    /// assert_eq!(
    ///     tf.parameter.get(&12345678),
    ///     Some(&Parameter {latitude: 0.00001, longitude: 0.00002, altitude: 0.00003})
    /// );
    /// # Ok(())}
    /// ```
    #[inline]
    pub fn from_str(s: &str, format: Format) -> std::result::Result<Self, ParseParError> {
        format.parse(s)
    }

    /// Returns the statistics of the parameter.
    ///
    /// See [`StatisticData`] for details of result's components.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::{Parameter, StatisticData};
    /// # fn main() {
    /// // from SemiDynaEXE2023.par
    /// let tf = Transformer::new(
    ///     Format::SemiDynaEXE,
    ///     [
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///         (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
    ///         (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
    ///     ].into()
    /// );
    ///
    /// let stats = tf.statistics();
    /// assert_eq!(stats.latitude.count, Some(4));
    /// assert_eq!(stats.latitude.mean, Some(-0.0064225));
    /// assert_eq!(stats.latitude.std, Some(0.019268673410486777));
    /// assert_eq!(stats.latitude.abs, Some(0.006422499999999999));
    /// assert_eq!(stats.latitude.min, Some(-0.00664));
    /// assert_eq!(stats.latitude.max, Some(-0.0062));
    /// # }
    /// ```
    pub fn statistics(&self) -> Statistics {
        macro_rules! extract {
            ($name:ident) => {
                self.parameter.values().map(|v| v.$name).collect::<Vec<_>>()
            };
        }

        // latitude
        let arr: Vec<f64> = extract!(latitude);
        let latitude = StatisticData::from_arr(&arr);

        let arr: Vec<f64> = extract!(longitude);
        let longitude = StatisticData::from_arr(&arr);

        // altitude
        let arr: Vec<f64> = extract!(altitude);
        let altitude = StatisticData::from_arr(&arr);

        Statistics {
            latitude,
            longitude,
            altitude,
        }
    }

    /// Returns the forward-transformed position from [`point`](Point).
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::Parameter;
    /// # fn main() -> Result<(), TransformError> {
    /// // from SemiDynaEXE2023.par
    /// let tf = Transformer::new(
    ///     Format::SemiDynaEXE,
    ///     [
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///         (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
    ///         (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
    ///     ].into()
    /// );
    ///
    /// let origin = Point::new(36.10377479, 140.087855041, 2.34);
    /// let result = tf.forward(&origin)?;
    /// assert_eq!(result.latitude, 36.103773017086695);
    /// assert_eq!(result.longitude, 140.08785924333452);
    /// assert_eq!(result.altitude, 2.4363138578103);
    ///
    /// // This is equivalent to adding the result of Transformer::forward_corr
    /// assert_eq!(result, &origin + tf.forward_corr(&origin)?);
    /// # Ok(())}
    /// ```
    #[inline]
    pub fn forward(&self, point: &Point) -> Result<Point> {
        self.forward_corr(point).map(|corr| point + corr)
    }

    /// Returns the backward-transformed position from [`point`](Point).
    ///
    /// This is *not* exact as the original _TKY2JGD for Windows Ver.1.3.79_
    /// and the web APIs are (as far as we researched).
    ///
    /// There are points where unable to perform backward transformation
    /// even if they are the results of the forward transformation,
    /// because the forward transformation moves them to the area where the parameter does not support.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::Parameter;
    /// # fn main() -> Result<(), TransformError> {
    /// // from SemiDynaEXE2023.par
    /// let tf = Transformer::new(
    ///     Format::SemiDynaEXE,
    ///     [
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///         (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
    ///         (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
    ///     ].into()
    /// );
    ///
    /// // origin is forward trans. from 36.10377479, 140.087855041, 2.34
    /// let origin = Point::new(36.103773017086695, 140.08785924333452, 2.4363138578103);
    /// let result = tf.backward(&origin)?;
    /// assert_eq!(result.latitude, 36.10377479000002);
    /// assert_eq!(result.longitude, 140.087855041);
    /// assert_eq!(result.altitude, 2.339999999578243);
    ///
    /// // This is equivalent to adding the result of Transformer::backward_corr
    /// assert_eq!(result, &origin + tf.backward_corr(&origin)?);
    /// # Ok(())}
    /// ```
    #[inline]
    pub fn backward(&self, point: &Point) -> Result<Point> {
        self.backward_corr(point).map(|corr| point + corr)
    }

    /// Returns the validated backward-transformed position.
    ///
    /// The result's drafting from the exact solution
    /// is less than error of the GIAJ latitude and longitude parameter,
    /// 1e-9 \[deg\], for each latitude and longitude.
    /// The altitude's drafting is less than 1e-5 which is error of the GIAJ altitude parameter.
    ///     
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::Parameter;
    /// # fn main() -> Result<(), TransformError> {
    /// // from SemiDynaEXE2023.par
    /// let tf = Transformer::new(
    ///     Format::SemiDynaEXE,
    ///     [
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///         (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
    ///         (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
    ///     ].into()
    /// );
    ///
    /// // The origin is forward trans. from 36.10377479, 140.087855041, 2.34
    /// // In this case, no error remains
    /// let origin = Point::new(36.103773017086695, 140.08785924333452, 2.4363138578103);
    /// let result = tf.backward_safe(&origin)?;
    /// assert_eq!(result.latitude, 36.10377479);
    /// assert_eq!(result.longitude, 140.087855041);
    /// assert_eq!(result.altitude, 2.34);
    ///
    /// // This is equivalent to adding the result of Transformer::backward_corr_safe
    /// assert_eq!(result, &origin + tf.backward_safe_corr(&origin)?);
    /// # Ok(())}
    /// ```
    #[inline]
    pub fn backward_safe(&self, point: &Point) -> Result<Point> {
        self.backward_safe_corr(point).map(|corr| point + corr)
    }

    fn parameter_quadruple(
        &self,
        cell: &MeshCell,
    ) -> Result<(&Parameter, &Parameter, &Parameter, &Parameter)> {
        let meshcode = cell.south_west.to_meshcode();
        let sw = self
            .parameter
            .get(&meshcode)
            .ok_or(TransformError::new_pnf(meshcode, MeshCellCorner::SouthWest))?;

        let meshcode = cell.south_east.to_meshcode();
        let se = self
            .parameter
            .get(&meshcode)
            .ok_or(TransformError::new_pnf(meshcode, MeshCellCorner::SouthEast))?;

        let meshcode = cell.north_west.to_meshcode();
        let nw = self
            .parameter
            .get(&meshcode)
            .ok_or(TransformError::new_pnf(meshcode, MeshCellCorner::NorthWest))?;

        let meshcode = cell.north_east.to_meshcode();
        let ne = self
            .parameter
            .get(&meshcode)
            .ok_or(TransformError::new_pnf(meshcode, MeshCellCorner::NorthEast))?;

        Ok((sw, se, nw, ne))
    }

    /// Return the correction on forward-transformation.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::{Parameter, Correction};
    /// # fn main() -> Result<(), TransformError> {
    /// // from SemiDynaEXE2023.par
    /// let tf = Transformer::new(
    ///     Format::SemiDynaEXE,
    ///     [
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///         (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
    ///         (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
    ///     ].into()
    /// );
    ///
    /// let origin = Point::new(36.10377479, 140.087855041, 0.0);
    /// let corr = tf.forward_corr(&origin)?;
    /// assert_eq!(corr.latitude, -1.7729133100878255e-6);
    /// assert_eq!(corr.longitude, 4.202334510058886e-6);
    /// assert_eq!(corr.altitude, 0.09631385781030007);
    ///
    /// assert_eq!(&origin + corr, tf.forward(&origin)?);
    /// # Ok(())}
    /// ```
    pub fn forward_corr(&self, point: &Point) -> Result<Correction> {
        let cell = MeshCell::try_from_point(point, self.format.mesh_unit())
            .ok_or(TransformError::new_oob())?;

        let (sw, se, nw, ne) = self.parameter_quadruple(&cell)?;

        // Interpolation

        // y: latitude, x: longitude
        let (y, x) = cell.position(point);

        const SCALE: f64 = 3600.;

        let latitude = bilinear_interpolation(
            &sw.latitude,
            &se.latitude,
            &nw.latitude,
            &ne.latitude,
            &y,
            &x,
        ) / SCALE;

        let longitude = bilinear_interpolation(
            &sw.longitude,
            &se.longitude,
            &nw.longitude,
            &ne.longitude,
            &y,
            &x,
        ) / SCALE;

        let altitude = bilinear_interpolation(
            &sw.altitude,
            &se.altitude,
            &nw.altitude,
            &ne.altitude,
            &y,
            &x,
        );

        Ok(Correction {
            latitude,
            longitude,
            altitude,
        })
    }

    /// Return the correction on backward-transformation.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::{Parameter, Correction};
    /// # fn main() -> Result<(), TransformError> {
    /// // from SemiDynaEXE2023.par
    /// let tf = Transformer::new(
    ///     Format::SemiDynaEXE,
    ///     [
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///         (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
    ///         (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
    ///     ].into()
    /// );
    ///
    /// let origin = Point::new(36.103773017086695, 140.08785924333452, 0.0);
    /// let corr = tf.backward_corr(&origin)?;
    /// assert_eq!(corr.latitude, 1.7729133219831587e-6);
    /// assert_eq!(corr.longitude, -4.202334509042613e-6);
    /// assert_eq!(corr.altitude, -0.0963138582320569);
    ///
    /// assert_eq!(&origin + corr, tf.backward(&origin)?);
    /// # Ok(())}
    /// ```
    pub fn backward_corr(&self, point: &Point) -> Result<Correction> {
        // 12. / 3600.
        const DELTA: f64 = 1. / 300.;

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

    /// Return the verified correction on backward-transformation.
    ///
    /// See [`Transformer::backward_safe`] for detail.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::{Parameter, Correction};
    /// # fn main() -> Result<(), TransformError> {
    /// // from SemiDynaEXE2023.par
    /// let tf = Transformer::new(
    ///     Format::SemiDynaEXE,
    ///     [
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///         (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
    ///         (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
    ///     ].into()
    /// );
    ///
    /// let origin = Point::new(36.103773017086695, 140.08785924333452, 0.0);
    /// let corr = tf.backward_safe_corr(&origin)?;
    /// assert_eq!(corr.latitude, 1.7729133100878255e-6);
    /// assert_eq!(corr.longitude, -4.202334510058886e-6);
    /// assert_eq!(corr.altitude, -0.09631385781030007);
    ///
    /// assert_eq!(&origin + corr, tf.backward_safe(&origin)?);
    /// # Ok(())}
    /// ```
    pub fn backward_safe_corr(&self, point: &Point) -> Result<Correction> {
        // Newton's Method

        const SCALE: f64 = 3600.;
        const CRITERIA: f64 = 5e-14;
        const ITERATION: usize = 4;

        let mut yn = point.latitude;
        let mut xn = point.longitude;

        macro_rules! delta {
            ($x:expr, $xn:ident, $corr:expr) => {
                $x - ($xn + $corr)
            };
        }

        for _ in 0..ITERATION {
            let current = Point::new(yn, xn, 0.0);

            let cell = MeshCell::try_from_point(&current, self.format.mesh_unit())
                .ok_or(TransformError::new_oob())?;

            let (sw, se, nw, ne) = self.parameter_quadruple(&cell)?;

            let (y, x) = cell.position(&current);

            let corr_y = bilinear_interpolation(
                &sw.latitude,
                &se.latitude,
                &nw.latitude,
                &ne.latitude,
                &y,
                &x,
            ) / SCALE;

            let corr_x = bilinear_interpolation(
                &sw.longitude,
                &se.longitude,
                &nw.longitude,
                &ne.longitude,
                &y,
                &x,
            ) / SCALE;

            let fx = delta!(point.longitude, xn, corr_x);
            let fy = delta!(point.latitude, yn, corr_y);

            // for readability
            macro_rules! lng_sub {
                ($a:ident, $b:ident) => {
                    $a.longitude - $b.longitude
                };
            }
            macro_rules! lat_sub {
                ($a:ident, $b:ident) => {
                    $a.latitude - $b.latitude
                };
            }

            // fx,x
            let fx_x = -1. - (lng_sub!(se, sw) * (1. - yn) + lng_sub!(ne, nw) * yn) / SCALE;
            // fx,y
            let fx_y = -(lng_sub!(nw, sw) * (1. - xn) + lng_sub!(ne, se) * xn) / SCALE;
            // fy,x
            let fy_x = -(lat_sub!(se, sw) * (1. - yn) + lat_sub!(ne, nw) * yn) / SCALE;
            // fx,y
            let fy_y = -1. - (lat_sub!(nw, sw) * (1. - xn) + lat_sub!(ne, se) * xn) / SCALE;

            // # and its determinant
            let det = fx_x * fy_y - fy_x * fy_x;

            // # update Xn
            xn -= (fy_y * fx - fx_y * fy) / det;
            yn -= (fx_x * fy - fy_x * fx) / det;

            let corr = self.forward_corr(&Point::new(yn, xn, 0.0))?;

            let delta_x = delta!(point.longitude, xn, corr.longitude);
            let delta_y = delta!(point.latitude, yn, corr.latitude);

            if delta_x.abs().lt(&CRITERIA) && delta_y.abs().lt(&CRITERIA) {
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

/// The builder of [`Transformer`].
///
/// # Example
///
/// ```
/// # use jgdtrans::*;
/// # use jgdtrans::mesh::MeshUnit;
/// # use jgdtrans::transformer::{Parameter, TransformerBuilder};
/// # fn main() {
/// // from SemiDynaEXE2023.par
/// let tf: Transformer = TransformerBuilder::new(Format::SemiDynaEXE)
///   .parameters([
///       (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
///       (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
///   ])
///   .description("My parameter".to_string())
///   .build();
///
/// assert_eq!(tf.format, Format::SemiDynaEXE);
/// assert_eq!(
///     tf.parameter,
///     [
///       (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
///       (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
///     ].into()
/// );
/// assert_eq!(tf.description, Some("My parameter".to_string()));
/// # }
/// ```
#[derive(Debug, Clone)]
pub struct TransformerBuilder {
    format: Format,
    parameter: BTreeMap<u32, Parameter>,
    description: Option<String>,
}

impl TransformerBuilder {
    /// Makes a [`TransformerBuilder`].
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::{Parameter, TransformerBuilder};
    /// # use std::collections::BTreeMap;
    /// # fn main() {
    /// let tf = TransformerBuilder::new(Format::SemiDynaEXE).build();
    ///
    /// assert_eq!(tf.format, Format::SemiDynaEXE);
    /// assert_eq!(tf.parameter, BTreeMap::new());
    /// assert_eq!(tf.description, None);
    /// # }
    /// ```
    #[inline]
    pub fn new(format: Format) -> Self {
        TransformerBuilder {
            format,
            parameter: BTreeMap::new(),
            description: None,
        }
    }

    /// Updates by a [`Format`].
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::transformer::TransformerBuilder;
    /// # use std::collections::BTreeMap;
    /// # fn main() {
    /// let tf = TransformerBuilder::new(Format::SemiDynaEXE)
    ///     .format(Format::SemiDynaEXE)
    ///     .build();
    ///
    /// assert_eq!(tf.format, Format::SemiDynaEXE);
    /// # }
    /// ```
    #[inline]
    pub fn format(mut self, format: Format) -> Self {
        self.format = format;
        self
    }

    /// Adds a [`Parameter`].
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::{Parameter, TransformerBuilder};
    /// # use std::collections::BTreeMap;
    /// # fn main() {
    /// // from SemiDynaEXE2023.par
    /// let tf = TransformerBuilder::new(Format::SemiDynaEXE)
    ///     .parameter(54401005, Parameter::new(-0.00622, 0.01516, 0.0946))
    ///     .build();
    ///
    /// assert_eq!(tf.parameter, [(54401005, Parameter::new(-0.00622, 0.01516, 0.0946)), ].into());
    /// # }
    /// ```
    #[inline]
    pub fn parameter(mut self, key: u32, parameter: Parameter) -> Self {
        self.parameter.insert(key, parameter);
        self
    }

    /// Adds [`Parameter`]s.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::{Parameter, TransformerBuilder};
    /// # fn main() {
    /// // from SemiDynaEXE2023.par
    /// let tf = TransformerBuilder::new(Format::SemiDynaEXE)
    ///   .parameters([
    ///       (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///       (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///       (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
    ///       (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
    ///   ])
    ///   .build();
    ///
    /// assert_eq!(tf.parameter, [
    ///       (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///       (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///       (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
    ///       (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
    /// ].into());
    /// # }
    /// ```
    #[inline]
    pub fn parameters(mut self, parameters: impl IntoIterator<Item = (u32, Parameter)>) -> Self {
        for (key, parameter) in parameters.into_iter() {
            self.parameter.insert(key, parameter);
        }
        self
    }

    /// Updates [`description`](Transformer::description).
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::TransformerBuilder;
    /// # fn main() {
    /// let tf = TransformerBuilder::new(Format::SemiDynaEXE)
    ///   .description("My parameter".to_string())
    ///   .build();
    ///
    /// assert_eq!(tf.description, Some("My parameter".to_string()));
    /// # }
    /// ```
    #[inline]
    pub fn description(mut self, s: String) -> Self {
        self.description = Some(s);
        self
    }

    /// Builds [`Transformer`].
    #[inline]
    pub fn build(self) -> Transformer {
        Transformer {
            format: self.format,
            parameter: self.parameter,
            description: self.description,
        }
    }
}

//
// Error
//

#[derive(Debug)]
pub enum MeshCellCorner {
    NorthWest,
    NorthEast,
    SouthWest,
    SouthEast,
}

impl Display for MeshCellCorner {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        match self {
            Self::NorthWest => write!(f, "north-west"),
            Self::NorthEast => write!(f, "north-east"),
            Self::SouthWest => write!(f, "south-west"),
            Self::SouthEast => write!(f, "south-east"),
        }
    }
}

#[derive(Debug)]
pub enum TransformError {
    ParameterNotFound {
        meshcode: u32,
        corner: MeshCellCorner,
    },
    CorrectionNotFound,
    OutOfBounds,
}

impl Display for TransformError {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        match self {
            Self::ParameterNotFound { meshcode, corner } => {
                write!(f, "parameter not found: {} at {}", meshcode, corner)
            }
            Self::CorrectionNotFound => write!(f, "correction not found"),
            Self::OutOfBounds => write!(f, "position is out-of-bounds of transformation"),
        }
    }
}

impl Error for TransformError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

impl TransformError {
    #[cold]
    fn new_pnf(meshcode: u32, corner: MeshCellCorner) -> Self {
        Self::ParameterNotFound { meshcode, corner }
    }
    #[cold]
    fn new_cnf() -> Self {
        Self::CorrectionNotFound
    }
    #[cold]
    fn new_oob() -> Self {
        Self::OutOfBounds
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod test_ksum {
        use super::*;

        #[test]
        fn test_nan() {
            let actual = ksum(&[1., f64::NAN, 1.]);
            assert!(actual.is_nan());
        }
    }

    mod tests_transformer {
        use super::*;

        #[test]
        fn test_stats() {
            let stats = TransformerBuilder::new(Format::SemiDynaEXE)
                .parameters([
                    (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
                    (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
                    (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
                    (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
                ])
                .build()
                .statistics();

            assert_eq!(
                stats.latitude,
                StatisticData {
                    count: Some(4),
                    mean: Some(-0.0064225),
                    std: Some(0.019268673410486777),
                    abs: Some(0.006422499999999999),
                    min: Some(-0.00664),
                    max: Some(-0.0062)
                }
            );
            assert_eq!(
                stats.longitude,
                StatisticData {
                    count: Some(4),
                    mean: Some(0.0151075),
                    std: Some(0.045322702644480496),
                    abs: Some(0.0151075),
                    min: Some(0.01492),
                    max: Some(0.01529)
                }
            );
            assert_eq!(
                stats.altitude,
                StatisticData {
                    count: Some(4),
                    mean: Some(0.0972325),
                    std: Some(0.29174846730531423),
                    abs: Some(0.0972325),
                    min: Some(0.08972),
                    max: Some(0.10374)
                }
            );

            let stats = TransformerBuilder::new(Format::TKY2JGD)
                .build()
                .statistics();
            assert_eq!(
                stats.latitude,
                StatisticData {
                    count: None,
                    mean: None,
                    std: None,
                    abs: None,
                    min: None,
                    max: None
                }
            );
            assert_eq!(
                stats.longitude,
                StatisticData {
                    count: None,
                    mean: None,
                    std: None,
                    abs: None,
                    min: None,
                    max: None
                }
            );
            assert_eq!(
                stats.altitude,
                StatisticData {
                    count: None,
                    mean: None,
                    std: None,
                    abs: None,
                    min: None,
                    max: None
                }
            );

            let stats = TransformerBuilder::new(Format::SemiDynaEXE)
                .parameters([(54401005, Parameter::new(1., 0.0, f64::NAN))])
                .build()
                .statistics();

            assert_eq!(
                stats.latitude,
                StatisticData {
                    count: Some(1),
                    mean: Some(1.0),
                    std: Some(0.0),
                    abs: Some(1.0),
                    min: Some(1.0),
                    max: Some(1.0)
                }
            );
            assert_eq!(
                stats.longitude,
                StatisticData {
                    count: Some(1),
                    mean: Some(0.0),
                    std: Some(0.0),
                    abs: Some(0.0),
                    min: Some(0.0),
                    max: Some(0.0)
                }
            );
            assert_eq!(stats.altitude.count, Some(1));
            assert!(stats.altitude.mean.unwrap().is_nan());
            assert!(stats.altitude.std.unwrap().is_nan());
            assert!(stats.altitude.abs.unwrap().is_nan());
            assert!(stats.altitude.min.unwrap().is_nan());
            assert!(stats.altitude.max.unwrap().is_nan());
        }

        #[test]
        fn test_on_tky2jgd() {
            let tf = TransformerBuilder::new(Format::TKY2JGD)
                .parameters([
                    // forward
                    (54401027, Parameter::new(11.49105, -11.80078, 0.0)),
                    (54401027, Parameter::new(11.49105, -11.80078, 0.0)),
                    (54401037, Parameter::new(11.48732, -11.80198, 0.0)),
                    (54401028, Parameter::new(11.49096, -11.80476, 0.0)),
                    (54401038, Parameter::new(11.48769, -11.80555, 0.0)),
                    // backward
                    (54401047, Parameter::new(11.48373, -11.80318, 0.0)),
                    (54401048, Parameter::new(11.48438, -11.80689, 0.0)),
                ])
                .build();

            // v.s. web
            const DELTA: f64 = 0.00000001;

            // 国土地理院
            let origin = Point::new(36.103774791666666, 140.08785504166664, 0.0);
            let actual = tf.forward(&origin).unwrap();

            assert!((36.106966281 - actual.latitude).abs() < DELTA);
            assert!((140.084576867 - actual.longitude).abs() < DELTA);
            assert_eq!(0.0, actual.altitude);

            let origin = Point::new(36.10696628160147, 140.08457686629436, 0.0);
            let actual = tf.backward(&origin).unwrap();
            assert!((36.103774792 - actual.latitude).abs() < DELTA);
            assert!((140.087855042 - actual.longitude).abs() < DELTA);
            assert_eq!(0.0, actual.altitude);
        }

        #[test]
        fn test_on_patch_jgd_hv() {
            let tf = TransformerBuilder::new(Format::PatchJGD_HV)
                .parameters([
                    // forward
                    (57413454, Parameter::new(-0.05984, 0.22393, -1.25445)),
                    (57413464, Parameter::new(-0.06011, 0.22417, -1.24845)),
                    (57413455, Parameter::new(-0.0604, 0.2252, -1.29)),
                    (57413465, Parameter::new(-0.06064, 0.22523, -1.27667)),
                    // backward
                    (57413474, Parameter::new(-0.06037, 0.22424, -0.35308)),
                    (57413475, Parameter::new(-0.06089, 0.22524, 0.0)),
                ])
                .build();

            // v.s. web
            const DELTA: f64 = 0.00000001;

            // 金華山黄金山神社
            let origin = Point::new(38.2985120586605, 141.5559006163195, 0.);
            let actual = tf.forward(&origin).unwrap();
            assert!((38.298495306 - actual.latitude).abs() < DELTA);
            assert!((141.555963019 - actual.longitude).abs() < DELTA);
            assert!((-1.263 - actual.altitude).abs() < 0.001);

            let origin = Point::new(38.29849530463122, 141.55596301776936, 0.0);
            let actual = tf.backward(&origin).unwrap();
            assert!((38.298512058 - actual.latitude).abs() < DELTA);
            assert!((141.555900614 - actual.longitude).abs() < DELTA);
            assert!((1.264 - actual.altitude).abs() < 0.001);
        }

        #[test]
        fn test_on_semi_nyna_exe() {
            let tf = TransformerBuilder::new(Format::SemiDynaEXE)
                .parameters([
                    (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
                    (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
                    (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
                    (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
                ])
                .build();

            // v.s. web
            const DELTA: f64 = 0.00000001;

            // 国土地理院
            let origin = Point::new(36.103774791666666, 140.08785504166664, 0.);
            let actual = tf.forward(&origin).unwrap();
            assert!((36.103773019 - actual.latitude).abs() < DELTA);
            assert!((140.087859244 - actual.longitude).abs() < DELTA);
            assert!((0.096 - actual.altitude).abs() < 0.001);

            let origin = Point::new(36.10377301875336, 140.08785924400115, 0.);
            let actual = tf.backward(&origin).unwrap();
            assert!((36.103774792 - actual.latitude).abs() < DELTA);
            assert!((140.087855042 - actual.longitude).abs() < DELTA);
            assert!((-0.096 - actual.altitude).abs() < 0.001);
        }

        #[test]
        fn test_on_semi_nyna_exe_exact() {
            let tf = TransformerBuilder::new(Format::SemiDynaEXE)
                .parameters([
                    (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
                    (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
                    (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
                    (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
                ])
                .build();

            // v.s. exact
            const DELTA: f64 = 0.0000000000001;

            // 国土地理院
            let origin = Point::new(36.103774791666666, 140.08785504166664, 0.0);
            let actual = tf.forward(&origin).unwrap();
            assert!((36.10377301875335 - actual.latitude).abs() < DELTA);
            assert!((140.08785924400115 - actual.longitude).abs() < DELTA);
            assert!((0.09631385775572238 - actual.altitude).abs() < DELTA);

            let actual = tf.backward(&actual).unwrap();
            assert!((36.10377479166668 - actual.latitude).abs() < DELTA);
            assert!((140.08785504166664 - actual.longitude).abs() < DELTA);
            assert!((-4.2175864502150125955e-10 - actual.altitude).abs() < DELTA);
        }
    }
}
