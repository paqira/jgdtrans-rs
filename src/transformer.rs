//! Provides [`Transformer`] etc.
use std::collections::HashMap;
use std::error::Error;
use std::fmt::{Display, Formatter};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::internal::mul_add;
use crate::mesh::{MeshCell, MeshCode, MeshUnit};
use crate::par::ParseParError;
use crate::{Format, Point};

type Result<T> = std::result::Result<T, TransformError>;

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

impl From<(f64, f64, f64)> for Parameter {
    #[inline]
    fn from(value: (f64, f64, f64)) -> Self {
        Self {
            latitude: value.0,
            longitude: value.1,
            altitude: value.2,
        }
    }
}

impl From<[f64; 3]> for Parameter {
    #[inline]
    fn from(value: [f64; 3]) -> Self {
        Self {
            latitude: value[0],
            longitude: value[1],
            altitude: value[2],
        }
    }
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
    pub const fn new(latitude: f64, longitude: f64, altitude: f64) -> Self {
        Self {
            latitude,
            longitude,
            altitude,
        }
    }

    /// Returns √𝑙𝑎𝑡𝑖𝑡𝑢𝑑𝑒² + 𝑙𝑜𝑛𝑔𝑖𝑡𝑢𝑑𝑒².
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
    pub const fn new(latitude: f64, longitude: f64, altitude: f64) -> Self {
        Self {
            latitude,
            longitude,
            altitude,
        }
    }

    /// Returns √𝑙𝑎𝑡𝑖𝑡𝑢𝑑𝑒² + 𝑙𝑜𝑛𝑔𝑖𝑡𝑢𝑑𝑒².
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
    /// The count of parameters.
    pub count: Option<usize>,
    /// The mean, \[sec\] or \[m\].
    pub mean: Option<f64>,
    /// The standard variance, \[sec\] or \[m\].
    pub std: Option<f64>,
    /// The mean of abs value, 1/𝑛 ∑ᵢ | 𝑝𝑎𝑟𝑎𝑚𝑒𝑡𝑒𝑟ᵢ |, \[sec\] or \[m\].
    pub abs: Option<f64>,
    /// The minimum,\[sec\] or \[m\].
    pub min: Option<f64>,
    /// The maximum, \[sec\] or \[m\].
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

        let count = vs.len();
        let mut max = f64::MIN;
        let mut min = f64::MAX;
        let mut std: Vec<f64> = Vec::with_capacity(count);
        let mut abs: Vec<f64> = Vec::with_capacity(count);

        for v in vs.iter() {
            max = v.max(max);
            min = v.min(min);
            std.push((sum - *v).powi(2));
            abs.push(v.abs());
        }

        let length = count as f64;
        Self {
            count: Some(count),
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
    /// The statistics of horizontal.
    pub horizontal: StatisticData,
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
/// # Ok::<(), TransformError>(())
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
    pub parameter: HashMap<u32, Parameter>,
    /// The description, or the header of par-formatted data.
    #[cfg_attr(feature = "serde", serde(skip_serializing_if = "Option::is_none"))]
    pub description: Option<String>,
}

impl Transformer {
    /// Max error of [`Transformer::backward`] and [`Transformer::backward_corr`].
    pub const ERROR_MAX: f64 = 5e-14;

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
    /// ```
    #[inline]
    pub const fn new(format: Format, parameter: HashMap<u32, Parameter>) -> Self {
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
    /// # use std::collections::HashMap;
    /// let tf = Transformer::with_description(
    ///     Format::TKY2JGD,
    ///     HashMap::new(),
    ///     "My Parameter".to_string()
    /// );
    /// assert_eq!(tf.format, Format::TKY2JGD);
    /// assert_eq!(tf.format.mesh_unit(), MeshUnit::One);
    /// assert_eq!(tf.parameter, HashMap::new());
    /// assert_eq!(tf.description, Some("My Parameter".to_string()));
    /// ```
    #[inline]
    pub const fn with_description(
        format: Format,
        parameter: HashMap<u32, Parameter>,
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
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    ///
    /// # Errors
    ///
    /// Returns [`Err`] when the invalid data found.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// # use jgdtrans::transformer::Parameter;
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
    ///     Some(&Parameter::new(0.00001, 0.00002, 0.00003))
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[inline]
    pub fn from_str(s: &str, format: Format) -> std::result::Result<Self, ParseParError> {
        format.parse(s)
    }

    /// Deserialize par-formatted [`&str`] into a [`Transformer`] with description.
    ///
    /// See [`Transformer::from_str`] for detail.
    ///
    /// ```no_run
    /// # use std::fs;
    /// # use std::error::Error;
    /// # use jgdtrans::{Transformer, Format, Point};
    /// // deserialize SemiDynaEXE par file, e.g. SemiDyna2023.par
    /// let s = fs::read_to_string("SemiDyna2023.par")?;
    /// let tf = Transformer::from_str_with_description(
    ///     &s,
    ///     Format::SemiDynaEXE,
    ///     "SemiDyna2023.par".to_string()
    /// )?;
    ///
    /// // prints Format::SemiDynaEXE
    /// println!("{:?}", tf.format);
    /// // prints all parameter (long display)
    /// println!("{:?}", tf.parameter);
    /// // prints SemiDyna2023.par
    /// println!("{:?}", tf.description);
    ///
    /// // transform coordinate
    /// let point: Point = (35.0, 135.0).into();
    /// let result = tf.forward(&point);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    ///
    /// # Errors
    ///
    /// Returns [`Err`] when the invalid data found.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// # use jgdtrans::transformer::Parameter;
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
    /// let tf = Transformer::from_str_with_description(
    ///     &s,
    ///     Format::SemiDynaEXE,
    ///     "SemiDyna2023.par".to_string(),
    /// )?;
    /// assert_eq!(
    ///     tf.parameter.get(&12345678),
    ///     Some(&Parameter::new(0.00001, 0.00002, 0.00003))
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[inline]
    pub fn from_str_with_description(
        s: &str,
        format: Format,
        description: String,
    ) -> std::result::Result<Self, ParseParError> {
        let tf = format.parse(s)?;
        Ok(Self::with_description(tf.format, tf.parameter, description))
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
    ///
    /// assert_eq!(stats.latitude.count, Some(4));
    /// assert_eq!(stats.latitude.mean, Some(-0.0064225));
    /// assert_eq!(stats.latitude.std, Some(0.019268673410486777));
    /// assert_eq!(stats.latitude.abs, Some(0.006422499999999999));
    /// assert_eq!(stats.latitude.min, Some(-0.00664));
    /// assert_eq!(stats.latitude.max, Some(-0.0062));
    /// ```
    pub fn statistics(&self) -> Statistics {
        macro_rules! extract {
            ($name:ident) => {
                self.parameter.values().map(|v| v.$name).collect::<Vec<_>>()
            };
        }

        let arr: Vec<f64> = extract!(latitude);
        let latitude = StatisticData::from_arr(&arr);

        let arr: Vec<f64> = extract!(longitude);
        let longitude = StatisticData::from_arr(&arr);

        let arr: Vec<f64> = extract!(altitude);
        let altitude = StatisticData::from_arr(&arr);

        let arr: Vec<f64> = self
            .parameter
            .values()
            .map(|v| v.horizontal())
            .collect::<Vec<_>>();
        let horizontal = StatisticData::from_arr(&arr);

        Statistics {
            latitude,
            longitude,
            altitude,
            horizontal,
        }
    }

    /// Returns the forward-transformed position.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] when fails to transform.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::Parameter;
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
    /// let point = Point::new(36.10377479, 140.087855041, 2.34);
    /// let result = tf.forward(&point)?;
    ///
    /// assert_eq!(result.latitude, 36.103773017086695);
    /// assert_eq!(result.longitude, 140.08785924333452);
    /// assert_eq!(result.altitude, 2.4363138578103);
    ///
    /// // Transformer::backward is equivalent to
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
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::Parameter;
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
    /// let point = Point::new(36.103773017086695, 140.08785924333452, 2.4363138578103);
    /// let result = tf.backward_compat(&point)?;
    ///
    /// assert_eq!(result.latitude, 36.10377479000002);  // exact: 36.10377479
    /// assert_eq!(result.longitude, 140.087855041);  // exact: 140.087855041
    /// assert_eq!(result.altitude, 2.339999999578243);  // exact: 2.34
    ///
    /// // Transformer::backward is equivalent to
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
    /// is larger than [`Transformer::ERROR_MAX`],
    /// that is, the result's error is suppressed under [`Transformer::ERROR_MAX`].
    ///
    /// Notes, the error is less than 1e-9 \[deg\], which is
    /// error of the GIAJ latitude and longitude parameter.
    /// This implies that altitude's error is less than 1e-5 \[m\],
    /// which is error of the GIAJ altitude parameter.
    ///
    /// This is not compatible to the GIAJ web app/APIs (but more accurate).
    ///
    /// # Errors
    ///
    /// Returns [`Err`] when the transformation fails.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::Parameter;
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
    /// # Example
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::Parameter;
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
    /// let point = Point::new(36.10377479, 140.087855041, 2.34);
    ///
    /// // Equivalent to Transformer::forward except checking
    /// assert_eq!(
    ///     tf.unchecked_forward(&point)?,
    ///     tf.forward(&point)?
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[inline]
    pub fn unchecked_forward(&self, point: &Point) -> Result<Point> {
        self.unchecked_forward_corr(point).map(|corr| point + corr)
    }

    /// Unchecked backward-transformation compatible to the GIAJ web app/APIs.
    ///
    /// This does not check the bounds of `point`.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] when the transformation fails.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::Parameter;
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
    /// let point = Point::new(36.103773017086695, 140.08785924333452, 2.4363138578103);
    ///
    /// // Equivalent to Transformer::backward_compat except checking
    /// assert_eq!(
    ///     tf.unchecked_backward_compat(&point)?,
    ///     tf.backward_compat(&point)?
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[inline]
    pub fn unchecked_backward_compat(&self, point: &Point) -> Result<Point> {
        self.unchecked_backward_compat_corr(point)
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
    /// # Example
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::Parameter;
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
    /// let point = Point::new(36.103773017086695, 140.08785924333452, 2.4363138578103);
    ///
    /// // Equivalent to Transformer::backward except checking
    /// assert_eq!(
    ///     tf.unchecked_backward(&point)?,
    ///     tf.backward(&point)?
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[inline]
    pub fn unchecked_backward(&self, point: &Point) -> Result<Point> {
        self.unchecked_backward_corr(point).map(|corr| point + corr)
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
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::{Parameter, Correction};
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
    ///
    /// assert_eq!(corr.latitude, -1.7729133100878255e-6);
    /// assert_eq!(corr.longitude, 4.202334510058886e-6);
    /// assert_eq!(corr.altitude, 0.09631385781030007);
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

        const SCALE: f64 = 3600.;

        let latitude = interpol.latitude(&y, &x) / SCALE;
        let longitude = interpol.longitude(&y, &x) / SCALE;
        let altitude = interpol.altitude(&y, &x);

        Ok(Correction {
            latitude,
            longitude,
            altitude,
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
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::{Parameter, Correction};
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
    /// let corr = tf.backward_compat_corr(&origin)?;
    ///
    /// assert_eq!(corr.latitude, 1.7729133219831587e-6);
    /// assert_eq!(corr.longitude, -4.202334509042613e-6);
    /// assert_eq!(corr.altitude, -0.0963138582320569);
    ///
    /// assert_eq!(&origin + corr, tf.backward_compat(&origin)?);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn backward_compat_corr(&self, point: &Point) -> Result<Correction> {
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

    /// Return the correction on the backward-transformation.
    ///
    /// See [`Transformer::the backward`] for detail.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] when solving correction fails.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::{Parameter, Correction};
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
    ///
    /// assert_eq!(corr.latitude, 1.7729133100878255e-6);
    /// assert_eq!(corr.longitude, -4.202334510058886e-6);
    /// assert_eq!(corr.altitude, -0.09631385781030007);
    ///
    /// assert_eq!(&origin + corr, tf.backward(&origin)?);
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn backward_corr(&self, point: &Point) -> Result<Correction> {
        // Newton's Method

        const SCALE: f64 = 3600.;
        const ITERATION: usize = 4;

        let mut xn = point.longitude;
        let mut yn = point.latitude;

        macro_rules! delta {
            ($x:expr, $xn:ident, $corr:expr) => {
                $x - ($xn + $corr)
            };
        }

        for _ in 0..ITERATION {
            let current = Point::new(yn, xn, 0.0);

            let cell = MeshCell::try_from_point(&current, self.format.mesh_unit())
                .ok_or(TransformError::new_oob())?;

            let interpol = Interpol::from(&self.parameter, &cell)?;

            let (y, x) = cell.position(&current);

            let drift_x = interpol.longitude(&y, &x) / SCALE;
            let drift_y = interpol.latitude(&y, &x) / SCALE;

            let fx = delta!(point.longitude, xn, drift_x);
            let fy = delta!(point.latitude, yn, drift_y);

            // for readability
            macro_rules! lng_sub {
                ($a:ident, $b:ident) => {
                    interpol.$a.longitude - interpol.$b.longitude
                };
            }

            macro_rules! lat_sub {
                ($a:ident, $b:ident) => {
                    interpol.$a.latitude - interpol.$b.latitude
                };
            }

            // let fx_x = -1. - (lng_sub!(se, sw) * (1. - yn) + lng_sub!(ne, nw) * yn) / SCALE;
            let fx_x = {
                let temp = lng_sub!(ne, nw) * yn;
                let temp = mul_add!(lng_sub!(se, sw), 1. - yn, temp);
                -mul_add!(temp, 1. / SCALE, 1.)
            };

            // let fx_y = -(lng_sub!(nw, sw) * (1. - xn) + lng_sub!(ne, se) * xn) / SCALE;
            let fx_y = {
                let temp = lng_sub!(ne, se) * xn;
                -mul_add!(lng_sub!(nw, sw), 1. - xn, temp) / SCALE
            };

            // let fy_x = -(lat_sub!(se, sw) * (1. - yn) + lat_sub!(ne, nw) * yn) / SCALE;
            let fy_x = {
                let temp = lat_sub!(ne, nw) * yn;
                -mul_add!(lat_sub!(se, sw), 1. - yn, temp) / SCALE
            };

            // let fy_y = -1. - (lat_sub!(nw, sw) * (1. - xn) + lat_sub!(ne, se) * xn) / SCALE;
            let fy_y = {
                let temp = lat_sub!(ne, se) * xn;
                let temp = mul_add!(lat_sub!(nw, sw), 1. - xn, temp);
                -mul_add!(temp, 1. / SCALE, 1.)
            };

            // and its determinant
            let det = fx_x * fy_y - fx_y * fy_x;

            // update Xn
            // xn -= (fy_y * fx - fx_y * fy) / det;
            // yn -= (fx_x * fy - fy_x * fx) / det;
            xn = mul_add!(fy_y * fx - fx_y * fy, -1. / det, xn);
            yn = mul_add!(fx_x * fy - fy_x * fx, -1. / det, yn);

            let corr = self.forward_corr(&Point::new(yn, xn, 0.0))?;

            let delta_x = delta!(point.longitude, xn, corr.longitude);
            let delta_y = delta!(point.latitude, yn, corr.latitude);

            if delta_x.abs().lt(&Self::ERROR_MAX) && delta_y.abs().lt(&Self::ERROR_MAX) {
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
    /// # Example
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::{Parameter, Correction};
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
    ///
    /// // Equivalent to Transformer::forward_corr except checking
    /// assert_eq!(
    ///     tf.unchecked_forward_corr(&origin)?,
    ///     tf.forward_corr(&origin)?
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[inline]
    pub fn unchecked_forward_corr(&self, point: &Point) -> Result<Correction> {
        let mesh_unit = self.format.mesh_unit();

        let code = MeshCode::from_point(point, &mesh_unit);

        // Interpolation
        let interpol = Interpol::unchecked_from(&self.parameter, &code, &mesh_unit)?;

        // y: latitude, x: longitude
        let (y, x) = code.position(point, &mesh_unit);

        const SCALE: f64 = 3600.;

        let latitude = interpol.latitude(&y, &x) / SCALE;
        let longitude = interpol.longitude(&y, &x) / SCALE;
        let altitude = interpol.altitude(&y, &x);

        Ok(Correction {
            latitude,
            longitude,
            altitude,
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
    /// # Example
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::{Parameter, Correction};
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
    ///
    /// // Equivalent to Transformer::backward_compat_corr except checking
    /// assert_eq!(
    ///     tf.unchecked_backward_compat_corr(&origin)?,
    ///     tf.backward_compat_corr(&origin)?,
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn unchecked_backward_compat_corr(&self, point: &Point) -> Result<Correction> {
        // 12. / 3600.
        const DELTA: f64 = 1. / 300.;

        let corr = Correction {
            latitude: -DELTA,
            longitude: DELTA,
            altitude: 0.0,
        };

        let temporal = point + corr;

        let corr = self.unchecked_forward_corr(&temporal)?;
        let reference = point - corr;

        // actual correction
        let corr = self.unchecked_forward_corr(&reference)?;
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
    /// # Example
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::{Parameter, Correction};
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
    ///
    /// // Equivalent to Transformer::backward_corr except checking
    /// assert_eq!(
    ///     tf.unchecked_backward_corr(&origin)?,
    ///     tf.backward_corr(&origin)?
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    pub fn unchecked_backward_corr(&self, point: &Point) -> Result<Correction> {
        let mesh_unit = self.format.mesh_unit();

        const SCALE: f64 = 3600.;
        const ITERATION: usize = 4;

        let mut xn = point.longitude;
        let mut yn = point.latitude;

        macro_rules! delta {
            ($x:expr, $xn:ident, $corr:expr) => {
                $x - ($xn + $corr)
            };
        }

        for _ in 0..ITERATION {
            let current = Point::new(yn, xn, 0.0);

            let code = MeshCode::from_point(&current, &mesh_unit);

            let interpol = Interpol::unchecked_from(&self.parameter, &code, &mesh_unit)?;

            let (y, x) = code.position(&current, &mesh_unit);

            let drift_x = interpol.longitude(&y, &x) / SCALE;
            let drift_y = interpol.latitude(&y, &x) / SCALE;

            let fx = delta!(point.longitude, xn, drift_x);
            let fy = delta!(point.latitude, yn, drift_y);

            macro_rules! lng_sub {
                ($a:ident, $b:ident) => {
                    interpol.$a.longitude - interpol.$b.longitude
                };
            }

            macro_rules! lat_sub {
                ($a:ident, $b:ident) => {
                    interpol.$a.latitude - interpol.$b.latitude
                };
            }

            let fx_x = {
                let temp = lng_sub!(ne, nw) * yn;
                let temp = mul_add!(lng_sub!(se, sw), 1. - yn, temp);
                -mul_add!(temp, 1. / SCALE, 1.)
            };

            let fx_y = {
                let temp = lng_sub!(ne, se) * xn;
                -mul_add!(lng_sub!(nw, sw), 1. - xn, temp) / SCALE
            };

            let fy_x = {
                let temp = lat_sub!(ne, nw) * yn;
                -mul_add!(lat_sub!(se, sw), 1. - yn, temp) / SCALE
            };

            let fy_y = {
                let temp = lat_sub!(ne, se) * xn;
                let temp = mul_add!(lat_sub!(nw, sw), 1. - xn, temp);
                -mul_add!(temp, 1. / SCALE, 1.)
            };

            // and its determinant
            let det = fx_x * fy_y - fx_y * fy_x;

            // update Xn
            xn = mul_add!(fy_y * fx - fx_y * fy, -1. / det, xn);
            yn = mul_add!(fx_x * fy - fy_x * fx, -1. / det, yn);

            let corr = self.unchecked_forward_corr(&Point::new(yn, xn, 0.0))?;

            let delta_x = delta!(point.longitude, xn, corr.longitude);
            let delta_y = delta!(point.latitude, yn, corr.latitude);

            if delta_x.abs().lt(&Self::ERROR_MAX) && delta_y.abs().lt(&Self::ERROR_MAX) {
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

struct Interpol<'a> {
    sw: &'a Parameter,
    se: &'a Parameter,
    nw: &'a Parameter,
    ne: &'a Parameter,
}

macro_rules! interpol {
    ($self:ident, $target:ident, $lat:ident, $lng:ident) => {{
        let temp = $self.sw.$target * (1. - $lng) * (1. - $lat);
        let temp = mul_add!($self.se.$target, $lng * (1. - $lat), temp);
        let temp = mul_add!($self.nw.$target, (1. - $lng) * $lat, temp);
        mul_add!($self.ne.$target, $lng * $lat, temp)
    }};
}

impl<'a> Interpol<'a> {
    #[inline]
    fn from(parameter: &'a HashMap<u32, Parameter>, cell: &MeshCell) -> Result<Self> {
        let meshcode = cell.south_west.to_meshcode();
        let sw = parameter
            .get(&meshcode)
            .ok_or(TransformError::new_pnf(meshcode, MeshCellCorner::SouthWest))?;

        let meshcode = cell.south_east.to_meshcode();
        let se = parameter
            .get(&meshcode)
            .ok_or(TransformError::new_pnf(meshcode, MeshCellCorner::SouthEast))?;

        let meshcode = cell.north_west.to_meshcode();
        let nw = parameter
            .get(&meshcode)
            .ok_or(TransformError::new_pnf(meshcode, MeshCellCorner::NorthWest))?;

        let meshcode = cell.north_east.to_meshcode();
        let ne = parameter
            .get(&meshcode)
            .ok_or(TransformError::new_pnf(meshcode, MeshCellCorner::NorthEast))?;

        Ok(Self { sw, se, nw, ne })
    }

    #[inline]
    fn unchecked_from(
        parameter: &'a HashMap<u32, Parameter>,
        code: &MeshCode,
        mesh_unit: &MeshUnit,
    ) -> Result<Self> {
        let east = code.next_east(mesh_unit);
        let north = code.next_north(mesh_unit);
        let north_east = north.next_east(mesh_unit);

        let meshcode = code.to_u32();
        let sw = parameter
            .get(&meshcode)
            .ok_or(TransformError::new_pnf(meshcode, MeshCellCorner::SouthWest))?;

        let meshcode = east.to_u32();
        let se = parameter
            .get(&meshcode)
            .ok_or(TransformError::new_pnf(meshcode, MeshCellCorner::SouthEast))?;

        let meshcode = north.to_u32();
        let nw = parameter
            .get(&meshcode)
            .ok_or(TransformError::new_pnf(meshcode, MeshCellCorner::NorthWest))?;

        let meshcode = north_east.to_u32();
        let ne = parameter
            .get(&meshcode)
            .ok_or(TransformError::new_pnf(meshcode, MeshCellCorner::NorthEast))?;

        Ok(Self { sw, se, nw, ne })
    }

    #[inline]
    fn latitude(&self, lat: &f64, lng: &f64) -> f64 {
        interpol!(self, latitude, lat, lng)
    }

    #[inline]
    fn longitude(&self, lat: &f64, lng: &f64) -> f64 {
        interpol!(self, longitude, lat, lng)
    }

    #[inline]
    fn altitude(&self, lat: &f64, lng: &f64) -> f64 {
        interpol!(self, altitude, lat, lng)
    }
}

/// The builder of [`Transformer`].
///
/// # Safety
///
/// Panics when `format` is not assigned.
///
/// # Example
///
/// ```
/// # use jgdtrans::*;
/// # use jgdtrans::mesh::MeshUnit;
/// # use jgdtrans::transformer::{Parameter, TransformerBuilder};
/// // from SemiDynaEXE2023.par
/// let tf: Transformer = TransformerBuilder::new()
///     .format(Format::SemiDynaEXE)
///     .parameters([
///         (54401005, (-0.00622, 0.01516, 0.0946)),
///         (54401055, (-0.0062, 0.01529, 0.08972)),
///     ])
///     .description("My parameter".to_string())
///     .build();
///
/// assert_eq!(tf.format, Format::SemiDynaEXE);
/// assert_eq!(
///     tf.parameter,
///     [
///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
///     ].into()
/// );
/// assert_eq!(tf.description, Some("My parameter".to_string()));
/// ```
#[derive(Debug, Clone)]
pub struct TransformerBuilder {
    format: Option<Format>,
    parameter: HashMap<u32, Parameter>,
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
    /// # use std::collections::HashMap;
    /// let tf = TransformerBuilder::new()
    ///     .format(Format::SemiDynaEXE)
    ///     .build();
    ///
    /// assert_eq!(tf.format, Format::SemiDynaEXE);
    /// assert_eq!(tf.parameter, HashMap::new());
    /// assert_eq!(tf.description, None);
    /// ```
    #[allow(clippy::new_without_default)]
    #[inline]
    pub fn new() -> Self {
        Self {
            format: None,
            parameter: HashMap::new(),
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
    /// # use std::collections::HashMap;
    /// let tf = TransformerBuilder::new()
    ///     .format(Format::SemiDynaEXE)
    ///     .build();
    ///
    /// assert_eq!(tf.format, Format::SemiDynaEXE);
    /// ```
    #[inline]
    pub const fn format(mut self, format: Format) -> Self {
        self.format = Some(format);
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
    /// # use std::collections::HashMap;
    /// // from SemiDynaEXE2023.par
    /// let tf = TransformerBuilder::new()
    ///     .format(Format::SemiDynaEXE)
    ///     .parameter(54401005, (-0.00622, 0.01516, 0.0946))
    ///     .build();
    ///
    /// assert_eq!(
    ///     tf.parameter,
    ///     [(54401005, Parameter::new(-0.00622, 0.01516, 0.0946)), ].into()
    /// );
    /// ```
    #[inline]
    pub fn parameter(mut self, meshcode: u32, parameter: impl Into<Parameter>) -> Self {
        self.parameter.insert(meshcode, parameter.into());
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
    /// // from SemiDynaEXE2023.par
    /// let tf = TransformerBuilder::new()
    ///     .format(Format::SemiDynaEXE)
    ///     .parameters([
    ///         (54401005, (-0.00622, 0.01516, 0.0946)),
    ///         (54401055, (-0.0062, 0.01529, 0.08972)),
    ///         (54401100, (-0.00663, 0.01492, 0.10374)),
    ///         (54401150, (-0.00664, 0.01506, 0.10087)),
    ///     ])
    ///     .build();
    ///
    /// assert_eq!(
    ///     tf.parameter,
    ///     [
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///         (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
    ///         (54401150, Parameter::new(-0.00664, 0.01506, 0.10087)),
    ///     ].into()
    /// );
    /// ```
    #[inline]
    pub fn parameters(
        mut self,
        parameters: impl IntoIterator<Item = (u32, impl Into<Parameter>)>,
    ) -> Self {
        for (meshcode, parameter) in parameters.into_iter() {
            self.parameter.insert(meshcode, parameter.into());
        }
        self
    }

    /// Updates [`description`](Transformer::description).
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::transformer::TransformerBuilder;
    /// let tf = TransformerBuilder::new()
    ///     .format(Format::SemiDynaEXE)
    ///     .description("My parameter".to_string())
    ///     .build();
    ///
    /// assert_eq!(tf.description, Some("My parameter".to_string()));
    /// ```
    #[inline]
    pub fn description(mut self, s: String) -> Self {
        self.description = Some(s);
        self
    }

    /// Builds [`Transformer`].
    ///
    /// # Safety
    ///
    /// Panics when `format` is not assigned.
    #[inline]
    pub fn build(self) -> Transformer {
        Transformer {
            format: self.format.expect("format is not assigned"),
            parameter: self.parameter,
            description: self.description,
        }
    }
}

//
// Error
//

/// An error which can be returned on coordinate transforming.
///
/// This error is used as the error type for the [`Transformer::forward`],
/// [`Transformer::forward_corr`] etc.
#[derive(Debug)]
pub struct TransformError {
    kind: TransformErrorKind,
}

/// An error kind used by [`TransformError`].
#[derive(Debug)]
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
#[derive(Debug)]
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

impl Display for TransformError {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        match &self.kind {
            TransformErrorKind::ParameterNotFound { meshcode, corner } => {
                write!(f, "parameter not found: {} at {}", meshcode, corner)
            }
            TransformErrorKind::CorrectionNotFound => write!(f, "correction not found"),
            TransformErrorKind::OutOfBounds => {
                write!(f, "position is out-of-bounds of transformation")
            }
        }
    }
}

impl Error for TransformError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
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
        fn test_stats() {
            let stats = TransformerBuilder::new()
                .format(Format::SemiDynaEXE)
                .parameters(SemiDynaEXE)
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
            assert_eq!(
                stats.horizontal,
                StatisticData {
                    count: Some(4),
                    mean: Some(if cfg!(target_os = "linux") {
                        0.065671211791622
                    } else {
                        0.016417802947905496
                    }),
                    std: Some(0.04925345347374167),
                    abs: Some(if cfg!(target_os = "linux") {
                        0.065671211791622
                    } else {
                        0.016417802947905496
                    }),
                    min: Some(0.016326766366920303),
                    max: Some(0.016499215132847987)
                }
            );
            // 0.016417802947905496

            let stats = TransformerBuilder::new()
                .format(Format::TKY2JGD)
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
            assert_eq!(
                stats.horizontal,
                StatisticData {
                    count: None,
                    mean: None,
                    std: None,
                    abs: None,
                    min: None,
                    max: None
                }
            );

            let stats = TransformerBuilder::new()
                .format(Format::SemiDynaEXE)
                .parameters([(54401005, (1., 0.0, f64::NAN))])
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
            assert_eq!(
                stats.horizontal,
                StatisticData {
                    count: Some(1),
                    mean: Some(1.0),
                    std: Some(0.0),
                    abs: Some(1.0),
                    min: Some(1.0),
                    max: Some(1.0)
                }
            );
        }

        #[test]
        fn test_on_tky2jgd() {
            let tf = TransformerBuilder::new()
                .format(Format::TKY2JGD)
                .parameters(TKY2JGD)
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
            let actual = tf.backward_compat(&origin).unwrap();
            assert!((36.103774792 - actual.latitude).abs() < DELTA);
            assert!((140.087855042 - actual.longitude).abs() < DELTA);
            assert_eq!(0.0, actual.altitude);
        }

        #[test]
        fn test_on_patch_jgd_hv() {
            let tf = TransformerBuilder::new()
                .format(Format::PatchJGD_HV)
                .parameters(PatchJGD_HV)
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
            let actual = tf.backward_compat(&origin).unwrap();
            assert!((38.298512058 - actual.latitude).abs() < DELTA);
            assert!((141.555900614 - actual.longitude).abs() < DELTA);
            assert!((1.264 - actual.altitude).abs() < 0.001);
        }

        #[test]
        fn test_on_semi_nyna_exe() {
            let tf = TransformerBuilder::new()
                .format(Format::SemiDynaEXE)
                .parameters(SemiDynaEXE)
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
            let actual = tf.backward_compat(&origin).unwrap();
            assert!((36.103774792 - actual.latitude).abs() < DELTA);
            assert!((140.087855042 - actual.longitude).abs() < DELTA);
            assert!((-0.096 - actual.altitude).abs() < 0.001);
        }

        #[test]
        fn test_on_semi_nyna_exe_exact() {
            let tf = TransformerBuilder::new()
                .format(Format::SemiDynaEXE)
                .parameters(SemiDynaEXE)
                .build();

            // v.s. exact
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
        fn test_unchecked_forward_and_corr() {
            // TKY2JGD
            let tf = TransformerBuilder::new()
                .format(Format::TKY2JGD)
                .parameters(TKY2JGD)
                .build();

            let origin = Point::new(36.103774791666666, 140.08785504166664, 0.0);
            assert_eq!(
                tf.unchecked_forward(&origin).unwrap(),
                tf.forward(&origin).unwrap()
            );
            assert_eq!(
                tf.unchecked_forward_corr(&origin).unwrap(),
                tf.forward_corr(&origin).unwrap()
            );

            // SemiDynaEXE
            let tf = TransformerBuilder::new()
                .format(Format::SemiDynaEXE)
                .parameters(SemiDynaEXE)
                .build();

            let origin = Point::new(36.103774791666666, 140.08785504166664, 0.0);
            assert_eq!(
                tf.unchecked_forward(&origin).unwrap(),
                tf.forward(&origin).unwrap()
            );
            assert_eq!(
                tf.unchecked_forward_corr(&origin).unwrap(),
                tf.forward_corr(&origin).unwrap()
            );
        }

        #[test]
        fn test_unchecked_backward_compat_and_corr() {
            // TKY2JGD
            let tf = TransformerBuilder::new()
                .format(Format::TKY2JGD)
                .parameters(TKY2JGD)
                .build();

            let origin = Point::new(36.103774791666666, 140.08785504166664, 0.0);
            assert_eq!(
                tf.unchecked_backward_compat(&origin).unwrap(),
                tf.backward_compat(&origin).unwrap()
            );
            assert_eq!(
                tf.unchecked_backward_compat_corr(&origin).unwrap(),
                tf.backward_compat_corr(&origin).unwrap()
            );

            // SemiDynaEXE
            let tf = TransformerBuilder::new()
                .format(Format::SemiDynaEXE)
                .parameters(SemiDynaEXE)
                .build();

            let origin = Point::new(36.103774791666666, 140.08785504166664, 0.0);
            assert_eq!(
                tf.unchecked_backward_compat(&origin).unwrap(),
                tf.backward_compat(&origin).unwrap()
            );
            assert_eq!(
                tf.unchecked_backward_compat_corr(&origin).unwrap(),
                tf.backward_compat_corr(&origin).unwrap()
            );
        }
        #[test]
        fn test_unchecked_backward_checked_and_corr() {
            // TKY2JGD
            let tf = TransformerBuilder::new()
                .format(Format::TKY2JGD)
                .parameters(TKY2JGD)
                .build();

            let origin = Point::new(36.103774791666666, 140.08785504166664, 0.0);
            assert_eq!(
                tf.unchecked_backward(&origin).unwrap(),
                tf.backward(&origin).unwrap()
            );
            assert_eq!(
                tf.unchecked_backward_corr(&origin).unwrap(),
                tf.backward_corr(&origin).unwrap()
            );

            // SemiDynaEXE
            let tf = TransformerBuilder::new()
                .format(Format::SemiDynaEXE)
                .parameters(SemiDynaEXE)
                .build();

            let origin = Point::new(36.103774791666666, 140.08785504166664, 0.0);
            assert_eq!(
                tf.unchecked_backward(&origin).unwrap(),
                tf.backward(&origin).unwrap()
            );
            assert_eq!(
                tf.unchecked_backward_corr(&origin).unwrap(),
                tf.backward_corr(&origin).unwrap()
            );
        }
    }

    mod test_builder {
        use super::*;

        #[test]
        #[should_panic(expected = "format is not assigned")]
        fn test_panic() {
            let _ = TransformerBuilder::new().build();
        }

        #[test]
        fn test_impl() {
            let tf = TransformerBuilder::new()
                .format(Format::SemiDynaEXE)
                .parameter(54401005, (-0.00622, 0.01516, 0.0946))
                .parameter(54401055, [-0.0062, 0.01529, 0.08972])
                .parameter(54401100, Parameter::new(-0.00663, 0.01492, 0.10374))
                .build();

            assert_eq!(
                tf.parameter,
                [
                    (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
                    (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
                    (54401100, Parameter::new(-0.00663, 0.01492, 0.10374)),
                ]
                .into()
            );
        }
    }
}
