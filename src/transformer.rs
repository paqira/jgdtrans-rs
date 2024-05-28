//! Provides [`Transformer`] etc.
use std::collections::HashMap;
use std::hash::{BuildHasher, RandomState};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::{Format, ParseParError};

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
/// if the parameter does not exist, as the parser does.
///
/// # Example
///
/// ```
/// # use jgdtrans::*;
/// #
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
    /// # use jgdtrans::*;
    /// #
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
/// We emphasize that the unit of latitude and longitude
/// is \[deg\], not \[sec\].
///
/// It should fill with 0.0 instead of [`NAN`](f64::NAN).
///
/// # Example
///
/// ```
/// # use jgdtrans::*;
/// #
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
    /// # use jgdtrans::*;
    /// #
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
#[derive(Debug, PartialEq, Clone)]
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
    fn from_array(vs: &[f64]) -> Self {
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
        let count = vs.len();
        if sum.is_nan() {
            return Self {
                count: Some(count),
                mean: Some(f64::NAN),
                std: Some(f64::NAN),
                abs: Some(f64::NAN),
                min: Some(f64::NAN),
                max: Some(f64::NAN),
            };
        }

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
#[derive(Debug, Clone)]
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
/// There is a builder, see [`TransformerBuilder`](crate::TransformerBuilder).
///
/// # Example
///
/// ```
/// # use std::collections::HashMap;
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
/// // forward transformation
/// let origin = Point::new(36.10377479, 140.087855041, 2.34);
/// let result = tf.forward(&origin)?;
/// assert_eq!(result.latitude, 36.103773017086695);
/// assert_eq!(result.longitude, 140.08785924333452);
/// assert_eq!(result.altitude, 2.4363138578103);
/// # Ok::<(), TransformError>(())
/// ```
#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Transformer<
    #[cfg(not(feature = "serde"))] S = RandomState,
    #[cfg(feature = "serde")] S: Default = RandomState,
> {
    /// The format of par file.
    pub format: Format,
    /// The transformation parameter.
    ///
    /// The entry represents single line of par-formatted file's parameter section,
    /// the key is meshcode, and the value parameter.
    #[cfg_attr(
        feature = "serde",
        serde(bound(
            serialize = "HashMap<u32, Parameter, S>: Serialize",
            deserialize = "HashMap<u32, Parameter, S>: Deserialize<'de>"
        ))
    )]
    pub parameter: HashMap<u32, Parameter, S>,
    /// The description, or the header of par-formatted data.
    #[cfg_attr(feature = "serde", serde(skip_serializing_if = "Option::is_none"))]
    pub description: Option<String>,
}

impl<#[cfg(not(feature = "serde"))] S, #[cfg(feature = "serde")] S: Default> Transformer<S> {
    /// Max error of backward transformation.
    ///
    /// Used by [`Transformer::backward`], [`Transformer::backward_corr`]
    /// [`Transformer::unchecked_backward`] and [`Transformer::unchecked_backward_corr`].
    pub const MAX_ERROR: f64 = 5e-14;

    /// Makes a [`Transformer`].
    ///
    /// We note that we provide a builder, see [`TransformerBuilder`](crate::TransformerBuilder).
    ///
    /// # Example
    ///
    /// ```
    /// # use std::collections::HashMap;
    /// use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// #
    /// // from SemiDynaEXE2023.par
    /// let tf = Transformer::new(
    ///     Format::SemiDynaEXE,
    ///     HashMap::from([
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///     ])
    /// );
    ///
    /// assert_eq!(tf.format, Format::SemiDynaEXE);
    /// assert_eq!(tf.format.mesh_unit(), MeshUnit::Five);
    /// assert_eq!(
    ///     tf.parameter,
    ///     HashMap::from([
    ///         (54401005, Parameter::new(-0.00622, 0.01516, 0.0946)),
    ///         (54401055, Parameter::new(-0.0062, 0.01529, 0.08972)),
    ///     ])
    /// );
    /// assert_eq!(tf.description, None);
    /// ```
    #[inline]
    pub const fn new(format: Format, parameter: HashMap<u32, Parameter, S>) -> Self {
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
    /// # use std::collections::HashMap;
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// #
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
        parameter: HashMap<u32, Parameter, S>,
        description: String,
    ) -> Self {
        Self {
            format,
            parameter,
            description: Some(description),
        }
    }

    /// Returns the statistics of the parameter.
    ///
    /// See [`StatisticData`] for details of result's components.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::collections::HashMap;
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
        // it's not optimal, but length of parameters is enough small

        // ensure summation order
        let mut sorted: Vec<_> = self.parameter.iter().collect();
        sorted.sort_by_key(|t| t.0);

        let arr: Vec<f64> = sorted.iter().map(|t| t.1.latitude).collect();
        let latitude = StatisticData::from_array(&arr);

        let arr: Vec<f64> = sorted.iter().map(|t| t.1.longitude).collect();
        let longitude = StatisticData::from_array(&arr);

        let arr: Vec<f64> = sorted.iter().map(|t| t.1.altitude).collect();
        let altitude = StatisticData::from_array(&arr);

        let arr: Vec<f64> = sorted.iter().map(|t| t.1.horizontal()).collect();
        let horizontal = StatisticData::from_array(&arr);

        Statistics {
            latitude,
            longitude,
            altitude,
            horizontal,
        }
    }
}

impl Transformer<RandomState> {
    /// Deserialize par-formatted [`&str`] into a [`Transformer`].
    ///
    /// Use `format` argument to specify the format of `s`.
    ///
    /// This fills by 0.0 for altitude parameter when [`Format::TKY2JGD`] or [`Format::PatchJGD`] given,
    /// and for latitude and longitude when [`Format::PatchJGD_H`] or [`Format::HyokoRev`] given.
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
    /// #
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
    ///
    /// assert_eq!(tf.format, Format::SemiDynaEXE);
    /// assert_eq!(
    ///     tf.parameter.get(&12345678),
    ///     Some(&Parameter::new(0.00001, 0.00002, 0.00003))
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[inline]
    pub fn from_str(s: &str, format: Format) -> std::result::Result<Self, ParseParError> {
        crate::par::from_str(s, format)
    }

    /// Deserialize par-formatted [`&str`] into a [`Transformer`] with description.
    ///
    /// See [`Transformer::from_str`] for detail.
    /// # Errors
    ///
    /// Returns [`Err`] when the invalid data found.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// #
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
    ///
    /// assert_eq!(tf.format, Format::SemiDynaEXE);
    /// assert_eq!(
    ///     tf.parameter.get(&12345678),
    ///     Some(&Parameter::new(0.00001, 0.00002, 0.00003))
    /// );
    /// assert_eq!(tf.description, Some("SemiDyna2023.par".to_string()));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[inline]
    pub fn from_str_with_description(
        s: &str,
        format: Format,
        description: String,
    ) -> std::result::Result<Self, ParseParError> {
        crate::par::Parser::new(format).parse_with_description(s, description)
    }
}

impl<#[cfg(not(feature = "serde"))] S, #[cfg(feature = "serde")] S: Default> PartialEq
    for Transformer<S>
where
    S: BuildHasher,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.format.eq(&other.format)
            && self.description.eq(&other.description)
            && self.parameter.eq(&other.parameter)
    }
}

impl<#[cfg(not(feature = "serde"))] S, #[cfg(feature = "serde")] S: Default> Clone
    for Transformer<S>
where
    S: Clone,
{
    #[inline]
    fn clone(&self) -> Self {
        Self {
            format: self.format.clone(),
            parameter: self.parameter.clone(),
            description: self.description.clone(),
        }
    }

    #[inline]
    fn clone_from(&mut self, source: &Self) {
        self.format.clone_from(&source.format);
        self.parameter.clone_from(&source.parameter);
        self.description.clone_from(&source.description);
    }
}

#[cfg(test)]
mod test {
    use crate::TransformerBuilder;

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
            // The difference comes from libc?
            // It's up to 1 ulp.
            assert_eq!(
                stats.horizontal,
                StatisticData {
                    count: Some(4),
                    mean: Some(if cfg!(target_os = "linux") {
                        0.016417802947905496
                    } else {
                        0.0164178029479055
                    }),
                    std: Some(if cfg!(target_os = "linux") {
                        0.04925345347374167
                    } else {
                        0.04925345347374168
                    }),
                    abs: Some(if cfg!(target_os = "linux") {
                        0.016417802947905496
                    } else {
                        0.0164178029479055
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
    }
}
