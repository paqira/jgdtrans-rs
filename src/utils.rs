//! Provides misc utilities.
use std::{fmt::Display, str::FromStr};

use crate::{error, Error, Result};

/// Returns the normalized latitude into -90.0 <= and <= 90.0.
///
/// We note that it may be interesting (the Earth is round).
///
/// # Example
///
/// ```
/// # use jgdtrans::utils::normalize_latitude;
/// assert_eq!(normalize_latitude(&35.0), 35.0);
/// assert_eq!(normalize_latitude(&100.0), 80.0);
/// assert_eq!(normalize_latitude(&190.0), -10.0);
/// assert_eq!(normalize_latitude(&-100.0), -80.0);
/// assert_eq!(normalize_latitude(&-190.0), 10.0);
/// assert!(normalize_latitude(&f64::NAN).is_nan());
/// ```
pub fn normalize_latitude(t: &f64) -> f64 {
    if t.is_nan() {
        return *t;
    };

    let t = t % 360.0;
    let res = if t.lt(&-270.0) || t.gt(&270.0) {
        t - f64::copysign(360.0, t)
    } else if t.lt(&-90.0) || t.gt(&90.0) {
        f64::copysign(180.0, t) - t
    } else {
        t
    };

    debug_assert!(res.ge(&-90.) && res.le(&90.));

    res
}

/// Returns the normalize longitude -180.0 <= and <= 180.0.
///
/// We note that it may be interesting (the Earth is round).
///
/// # Example
///
/// ```
/// # use jgdtrans::utils::normalize_longitude;
/// assert_eq!(normalize_longitude(&145.0), 145.0);
/// assert_eq!(normalize_longitude(&190.0), -170.0);
/// assert_eq!(normalize_longitude(&-190.0), 170.0);
/// assert!(normalize_longitude(&f64::NAN).is_nan());
/// ```
pub fn normalize_longitude(t: &f64) -> f64 {
    if t.is_nan() {
        return *t;
    };

    let t = t % 360.0;
    let res = if t.lt(&-180.0) || t.gt(&180.0) {
        t - f64::copysign(360.0, t)
    } else {
        t
    };

    debug_assert!(res.ge(&-180.) && res.le(&180.));

    res
}

/// Returns a DMS notation [`&str`] from a DD notation [`f64`].
///
/// This returns [`None`] if conversion failed.
///
/// # Example
///
/// ```
/// # use jgdtrans::utils::to_dms;
/// assert_eq!(to_dms(&36.103774791666666), Some("360613.589250000023299".to_string()));
/// assert_eq!(to_dms(&140.08785504166664), Some("1400516.278150000016467".to_string()));
/// ```
pub fn to_dms(t: &f64) -> Option<String> {
    DMS::try_from(t).ok().map(|x| x.to_string())
}

/// Returns a DD notation [`f64`] from a DMS notation [`&str`].
///
/// This returns [`None`] if conversion failed.
///
/// # Example
///
/// ```
/// # use jgdtrans::utils::from_dms;
/// assert_eq!(from_dms("360613.58925"), Some(36.103774791666666));
/// assert_eq!(from_dms("1400516.27815"), Some(140.08785504166667));
/// ```
pub fn from_dms(s: &str) -> Option<f64> {
    s.parse::<DMS>().ok().map(|x| x.into())
}

/// Signiture of DMS
#[derive(Debug, PartialEq)]
pub enum Sign {
    /// Plus
    Plus,
    /// Minus
    Minus,
}

/// Represents DMS notation latitude and/or longtiude.
///
/// This supports -180.0 <= and <= 180.0 angle in degree (DD notation).
///
/// # Example
///
/// ```
/// # use jgdtrans::*;
/// use jgdtrans::utils::{DMS, Sign};
/// # fn main() -> Result<()> {
///
/// let latitude = DMS::try_new(Sign::Plus, 36, 6, 13, 0.58925)?;
///
/// // prints DMS { sign: Plus, degree: 36, minute: 6, second: 13, fract: 0.58925 }
/// println!("{latitude:?}");
/// // prints "360613.58925"
/// println!("{latitude}");
///
/// // Construct from &str
/// assert_eq!(latitude, "360613.58925".parse::<DMS>()?);
///
/// // Convert into DD notation f64
/// assert_eq!(latitude.to_degree(), 36.103774791666666);
///
/// // Construct from DD notation f64
/// let latitude = DMS::try_from(36.103774791666666)?;
/// assert_eq!(latitude.sign(), &Sign::Plus);
/// assert_eq!(latitude.degree(), &36);
/// assert_eq!(latitude.minute(), &6);
/// assert_eq!(latitude.second(), &13);
/// assert!((0.58925 - latitude.fract()).abs() < 1e-10);
/// # Ok(())}
/// ```
#[derive(Debug, PartialEq)]
pub struct DMS {
    sign: Sign,
    degree: u8,
    minute: u8,
    second: u8,
    fract: f64,
}

impl Display for DMS {
    /// Returns a DMS notation [`&str`] which represents `self`.
    ///
    /// The fraction has 15 digits at most.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::utils::{DMS, Sign};
    /// # fn main() -> Result<()> {
    /// let dms = DMS::try_new(Sign::Plus, 36, 6, 13, 0.58925)?;
    /// assert_eq!(dms.to_string(), "360613.58925");
    /// let dms = DMS::try_new(Sign::Plus, 140, 5, 16, 0.27815)?;
    /// assert_eq!(dms.to_string(), "1400516.27815");
    /// # Ok(())}
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self.sign {
            Sign::Plus => "",
            Sign::Minus => "-",
        };

        let formatted = format!("{:.15}", self.fract);
        let mut parts = formatted.split('.');

        // drop integer part
        parts.next();

        // take fraction part
        let fract = match parts.next().unwrap().trim_end_matches('0') {
            "" => "0",
            x => x,
        };

        match (self.degree, self.minute, self.second) {
            (0, 0, sec) => write!(f, "{}{}.{}", s, sec, fract),
            (0, min, sec) => write!(f, "{}{}{:02}.{}", s, min, sec, fract),
            (deg, min, sec) => write!(f, "{}{}{:02}{:02}.{}", s, deg, min, sec, fract),
        }
    }
}

impl FromStr for DMS {
    type Err = Error;

    /// Makes a [`DMS`] from DMS notation [`&str`].
    ///
    /// This supports all of the common notation,
    /// e.g. 1.2, 1, +1., -.2, etc.
    ///
    /// # Errors
    ///
    /// If `s` is invalid or out-of-range.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::utils::{DMS, Sign};
    /// # fn main() -> Result<()> {
    /// assert_eq!(
    ///     "360613.58925".parse::<DMS>()?,
    ///     DMS::try_new(Sign::Plus, 36, 6, 13, 0.58925)?
    /// );
    /// assert_eq!(
    ///     "1400516.27815".parse::<DMS>()?,
    ///     DMS::try_new(Sign::Plus, 140, 5, 16, 0.27815)?
    /// );
    /// # Ok(())}
    /// ```
    fn from_str(s: &str) -> Result<Self> {
        // integer-like
        if let Some(res) = Self::parse_integer(s) {
            return Self::try_new(res.0, res.1, res.2, res.3, 0.0)
                .map_err(|_| Error::new_parse_dms_error(s.to_string()));
        }

        // float-like
        let mut parts = s.split('.');

        let integer = parts.next();
        let fraction = parts.next();

        // too many '.'
        if parts.next().is_some() {
            return Err(Error::new_parse_dms_error(s.to_string()));
        };

        match (integer, fraction) {
            //
            // empty fraction part
            //
            // "1"
            (Some(i), None) => {
                let res =
                    Self::parse_integer(i).ok_or(Error::new_parse_dms_error(s.to_string()))?;
                Self::try_new(res.0, res.1, res.2, res.3, 0.0)
            }
            // "1."
            (Some(i), Some("")) => {
                let res =
                    Self::parse_integer(i).ok_or(Error::new_parse_dms_error(s.to_string()))?;
                Self::try_new(res.0, res.1, res.2, res.3, 0.0)
            }
            //
            // empty integer part
            //
            // "+.1" or ".1"
            (Some(i), Some(f)) if i.eq("+") || i.is_empty() => match Self::perse_fraction(f) {
                Some(fract) => Self::try_new(Sign::Plus, 0, 0, 0, fract),
                _ => Err(Error::new_parse_dms_error(s.to_string())),
            },
            // "-.1"
            (Some(i), Some(f)) if i.eq("-") => match Self::perse_fraction(f) {
                Some(fract) => Self::try_new(Sign::Minus, 0, 0, 0, fract),
                _ => Err(Error::new_parse_dms_error(s.to_string())),
            },
            //
            // formal float
            //
            // "1.1"
            (Some(i), Some(f)) => {
                let res =
                    Self::parse_integer(i).ok_or(Error::new_parse_dms_error(s.to_string()))?;
                let fract =
                    Self::perse_fraction(f).ok_or(Error::new_parse_dms_error(s.to_string()))?;
                Self::try_new(res.0, res.1, res.2, res.3, fract)
            }
            _ => Err(Error::new_parse_dms_error(s.to_string())),
        }
    }
}

impl TryFrom<f64> for DMS {
    type Error = Error;

    /// Makes a [`DMS`] from DD notation [`f64`]
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::utils::{DMS, Sign};
    /// # fn main() -> Result<()> {
    /// assert_eq!(
    ///     DMS::try_from(36.103774791666666)?,
    ///     DMS::try_new(Sign::Plus, 36, 6, 13, 0.5892500000232985)?
    /// );
    /// assert_eq!(
    ///     DMS::try_from(140.08785504166664)?,
    ///     DMS::try_new(Sign::Plus, 140, 5, 16, 0.27815000001646695)?
    /// );
    /// # Ok(())}
    /// ```
    fn try_from(value: f64) -> Result<Self> {
        // FIXME:
        // Support the identity on full range, -180 to 180
        if value.is_nan() || value.lt(&-180.0) || value.gt(&180.0) {
            return Err(Error {
                err: Box::new(error::ErrorImpl::OutOfRangeDegree {
                    low: -180.,
                    high: 180.,
                    degree: value,
                }),
            });
        };

        // FIXME: dirty dirty hack
        let mm = 60. * value.abs().next_up().fract();
        let ss = 60. * mm.fract();

        let sign = if value.signum().eq(&1.0) {
            Sign::Plus
        } else {
            Sign::Minus
        };
        let degree = value.trunc().abs() as u8;
        let minute = mm.trunc() as u8;
        let second = ss.trunc() as u8;
        let fract = ss.fract();

        // verify
        if cfg!(debug_assert) && degree.eq(&180) {
            debug_assert!((minute.eq(&0) && second.eq(&0) && fract.eq(&0.0)));
        };
        debug_assert!(second.le(&60), "got {value:?}, expected second <= 60");
        debug_assert!(minute.le(&60), "got {value:?}, expected minute <= 60");
        debug_assert!(degree.le(&180), "got {value:?}, expected degree <= 180");

        // handle carry by binary64 rounding error
        let (carry, second) = (second / 60, second % 60);
        let minute: u8 = minute + carry;

        let (carry, minute) = (minute / 60, minute % 60);
        let degree = degree + carry;

        Self::try_new(sign, degree, minute, second, fract)
    }
}

impl TryFrom<&f64> for DMS {
    type Error = Error;

    /// Makes a [`DMS`] from DD notation [`f64`].
    ///
    /// See [`DMS::try_from<f64>`].
    fn try_from(value: &f64) -> Result<Self> {
        Self::try_from(*value)
    }
}

impl From<DMS> for f64 {
    /// Returns a DD notation [`f64`] that `self` converts into.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::utils::{DMS, Sign};
    /// # fn main() -> Result<()> {
    /// let dms = DMS::try_new(Sign::Plus, 36, 6, 13, 0.58925)?;
    /// assert_eq!(f64::from(dms), 36.103774791666666);
    ///
    /// let dms = DMS::try_new(Sign::Minus, 36, 6, 13, 0.58925)?;
    /// assert_eq!(f64::from(dms), -36.103774791666666);
    /// # Ok(())}
    /// ```
    fn from(value: DMS) -> Self {
        Self::from(&value)
    }
}

impl From<&DMS> for f64 {
    /// Returns a DD notation [`f64`] that `self` converts into.
    fn from(value: &DMS) -> Self {
        let mm = value.minute as f64 / 60.;
        let ss = (value.second as f64 + value.fract) / 3600.0;
        let res = (value.degree as f64) + mm + ss;

        match value.sign {
            Sign::Plus => res,
            Sign::Minus => -res,
        }
    }
}

impl DMS {
    /// Makes a [`DMS`].
    ///
    /// # Errors
    ///
    /// If all the following conditions does not hold;
    ///
    /// - `degree` satisries 0 <= and <= 180,
    /// - `minute` does 0 <= and < 60,
    /// - `second` does 0 <= and < 60,
    /// - and `fract` does 0.0 <= and < 1.0.
    /// - Additionally, `minute`, `second` and `fract` is zero if `degree` is 180.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::utils::{DMS, Sign};
    /// # fn main() -> Result<()> {
    /// let dms = DMS::try_new(Sign::Plus, 36, 6, 13, 0.58925)?;
    /// assert_eq!(dms.sign(), &Sign::Plus);
    /// assert_eq!(dms.degree(), &36);
    /// assert_eq!(dms.minute(), &6);
    /// assert_eq!(dms.second(), &13);
    /// assert_eq!(dms.fract(), &0.58925);
    /// # Ok(())}
    /// ```
    pub fn try_new(sign: Sign, degree: u8, minute: u8, second: u8, fract: f64) -> Result<Self> {
        if degree.eq(&180) && (minute.gt(&0) || second.gt(&0) || fract.gt(&0.0))
            || degree.gt(&180)
            || minute.ge(&60)
            || second.ge(&60)
            || fract.lt(&0.0)
            || fract.ge(&1.0)
        {
            return Err(Error {
                err: Box::new(error::ErrorImpl::OutOfRangeDMS {
                    degree,
                    minute,
                    second,
                    fract,
                }),
            });
        }

        Ok(Self {
            sign,
            degree,
            minute,
            second,
            fract,
        })
    }

    /// Returns the sign of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::utils::{DMS, Sign};
    /// # fn main() -> Result<()> {
    /// let dms = DMS::try_new(Sign::Plus, 36, 6, 13, 0.58925)?;
    /// assert_eq!(dms.sign(), &Sign::Plus);
    /// # Ok(())}
    /// ```
    pub fn sign(&self) -> &Sign {
        &self.sign
    }

    /// Returns the degree of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::utils::{DMS, Sign};
    /// # fn main() -> Result<()> {
    /// let dms = DMS::try_new(Sign::Plus, 36, 6, 13, 0.58925)?;
    /// assert_eq!(dms.degree(), &36);
    /// # Ok(())}
    /// ```
    pub fn degree(&self) -> &u8 {
        &self.degree
    }

    /// Returns the minute of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::utils::{DMS, Sign};
    /// # fn main() -> Result<()> {
    /// let dms = DMS::try_new(Sign::Plus, 36, 6, 13, 0.58925)?;
    /// assert_eq!(dms.minute(), &6);
    /// # Ok(())}
    /// ```
    pub fn minute(&self) -> &u8 {
        &self.minute
    }

    /// Returns the integer part of second of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::utils::{DMS, Sign};
    /// # fn main() -> Result<()> {
    /// let dms = DMS::try_new(Sign::Plus, 36, 6, 13, 0.58925)?;
    /// assert_eq!(dms.second(), &13);
    /// # Ok(())}
    /// ```
    pub fn second(&self) -> &u8 {
        &self.second
    }

    /// Returns the fraction part of second of `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::utils::{DMS, Sign};
    /// # fn main() -> Result<()> {
    /// let dms = DMS::try_new(Sign::Plus, 36, 6, 13, 0.58925)?;
    /// assert_eq!(dms.fract(), &0.58925);
    /// # Ok(())}
    /// ```
    pub fn fract(&self) -> &f64 {
        &self.fract
    }

    fn parse_integer(s: &str) -> Option<(Sign, u8, u8, u8)> {
        let sign = if s.starts_with('-') {
            Sign::Minus
        } else {
            Sign::Plus
        };

        let i = s.parse::<i64>().ok()?.abs();
        let degree = u8::try_from(i / 10000).ok()?;

        let rest = i % 10000;
        let minute = u8::try_from(rest / 100).ok()?;
        let second = u8::try_from(rest % 100).ok()?;
        Some((sign, degree, minute, second))
    }

    fn perse_fraction(s: &str) -> Option<f64> {
        if s.is_empty() {
            None
        } else {
            ("0.".to_string() + s).parse::<f64>().ok()
        }
    }

    /// Makes a [`DMS`] from DD notation [`f64`].
    ///
    /// `t` is angle which safisfies -180.0 <= and <= 180.0.
    ///
    /// # Errors
    ///
    /// If `t` is out-of-range.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::utils::{DMS, Sign};
    /// # fn main() -> Result<()> {
    /// assert_eq!(
    ///     DMS::try_from_dd(&36.103774791666666)?,
    ///     DMS::try_new(Sign::Plus, 36, 6, 13, 0.5892500000232985)?
    /// );
    /// assert_eq!(
    ///     DMS::try_from_dd(&140.08785504166664)?,
    ///     DMS::try_new(Sign::Plus, 140, 5, 16, 0.27815000001646695)?
    /// );
    /// # Ok(())}
    /// ```
    pub fn try_from_dd(t: &f64) -> Result<Self> {
        t.try_into()
    }

    /// Returns a DD notation [`f64`] that `self` converts into.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::utils::{DMS, Sign};
    /// # fn main() -> Result<()> {
    /// let dms = DMS::try_new(Sign::Plus, 36, 6, 13, 0.58925)?;
    /// assert_eq!(
    ///     dms.to_degree(),
    ///     36.103774791666666
    ///     
    /// );
    /// let dms = DMS::try_new(Sign::Minus, 36, 6, 13, 0.58925)?;
    /// assert_eq!(
    ///     dms.to_degree(),
    ///     -36.103774791666666,
    /// );
    /// # Ok(())}
    /// ```
    pub fn to_degree(&self) -> f64 {
        f64::from(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    mod tests_dms {
        use super::*;

        #[test]
        fn test_try_new() {
            // error
            assert!(DMS::try_new(Sign::Plus, 0, 0, 0, 0.0_f64.next_down()).is_err());
            assert!(DMS::try_new(Sign::Plus, 0, 0, 0, 1.0_f64.next_up()).is_err());
            assert!(DMS::try_new(Sign::Plus, 0, 0, 60, 0.0).is_err());
            assert!(DMS::try_new(Sign::Plus, 0, 60, 0, 0.0).is_err());
            assert!(DMS::try_new(Sign::Plus, 180, 0, 0, 1.0_f64.next_up()).is_err());
            assert!(DMS::try_new(Sign::Plus, 180, 0, 1, 0.0).is_err());
            assert!(DMS::try_new(Sign::Plus, 180, 1, 0, 0.0).is_err());

            // healthy
            assert!(DMS::try_new(Sign::Plus, 180, 0, 0, 0.0).is_ok());
        }

        #[test]
        fn test_to_string() {
            let cases = [
                (DMS::try_new(Sign::Plus, 0, 0, 0, 0.0), "0.0"),
                (DMS::try_new(Sign::Minus, 0, 0, 0, 0.0), "-0.0"),
                (DMS::try_new(Sign::Plus, 0, 0, 0, 0.000012), "0.000012"),
                (DMS::try_new(Sign::Minus, 0, 0, 0, 0.000012), "-0.000012"),
                (DMS::try_new(Sign::Plus, 0, 0, 1, 0.0), "1.0"),
                (DMS::try_new(Sign::Minus, 0, 0, 1, 0.0), "-1.0"),
                (DMS::try_new(Sign::Plus, 0, 0, 10, 0.0), "10.0"),
                (DMS::try_new(Sign::Minus, 0, 0, 10, 0.0), "-10.0"),
                (DMS::try_new(Sign::Plus, 0, 1, 0, 0.0), "100.0"),
                (DMS::try_new(Sign::Minus, 0, 1, 0, 0.0), "-100.0"),
                (DMS::try_new(Sign::Plus, 1, 0, 0, 0.0), "10000.0"),
                (DMS::try_new(Sign::Minus, 1, 0, 0, 0.0), "-10000.0"),
                (DMS::try_new(Sign::Plus, 1, 1, 1, 0.0), "10101.0"),
                (DMS::try_new(Sign::Minus, 1, 1, 1, 0.0), "-10101.0"),
            ];

            for (a, e) in cases {
                assert_eq!(a.unwrap().to_string(), e);
            }
        }

        #[test]
        fn test_from_str() {
            let cases = [
                // sign
                ("00", DMS::try_new(Sign::Plus, 0, 0, 0, 0.0)),
                ("-00", DMS::try_new(Sign::Minus, 0, 0, 0, 0.0)),
                ("00.0", DMS::try_new(Sign::Plus, 0, 0, 0, 0.0)),
                ("-00.0", DMS::try_new(Sign::Minus, 0, 0, 0, 0.0)),
                ("00.", DMS::try_new(Sign::Plus, 0, 0, 0, 0.0)),
                ("-00.", DMS::try_new(Sign::Minus, 0, 0, 0, 0.0)),
                (".00", DMS::try_new(Sign::Plus, 0, 0, 0, 0.0)),
                ("-.00", DMS::try_new(Sign::Minus, 0, 0, 0, 0.0)),
                // healthy
                ("123456", DMS::try_new(Sign::Plus, 12, 34, 56, 0.0)),
                ("-123456", DMS::try_new(Sign::Minus, 12, 34, 56, 0.0)),
                ("123456.78", DMS::try_new(Sign::Plus, 12, 34, 56, 0.78)),
                ("-123456.78", DMS::try_new(Sign::Minus, 12, 34, 56, 0.78)),
                ("123456.", DMS::try_new(Sign::Plus, 12, 34, 56, 0.0)),
                ("-123456.", DMS::try_new(Sign::Minus, 12, 34, 56, 0.0)),
                (".78", DMS::try_new(Sign::Plus, 0, 0, 0, 0.78)),
                ("-.78", DMS::try_new(Sign::Minus, 0, 0, 0, 0.78)),
            ];
            for (a, e) in cases {
                assert_eq!(DMS::from_str(a).unwrap(), e.unwrap());
            }

            // error
            let cases = [
                "", "-", "a", "-a", ".", "-.", "..", "-..", "..0", "-..0", ".0.", "-.0.", "0..",
                "-0..",
            ];
            for c in cases {
                assert!(DMS::from_str(c).is_err());
            }
        }

        #[test]
        fn test_into_f64() {
            let dms = DMS::try_new(Sign::Plus, 36, 6, 13, 0.58925).unwrap();
            assert!((36.103774791666666 - f64::from(dms)).abs() < 1e-10);

            let dms = DMS::try_new(Sign::Plus, 140, 5, 16, 0.27815).unwrap();
            assert!((140.08785504166664 - f64::from(dms)).abs() < 1e-10);
        }

        #[test]
        fn test_from_f64() {
            let dms = DMS::try_new(Sign::Plus, 36, 6, 13, 0.58925).unwrap();
            let result = DMS::try_from(36.103774791666666).unwrap();
            assert_eq!(dms.sign, result.sign);
            assert_eq!(dms.degree, result.degree);
            assert_eq!(dms.minute, result.minute);
            assert_eq!(dms.second, result.second);
            assert!((result.fract - dms.fract).abs() < 3e-10);

            let dms = DMS::try_new(Sign::Plus, 140, 5, 16, 0.27815).unwrap();
            let result = DMS::try_from(140.08785504166664).unwrap();
            assert_eq!(dms.sign, result.sign);
            assert_eq!(dms.degree, result.degree);
            assert_eq!(dms.minute, result.minute);
            assert_eq!(dms.second, result.second);
            assert!((result.fract - dms.fract).abs() < 3e-10);

            assert!(DMS::try_from(f64::NAN).is_err());
            assert!(DMS::try_from((-180.0_f64).next_down()).is_err());
            assert!(DMS::try_from(180.0_f64.next_up()).is_err());
        }

        #[test]
        fn test_identity_exact() {
            for deg in 20..161 {
                for min in 0..60 {
                    for sec in 0..60 {
                        // plus
                        let dms = DMS::try_new(Sign::Plus, deg, min, sec, 0.0).unwrap();
                        let degree: f64 = (&dms).into();
                        let result = DMS::try_from(degree).unwrap();

                        assert_eq!(dms.sign, result.sign, "dms: {dms:?}, result: {result:?}");
                        assert_eq!(
                            dms.degree, result.degree,
                            "dms: {dms:?}, result: {result:?}"
                        );
                        assert_eq!(
                            dms.minute, result.minute,
                            "dms: {dms:?}, result: {result:?}"
                        );
                        assert_eq!(
                            dms.second, result.second,
                            "dms: {dms:?}, result: {result:?}"
                        );
                        assert!(
                            (result.fract - dms.fract).abs() < 3e-10,
                            "dms: {dms:?}, result: {result:?}"
                        );
                        assert!((result.to_degree() - degree).abs() < 3e-10);

                        // minus
                        let dms = DMS::try_new(Sign::Minus, deg, min, sec, 0.0).unwrap();
                        let degree: f64 = (&dms).into();
                        let result = DMS::try_from(degree).unwrap();

                        assert_eq!(dms.sign, result.sign, "dms: {dms:?}, result: {result:?}");
                        assert_eq!(
                            dms.degree, result.degree,
                            "dms: {dms:?}, result: {result:?}"
                        );
                        assert_eq!(
                            dms.minute, result.minute,
                            "dms: {dms:?}, result: {result:?}"
                        );
                        assert_eq!(
                            dms.second, result.second,
                            "dms: {dms:?}, result: {result:?}"
                        );
                        assert!(
                            (result.fract - dms.fract).abs() < 3e-10,
                            "dms: {dms:?}, result: {result:?}"
                        );
                        assert!((result.to_degree() - degree).abs() < 3e-10);
                    }
                }
            }
        }

        // #[test]
        // fn test_identity_less_than() {
        //     for deg in 20..161 {
        //         for min in 0..59 {
        //             for sec in 0..59 {
        //                 // plus
        //                 let dms =
        //                     DMS::try_new(Sign::Plus, deg, min, sec, 1.0_f64.next_down()).unwrap();
        //                 let degree: f64 = (&dms).into();
        //                 let result = DMS::try_from(degree).unwrap();

        //                 let dms = DMS::try_new(Sign::Plus, deg, min, sec + 1, 0.0).unwrap();

        //                 assert_eq!(dms.sign, result.sign, "dms: {dms:?}, result: {result:?}");
        //                 assert_eq!(
        //                     dms.degree, result.degree,
        //                     "dms: {dms:?}, result: {result:?}"
        //                 );
        //                 assert_eq!(
        //                     dms.minute, result.minute,
        //                     "dms: {dms:?}, result: {result:?}"
        //                 );
        //                 assert_eq!(
        //                     dms.second, result.second,
        //                     "dms: {dms:?}, result: {result:?}"
        //                 );
        //                 assert!(
        //                     (result.fract - dms.fract).abs() < 3e-11,
        //                     "dms: {dms:?}, result: {result:?}"
        //                 );
        //                 assert!((result.to_degree() - degree).abs() < 3e-11);

        //                 // minus
        //                 let dms =
        //                     DMS::try_new(Sign::Minus, deg, min, sec, 1.0_f64.next_down()).unwrap();
        //                 let degree: f64 = (&dms).into();
        //                 let result = DMS::try_from(degree).unwrap();

        //                 let dms = DMS::try_new(Sign::Minus, deg, min, sec + 1, 0.0).unwrap();

        //                 assert_eq!(dms.sign, result.sign, "dms: {dms:?}, result: {result:?}");
        //                 assert_eq!(
        //                     dms.degree, result.degree,
        //                     "dms: {dms:?}, result: {result:?}"
        //                 );
        //                 assert_eq!(
        //                     dms.minute, result.minute,
        //                     "dms: {dms:?}, result: {result:?}"
        //                 );
        //                 assert_eq!(
        //                     dms.second, result.second,
        //                     "dms: {dms:?}, result: {result:?}"
        //                 );
        //                 assert!(
        //                     (result.fract - dms.fract).abs() < 3e-11,
        //                     "dms: {dms:?}, result: {result:?}"
        //                 );
        //                 assert!((result.to_degree() - degree).abs() < 3e-11);
        //             }
        //         }
        //     }
        // }
    }
}
