//! Provides utilities for DMS notation degree.
use std::error::Error;
use std::fmt::{Display, Formatter};
use std::num::IntErrorKind;
use std::str::FromStr;

/// Returns a DMS notation [`str`] from a DD notation [`f64`].
///
/// This returns [`None`] if conversion failed.
///
/// # Example
///
/// ```
/// # use jgdtrans::dms::to_dms;
/// assert_eq!(to_dms(&36.103774791666666), Some("360613.589249999997719".to_string()));
/// assert_eq!(to_dms(&140.08785504166664), Some("1400516.278149999914149".to_string()));
/// ```
pub fn to_dms(t: &f64) -> Option<String> {
    DMS::try_from(t).ok().map(|x| x.to_string())
}

/// Returns a DD notation [`f64`] from a DMS notation [`str`].
///
/// This returns [`None`] if conversion failed.
///
/// # Example
///
/// ```
/// # use jgdtrans::dms::from_dms;
/// assert_eq!(from_dms("360613.58925"), Some(36.103774791666666));
/// assert_eq!(from_dms("1400516.27815"), Some(140.08785504166667));
/// ```
pub fn from_dms(s: &str) -> Option<f64> {
    s.parse::<DMS>().ok().map(|x| x.to_degree())
}

/// Signature of DMS
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum Sign {
    /// Plus
    Plus,
    /// Minus
    Minus,
}

/// Represents DMS notation latitude and/or longitude.
///
/// This supports -180.0 <= and <= 180.0 angle in degree (DD notation).
///
/// # Example
///
/// ```
/// # use std::error::Error;
/// # use jgdtrans::*;
/// use jgdtrans::dms::{DMS, Sign};
/// # fn main() -> Result<(), Box<dyn Error>> {
///
/// let latitude = DMS::try_new(Sign::Plus, 36, 6, 13, 0.58925).unwrap();
///
/// // prints DMS { sign: Plus, degree: 36, minute: 6, second: 13, fract: 0.58925 }
/// println!("{:?}", latitude);
/// // prints "360613.58925"
/// println!("{}", latitude);
///
/// // Construct from &str
/// assert_eq!(latitude, "360613.58925".parse::<DMS>()?);
///
/// // Convert into DD notation f64
/// assert_eq!(latitude.to_degree(), 36.103774791666666);
///
/// // Construct from DD notation f64
/// let latitude = DMS::try_from(&36.103774791666666)?;
/// assert_eq!(latitude.sign(), &Sign::Plus);
/// assert_eq!(latitude.degree(), &36);
/// assert_eq!(latitude.minute(), &6);
/// assert_eq!(latitude.second(), &13);
/// assert!((0.58925 - latitude.fract()).abs() < 1e-10);
/// # Ok(())}
/// ```
#[derive(Debug, PartialEq, Clone)]
pub struct DMS {
    sign: Sign,
    degree: u8,
    minute: u8,
    second: u8,
    fract: f64,
}

impl Display for DMS {
    /// Returns a DMS notation [`str`] which represents `self`.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::dms::{DMS, Sign};
    /// # fn run() -> Option<()> {
    /// let dms = DMS::try_new(Sign::Plus, 36, 6, 13, 0.58925)?;
    /// assert_eq!(dms.to_string(), "360613.58925");
    /// let dms = DMS::try_new(Sign::Plus, 140, 5, 16, 0.27815)?;
    /// assert_eq!(dms.to_string(), "1400516.27815");
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.sign {
            Sign::Plus => {}
            Sign::Minus => write!(f, "-")?,
        };

        match (self.degree, self.minute, self.second) {
            (0, 0, sec) => write!(f, "{}", sec)?,
            (0, min, sec) => write!(f, "{}{:02}", min, sec)?,
            (deg, min, sec) => write!(f, "{}{:02}{:02}", deg, min, sec)?,
        };

        let s = format!("{:.15}", self.fract);
        if let Some((_, fract)) = s.trim_end_matches('0').split_once('.') {
            if fract.is_empty() {
                write!(f, ".0")?
            } else {
                write!(f, ".{}", fract)?
            }
        };

        Ok(())
    }
}

impl FromStr for DMS {
    type Err = ParseDMSError;

    /// Makes a [`DMS`] from DMS notation [`&str`].
    ///
    /// This supports all the common notation,
    /// e.g. 1.2, 1, +1., -.2, etc.
    ///
    /// # Errors
    ///
    /// When `s` is invalid or out-of-range.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// # use jgdtrans::dms::{DMS, Sign};
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// assert_eq!(
    ///     "360613.58925".parse::<DMS>()?,
    ///     DMS::try_new(Sign::Plus, 36, 6, 13, 0.58925).unwrap()
    /// );
    /// assert_eq!(
    ///     "1400516.27815".parse::<DMS>()?,
    ///     DMS::try_new(Sign::Plus, 140, 5, 16, 0.27815).unwrap()
    /// );
    /// # Ok(())}
    /// ```
    fn from_str(s: &str) -> Result<Self, ParseDMSError> {
        // float-like
        let mut parts = s.split('.');

        let integer = parts.next();
        let fraction = parts.next();

        // too many '.'
        if parts.next().is_some() {
            return Err(ParseDMSError::new_id());
        };

        match (integer, fraction) {
            // [+-]?\d+[.]?
            (Some(i), Some("") | None) => {
                let int = Self::parse_integer(i)?;
                Self::try_new(int.0, int.1, int.2, int.3, 0.0).ok_or(ParseDMSError::new_oob())
            }
            (Some(i), Some(f)) => {
                // 0 <= fract < 1
                let fract = Self::parse_fraction(f)?;

                if i.eq("+") || i.is_empty() {
                    // +?[.]\d+
                    Ok(Self {
                        sign: Sign::Plus,
                        degree: 0,
                        minute: 0,
                        second: 0,
                        fract,
                    })
                } else if i.eq("-") {
                    // -[.]\d+
                    Ok(Self {
                        sign: Sign::Minus,
                        degree: 0,
                        minute: 0,
                        second: 0,
                        fract,
                    })
                } else {
                    // [+-]?\d+[.]\d+
                    let int = Self::parse_integer(i)?;
                    Self::try_new(int.0, int.1, int.2, int.3, fract).ok_or(ParseDMSError::new_oob())
                }
            }
            (None, None) => Err(ParseDMSError::new_empty()),
            // others
            (None, _) => unreachable!(),
        }
    }
}

impl TryFrom<&f64> for DMS {
    type Error = TryFromDMSError;

    /// Makes a [`DMS`] from DD notation [`f64`].
    ///
    /// `value` is angle which satisfies -180.0 <= and <= 180.0.
    ///
    /// # Errors
    ///
    /// When `value` is not in -180.0 to 180.0.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// # use jgdtrans::dms::{DMS, Sign};
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// assert_eq!(
    ///     DMS::try_from(&36.103774791666666)?,
    ///     DMS::try_new(Sign::Plus, 36, 6, 13, 0.589249999997719).unwrap()
    /// );
    /// assert_eq!(
    ///     DMS::try_from(&140.08785504166664)?,
    ///     DMS::try_new(Sign::Plus, 140, 5, 16, 0.2781499999141488).unwrap()
    /// );
    /// # Ok(())}
    /// ```
    fn try_from(value: &f64) -> Result<Self, TryFromDMSError> {
        if value.is_nan() {
            return Err(TryFromDMSError::new_nan());
        };
        if value.lt(&-180.0) || value.gt(&180.0) {
            return Err(TryFromDMSError::new_oob());
        };

        let mm = 60. * value.fract();
        let ss = 60. * mm.fract();

        let sign = if value.is_sign_positive() {
            Sign::Plus
        } else {
            Sign::Minus
        };

        let degree = value.trunc().abs() as u8;
        let minute = mm.trunc().abs() as u8;
        let second = ss.trunc().abs() as u8;
        let fract = ss.fract().abs();

        Self::try_new(sign, degree, minute, second, fract).ok_or(TryFromDMSError::new_oob())
    }
}

impl DMS {
    fn parse_integer(s: &str) -> Result<(Sign, u8, u8, u8), ParseDMSError> {
        let sign = if s.starts_with('-') {
            Sign::Minus
        } else {
            Sign::Plus
        };

        let i = s
            .parse::<i64>()
            .map_err(|err| match err.kind() {
                IntErrorKind::NegOverflow | IntErrorKind::PosOverflow => ParseDMSError::new_oob(),
                _ => ParseDMSError::new_id(),
            })?
            .unsigned_abs();
        let degree = u8::try_from(i / 10000).map_err(|_| ParseDMSError::new_oob())?;

        let rest = i % 10000;
        let minute = u8::try_from(rest / 100).map_err(|_| ParseDMSError::new_oob())?;
        let second = u8::try_from(rest % 100).map_err(|_| ParseDMSError::new_oob())?;

        Ok((sign, degree, minute, second))
    }

    fn parse_fraction(s: &str) -> Result<f64, ParseDMSError> {
        if s.is_empty() {
            Err(ParseDMSError::new_id())
        } else {
            format!("0.{}", s)
                .parse::<f64>()
                .map_err(|_| ParseDMSError::new_id())
        }
    }
}

impl DMS {
    /// Makes a [`DMS`].
    ///
    /// # Errors
    ///
    /// Returns [`None`] when the input is not in -180°0′0″ to 180°0′0″.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::dms::{DMS, Sign};
    /// # fn run() -> Option<()> {
    /// let dms = DMS::try_new(Sign::Plus, 36, 6, 13, 0.58925)?;
    /// assert_eq!(dms.to_string(), "360613.58925");
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn try_new(sign: Sign, degree: u8, minute: u8, second: u8, fract: f64) -> Option<Self> {
        if fract.is_nan()
            || degree.eq(&180) && (minute.gt(&0) || second.gt(&0) || fract.gt(&0.0))
            || degree.gt(&180)
            || minute.ge(&60)
            || second.ge(&60)
            || fract.lt(&0.0)
            || fract.ge(&1.0)
        {
            return None;
        }

        Some(Self {
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
    /// # use jgdtrans::dms::{DMS, Sign};
    /// # fn run() -> Option<()> {
    /// let dms = DMS::try_new(Sign::Plus, 36, 6, 13, 0.58925)?;
    /// assert_eq!(dms.sign(), &Sign::Plus);
    /// # Some(())}
    /// # fn main() -> () {run();()}
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
    /// # use jgdtrans::dms::{DMS, Sign};
    /// # fn run() -> Option<()> {
    /// let dms = DMS::try_new(Sign::Plus, 36, 6, 13, 0.58925)?;
    /// assert_eq!(dms.degree(), &36);
    /// # Some(())}
    /// # fn main() -> () {run();()}
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
    /// # use jgdtrans::dms::{DMS, Sign};
    /// # fn run() -> Option<()> {
    /// let dms = DMS::try_new(Sign::Plus, 36, 6, 13, 0.58925)?;
    /// assert_eq!(dms.minute(), &6);
    /// # Some(())}
    /// # fn main() -> () {run();()}
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
    /// # use jgdtrans::dms::{DMS, Sign};
    /// # fn run() -> Option<()> {
    /// let dms = DMS::try_new(Sign::Plus, 36, 6, 13, 0.58925)?;
    /// assert_eq!(dms.second(), &13);
    /// # Some(())}
    /// # fn main() -> () {run();()}
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
    /// # use jgdtrans::dms::{DMS, Sign};
    /// # fn run() -> Option<()> {
    /// let dms = DMS::try_new(Sign::Plus, 36, 6, 13, 0.58925)?;
    /// assert_eq!(dms.fract(), &0.58925);
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn fract(&self) -> &f64 {
        &self.fract
    }

    /// Returns a DD notation [`f64`] that `self` converts into.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::dms::{DMS, Sign};
    /// # fn run() -> Option<()> {
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
    /// # Some(())}
    /// # fn main() -> () {run();()}
    /// ```
    pub fn to_degree(&self) -> f64 {
        let res = (self.degree as f64)
            + self.minute as f64 / 60.
            + (self.second as f64 + self.fract) / 3600.0;

        match self.sign {
            Sign::Plus => res,
            Sign::Minus => -res,
        }
    }
}

//
// Error
//

#[derive(Debug)]
pub enum ParseDMSError {
    InvalidDigit,
    OutOfBounds,
    Empty,
}

impl Display for ParseDMSError {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        match self {
            Self::InvalidDigit => write!(f, "invalid digit found in string"),
            Self::OutOfBounds => write!(f, "cannot parse out-of-bounds DMS"),
            Self::Empty => write!(f, "cannot parse DMS from empty string"),
        }
    }
}

impl Error for ParseDMSError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

impl ParseDMSError {
    #[cold]
    fn new_id() -> Self {
        Self::InvalidDigit
    }
    #[cold]
    fn new_oob() -> Self {
        Self::OutOfBounds
    }
    #[cold]
    fn new_empty() -> Self {
        Self::Empty
    }
}

#[derive(Debug)]
pub enum TryFromDMSError {
    NAN,
    OutOfBounds,
}

impl Display for TryFromDMSError {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        match self {
            Self::NAN => write!(f, "number would be NAN"),
            Self::OutOfBounds => write!(f, "number would be out-of-bounds"),
        }
    }
}

impl Error for TryFromDMSError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

impl TryFromDMSError {
    #[cold]
    fn new_nan() -> Self {
        Self::NAN
    }
    #[cold]
    fn new_oob() -> Self {
        Self::OutOfBounds
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
            assert!(DMS::try_new(Sign::Plus, 0, 0, 0, 0.0_f64.next_down()).is_none());

            assert!(DMS::try_new(Sign::Plus, 0, 0, 0, 1.0).is_none());
            assert!(DMS::try_new(Sign::Plus, 0, 0, 60, 0.0).is_none());
            assert!(DMS::try_new(Sign::Plus, 0, 60, 0, 0.0).is_none());

            assert!(DMS::try_new(Sign::Plus, 180, 0, 0, 0.0_f64.next_up()).is_none());
            assert!(DMS::try_new(Sign::Plus, 180, 0, 1, 0.0).is_none());
            assert!(DMS::try_new(Sign::Plus, 180, 1, 0, 0.0).is_none());

            assert!(DMS::try_new(Sign::Minus, 180, 1, 0, 0.0).is_none());
            assert!(DMS::try_new(Sign::Minus, 180, 0, 1, 0.0).is_none());
            assert!(DMS::try_new(Sign::Minus, 180, 0, 0, 0.1).is_none());

            // healthy
            assert!(DMS::try_new(Sign::Plus, 0, 0, 0, 0.0).is_some());
            assert!(DMS::try_new(Sign::Plus, 180, 0, 0, 0.0).is_some());
            assert!(DMS::try_new(Sign::Minus, 180, 0, 0, 0.0).is_some());
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
                assert_eq!(DMS::from_str(a).expect(a), e.expect(a), "{}", a);
            }

            // error
            let cases = [
                "", "-", "a", "-a", ".", "-.", "..", "-..", "..0", "-..0", ".0.", "-.0.", "0..",
                "-0..",
            ];
            for c in cases {
                assert!(DMS::from_str(c).is_err(), "{}", c);
            }
        }

        #[test]
        fn test_to_degree() {
            let dms = DMS::try_new(Sign::Plus, 36, 6, 13, 0.58925).unwrap();
            assert!((36.103774791666666 - dms.to_degree()).abs() < 1e-10);

            let dms = DMS::try_new(Sign::Plus, 140, 5, 16, 0.27815).unwrap();
            assert!((140.08785504166664 - dms.to_degree()).abs() < 1e-10);
        }

        #[test]
        fn test_try_from_dd() {
            let dms = DMS::try_new(Sign::Plus, 36, 6, 13, 0.58925).unwrap();
            let result = DMS::try_from(&36.103774791666666).unwrap();
            assert_eq!(dms.sign, result.sign);
            assert_eq!(dms.degree, result.degree);
            assert_eq!(dms.minute, result.minute);
            assert_eq!(dms.second, result.second);
            assert!((result.fract - dms.fract).abs() < 3e-10);

            let dms = DMS::try_new(Sign::Plus, 140, 5, 16, 0.27815).unwrap();
            let result = DMS::try_from(&140.08785504166664).unwrap();
            assert_eq!(dms.sign, result.sign);
            assert_eq!(dms.degree, result.degree);
            assert_eq!(dms.minute, result.minute);
            assert_eq!(dms.second, result.second);
            assert!((result.fract - dms.fract).abs() < 3e-10);

            // at origin
            let a = DMS::try_from(&0.0).unwrap();
            assert_eq!(a.sign, Sign::Plus);
            assert_eq!(a.degree, 0);
            assert_eq!(a.second, 0);
            assert_eq!(a.minute, 0);
            assert_eq!(a.fract, 0.0);

            let a = DMS::try_from(&-0.0).unwrap();
            assert_eq!(a.sign, Sign::Minus);
            assert_eq!(a.degree, 0);
            assert_eq!(a.second, 0);
            assert_eq!(a.minute, 0);
            assert_eq!(a.fract, 0.0);

            // on bounds
            let a = DMS::try_from(&180.0).unwrap();
            assert_eq!(a.sign, Sign::Plus);
            assert_eq!(a.degree, 180);
            assert_eq!(a.second, 0);
            assert_eq!(a.minute, 0);
            assert_eq!(a.fract, 0.0);

            let a = DMS::try_from(&-180.0_f64).unwrap();
            assert_eq!(a.sign, Sign::Minus);
            assert_eq!(a.degree, 180);
            assert_eq!(a.second, 0);
            assert_eq!(a.minute, 0);
            assert_eq!(a.fract, 0.0);

            // near bounds
            let a = DMS::try_from(&180.0_f64.next_down()).unwrap();
            assert_eq!(a.sign, Sign::Plus);
            assert_eq!(a.degree, 179);
            assert_eq!(a.second, 59);
            assert_eq!(a.minute, 59);
            // assert!((1.0_f64.next_down() - a.fract).abs() < 1e-10);

            let a = DMS::try_from(&(-180.0_f64).next_up()).unwrap();
            assert_eq!(a.sign, Sign::Minus);
            assert_eq!(a.degree, 179);
            assert_eq!(a.second, 59);
            assert_eq!(a.minute, 59);
            // assert!((0.999999999999 - a.fract).abs() < 1e-10);

            // err
            assert!(DMS::try_from(&f64::NAN).is_err());
            assert!(DMS::try_from(&(-180.0_f64).next_down()).is_err());
            assert!(DMS::try_from(&180.0_f64.next_up()).is_err());
        }

        #[test]
        fn test_identity_exact() {
            for deg in 0..180 {
                for min in 0..60 {
                    for sec in 0..60 {
                        for frac in 0..10 {
                            let frac = frac as f64 / 10.0;

                            // plus
                            let degree = DMS::try_new(Sign::Plus, deg, min, sec, frac)
                                .unwrap()
                                .to_degree();
                            let result = DMS::try_from(&degree).unwrap();
                            assert!((result.to_degree() - degree).abs() < 3e-15);

                            // minus
                            let degree = DMS::try_new(Sign::Minus, deg, min, sec, frac)
                                .unwrap()
                                .to_degree();
                            let result = DMS::try_from(&degree).unwrap();
                            assert!((result.to_degree() - degree).abs() < 3e-15);
                        }
                    }
                }
            }
        }
    }
}
