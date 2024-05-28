//! Provides deserializer of par file.
use std::collections::HashMap;
use std::error::Error;
use std::fmt::{Display, Formatter};
use std::hash::{BuildHasher, Hash, RandomState};
use std::num::{ParseFloatError, ParseIntError};
use std::ops::Range;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::mesh::MeshUnit;
use crate::{Parameter, Transformer};

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
/// let tf = from_str(&s, Format::SemiDynaEXE)?;
///
/// assert_eq!(
///     tf.parameter.get(&12345678),
///     Some(&Parameter::new(0.00001, 0.00002, 0.00003))
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
#[inline]
pub fn from_str(s: &str, format: Format) -> Result<Transformer, ParseParError> {
    Parser::new(format).parse(s)
}

/// Represents format of par-formatted text.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Format {
    TKY2JGD,
    PatchJGD,
    #[allow(non_camel_case_types)]
    PatchJGD_H,
    /// The format of composition of PatchJGD and PatchJGD(H) par files.
    ///
    /// [`Format::PatchJGD_HV`] is for the same event,
    /// e.g. `touhokutaiheiyouoki2011.par` and `touhokutaiheiyouoki2011_h.par`.
    /// We note that transformation works fine with such data,
    /// and GIAJ does not distribute such file.
    ///
    /// It should fill by zero for the parameters of remaining transformation
    /// in areas where it supports only part of the transformation as a result of composition
    /// in order to support whole area of each parameter,
    /// e.g. altitude of Chubu (<span lang="ja">中部</span>) on the composition of
    /// `touhokutaiheiyouoki2011.par` and `touhokutaiheiyouoki2011_h.par`.
    ///
    /// The composite data should be in the same format as SemiDynaEXE.
    #[allow(non_camel_case_types)]
    PatchJGD_HV,
    HyokoRev,
    #[allow(non_camel_case_types)]
    SemiDynaEXE,
    #[allow(non_camel_case_types)]
    geonetF3,
    ITRF2014,
}

impl Format {
    /// Returns the unit.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::Format;
    /// # use jgdtrans::mesh::MeshUnit;
    /// #
    /// assert_eq!(Format::TKY2JGD.mesh_unit(), MeshUnit::One);
    /// assert_eq!(Format::SemiDynaEXE.mesh_unit(), MeshUnit::Five);
    /// ```
    #[inline]
    pub const fn mesh_unit(&self) -> MeshUnit {
        match self {
            Self::TKY2JGD
            | Self::PatchJGD
            | Self::PatchJGD_H
            | Self::PatchJGD_HV
            | Self::HyokoRev => MeshUnit::One,
            Self::SemiDynaEXE | Self::geonetF3 | Self::ITRF2014 => MeshUnit::Five,
        }
    }
}

#[allow(clippy::type_complexity)]
fn parse<S>(
    text: &str,
    header: usize,
    meshcode: Range<usize>,
    latitude: Option<Range<usize>>,
    longitude: Option<Range<usize>>,
    altitude: Option<Range<usize>>,
    hash_builder: S,
) -> Result<(HashMap<u32, Parameter, S>, Option<String>), ParseParError>
where
    S: BuildHasher,
{
    if text.lines().count().lt(&header) {
        return Err(ParseParError::new(
            0,
            text.lines().by_ref().last().map_or(0, str::len),
            text.lines().count(),
            ParseParErrorKind::Header,
            Column::Meshcode,
        ));
    }

    let mut lines = text.lines().enumerate();

    let description = lines
        .by_ref()
        .take(header)
        .map(|(_, s)| s)
        .collect::<Vec<_>>()
        .join("\n")
        + "\n";

    let mut parameter = HashMap::with_hasher(hash_builder);
    for (lineno, line) in lines {
        let meshcode: u32 = line
            .get(meshcode.clone())
            .ok_or(ParseParError::new(
                meshcode.start,
                meshcode.end,
                lineno + 1,
                ParseParErrorKind::ColumnNotFound,
                Column::Meshcode,
            ))?
            .trim()
            .parse()
            .map_err(|e| {
                ParseParError::new(
                    meshcode.start,
                    meshcode.end,
                    lineno + 1,
                    ParseParErrorKind::ParseInt(e),
                    Column::Meshcode,
                )
            })?;

        let latitude: f64 = match latitude {
            None => 0.0,
            Some(ref range) => line
                .get(range.clone())
                .ok_or(ParseParError::new(
                    range.start,
                    range.end,
                    lineno + 1,
                    ParseParErrorKind::ColumnNotFound,
                    Column::Latitude,
                ))?
                .trim()
                .parse()
                .map_err(|e| {
                    ParseParError::new(
                        range.start,
                        range.end,
                        lineno + 1,
                        ParseParErrorKind::ParseFloat(e),
                        Column::Latitude,
                    )
                })?,
        };

        let longitude: f64 = match longitude {
            None => 0.0,
            Some(ref range) => line
                .get(range.clone())
                .ok_or(ParseParError::new(
                    range.start,
                    range.end,
                    lineno + 1,
                    ParseParErrorKind::ColumnNotFound,
                    Column::Longitude,
                ))?
                .trim()
                .parse()
                .map_err(|e| {
                    ParseParError::new(
                        range.start,
                        range.end,
                        lineno + 1,
                        ParseParErrorKind::ParseFloat(e),
                        Column::Longitude,
                    )
                })?,
        };

        let altitude: f64 = match altitude {
            None => 0.0,
            Some(ref range) => line
                .get(range.clone())
                .ok_or(ParseParError::new(
                    range.start,
                    range.end,
                    lineno + 1,
                    ParseParErrorKind::ColumnNotFound,
                    Column::Altitude,
                ))?
                .trim()
                .parse()
                .map_err(|e| {
                    ParseParError::new(
                        range.start,
                        range.end,
                        lineno + 1,
                        ParseParErrorKind::ParseFloat(e),
                        Column::Altitude,
                    )
                })?,
        };

        parameter.insert(
            meshcode,
            Parameter {
                latitude,
                longitude,
                altitude,
            },
        );
    }

    parameter.shrink_to_fit();

    Ok((parameter, Some(description)))
}

/// Parser of par-formatted [`&str`].
///
/// # Example
///
/// ```
/// # use std::error::Error;
/// # use jgdtrans::*;
/// # use jgdtrans::par::Parser;
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
/// let tf = Parser::new(Format::SemiDynaEXE).parse(&s)?;
///
/// assert_eq!(
///     tf.parameter.get(&12345678),
///     Some(&Parameter::new(0.00001, 0.00002, 0.00003))
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
#[derive(Debug)]
pub struct Parser<S = RandomState> {
    format: Format,
    hash_builder: S,
}

impl Parser<RandomState> {
    /// Makes a parser.
    #[inline]
    pub fn new(format: Format) -> Self {
        Self::with_hasher(format, RandomState::new())
    }
}

impl<#[cfg(not(feature = "serde"))] S, #[cfg(feature = "serde")] S: Default> Parser<S> {
    /// Makes a parser reuslting [`Transformer`] which uses the given hash builder to hash meshcode.
    ///
    /// This may improve performance of transformation.
    /// See [`HashMap::with_hasher`], for detail.
    #[inline]
    pub const fn with_hasher(format: Format, hash_builder: S) -> Self {
        Self {
            format,
            hash_builder,
        }
    }
}

impl<#[cfg(not(feature = "serde"))] S, #[cfg(feature = "serde")] S: Default> Parser<S>
where
    S: BuildHasher,
{
    /// Deserialize par-formatted [`&str`] into a [`Transformer`].
    #[inline]
    pub fn parse(self, s: &str) -> Result<Transformer<S>, ParseParError> {
        let (parameter, description) = match self.format {
            Format::TKY2JGD => self::parse(
                s,
                2,
                0..8,
                Some(9..18),
                Some(19..28),
                None,
                self.hash_builder,
            ),
            Format::PatchJGD => self::parse(
                s,
                16,
                0..8,
                Some(9..18),
                Some(19..28),
                None,
                self.hash_builder,
            ),
            Format::PatchJGD_H => {
                self::parse(s, 16, 0..8, None, None, Some(9..18), self.hash_builder)
            }
            Format::HyokoRev => {
                self::parse(s, 16, 0..8, None, None, Some(12..21), self.hash_builder)
            }
            Format::PatchJGD_HV | Format::SemiDynaEXE => self::parse(
                s,
                16,
                0..8,
                Some(9..18),
                Some(19..28),
                Some(29..38),
                self.hash_builder,
            ),
            Format::geonetF3 | Format::ITRF2014 => self::parse(
                s,
                18,
                0..8,
                Some(12..21),
                Some(22..31),
                Some(32..41),
                self.hash_builder,
            ),
        }?;

        Ok(Transformer {
            format: self.format.clone(),
            parameter,
            description,
        })
    }

    /// Deserialize par-formatted [`&str`] into a [`Transformer`] with `description`.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jgdtrans::*;
    /// # use jgdtrans::par::Parser;
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
    /// let tf = Parser::new(Format::SemiDynaEXE)
    ///     .parse_with_description(&s, "My parameter".to_string())?;
    ///
    /// assert_eq!(
    ///     tf.description,
    ///     Some("My parameter".to_string())
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[inline]
    pub fn parse_with_description(
        self,
        s: &str,
        description: String,
    ) -> Result<Transformer<S>, ParseParError> {
        let tf = self.parse(s)?;
        Ok(Transformer {
            format: tf.format,
            parameter: tf.parameter,
            description: Some(description),
        })
    }
}

impl<#[cfg(not(feature = "serde"))] S, #[cfg(feature = "serde")] S: Default> Clone for Parser<S>
where
    S: Clone,
{
    #[inline]
    fn clone(&self) -> Self {
        Self {
            format: self.format.clone(),
            hash_builder: self.hash_builder.clone(),
        }
    }

    #[inline]
    fn clone_from(&mut self, source: &Self) {
        self.format.clone_from(&source.format);
        self.hash_builder.clone_from(&source.hash_builder)
    }
}

//
// Error
//

/// An error which can be returned on parsing par-formatted text.
///
/// This error is used as the error type for the [`from_str`].
#[derive(Debug, PartialEq, Eq)]
pub struct ParseParError {
    /// Error kind
    kind: ParseParErrorKind,
    /// Error Column
    pub column: Column,
    /// Lineno of the data
    pub lineno: usize,
    /// Start colum no. of the data
    pub start: usize,
    /// End colum no. of the data
    pub end: usize,
}

/// An error kind of [`ParseParError`].
#[derive(Debug, PartialEq, Eq)]
pub enum ParseParErrorKind {
    Header,
    ColumnNotFound,
    ParseInt(ParseIntError),
    ParseFloat(ParseFloatError),
}

/// A column that error occurs.
#[derive(Debug, PartialEq, Eq)]
pub enum Column {
    Meshcode,
    Latitude,
    Longitude,
    Altitude,
    Other,
}

impl ParseParError {
    #[cold]
    const fn new(
        start: usize,
        end: usize,
        lineno: usize,
        kind: ParseParErrorKind,
        column: Column,
    ) -> Self {
        Self {
            kind,
            column,
            lineno,
            start,
            end,
        }
    }

    /// Returns the detailed cause.
    pub const fn kind(&self) -> &ParseParErrorKind {
        &self.kind
    }
}

impl Error for ParseParError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match &self.kind {
            ParseParErrorKind::ParseInt(e) => Some(e),
            ParseParErrorKind::ParseFloat(e) => Some(e),
            _ => None,
        }
    }
}

impl Display for ParseParError {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        match self.kind {
            ParseParErrorKind::Header => write!(
                f,
                "parse error: header at l{}:{}:{}",
                self.lineno, self.start, self.end
            ),
            _ => write!(
                f,
                "parse error: {} at l{}:{}:{}",
                self.column, self.lineno, self.start, self.end
            ),
        }
    }
}

impl Display for Column {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        match self {
            Self::Meshcode => write!(f, "meshcode"),
            Self::Latitude => write!(f, "latitude"),
            Self::Longitude => write!(f, "longitude"),
            Self::Altitude => write!(f, "altitude"),
            Self::Other => write!(f, "other"),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    macro_rules! transformer_eq {
        ($expected:ident, $actual:expr) => {
            assert_eq!($expected.format, $actual.format);
            assert_eq!($expected.parameter, $actual.parameter);
            assert_eq!($expected.description, $actual.description);
        };
    }

    mod tests_error {
        use super::*;

        #[test]
        fn test_empty() {
            let text = "JGD2000-TokyoDatum Ver.2.1.2
MeshCode   dB(sec)   dL(sec)";
            let actual = from_str(&text, Format::TKY2JGD).unwrap();
            let expected = Transformer {
                format: Format::TKY2JGD,
                parameter: [].into_iter().collect(),
                description: Some(
                    ("JGD2000-TokyoDatum Ver.2.1.2\nMeshCode   dB(sec)   dL(sec)\n").to_string(),
                ),
            };
            transformer_eq!(expected, actual);

            let text = "JGD2000-TokyoDatum Ver.2.1.2";
            let actual = from_str(&text, Format::TKY2JGD);
            assert!(actual.is_err());

            let text = "";
            let actual = from_str(&text, Format::TKY2JGD);
            assert!(actual.is_err());
        }

        #[test]
        fn test_meshcode() {
            let text = "\n".repeat(15)
                + "MeshCode dB(sec)  dL(sec) dH(m)
000x0000   0.00001   0.00002   0.00003
10000000 -10.00001 -10.00002 -10.00003";
            let actual = from_str(&text, Format::SemiDynaEXE).unwrap_err();

            assert_eq!(actual.start, 0);
            assert_eq!(actual.end, 8);
            assert_eq!(actual.lineno, 17);
            assert!(matches!(actual.column, Column::Meshcode));
        }

        #[test]
        fn test_latitude() {
            let text = "\n".repeat(15)
                + "MeshCode dB(sec)  dL(sec) dH(m)
00000000   0.0000x   0.00002   0.00003
10000000 -10.00001 -10.00002 -10.00003";
            let actual = from_str(&text, Format::SemiDynaEXE).unwrap_err();

            assert_eq!(actual.start, 9);
            assert_eq!(actual.end, 18);
            assert_eq!(actual.lineno, 17);
            assert!(matches!(actual.column, Column::Latitude));
        }

        #[test]
        fn test_longitude() {
            let text = "\n".repeat(15)
                + "MeshCode dB(sec)  dL(sec) dH(m)
00000000   0.00001   0.0000x   0.00003
10000000 -10.00001 -10.00002 -10.00003";
            let actual = from_str(&text, Format::SemiDynaEXE).unwrap_err();

            assert_eq!(actual.start, 19);
            assert_eq!(actual.end, 28);
            assert_eq!(actual.lineno, 17);
            assert!(matches!(actual.column, Column::Longitude));
        }

        #[test]
        fn test_altitude() {
            let text = "\n".repeat(15)
                + "MeshCode dB(sec)  dL(sec) dH(m)
00000000   0.00001   0.00002   0.0000x
10000000 -10.00001 -10.00002 -10.00003";
            let actual = from_str(&text, Format::SemiDynaEXE).unwrap_err();

            assert_eq!(actual.start, 29);
            assert_eq!(actual.end, 38);
            assert_eq!(actual.lineno, 17);
            assert!(matches!(actual.column, Column::Altitude));
        }
    }

    #[allow(non_snake_case)]
    mod tests_TKY2JGD {
        use super::*;

        #[test]
        fn test() {
            let text = "\n".repeat(1)
                + "MeshCode   dB(sec)   dL(sec)
00000000   0.00001   0.00002
10000000 -10.00001 -10.00002";
            let actual = from_str(&text, Format::TKY2JGD).unwrap();
            let expected = Transformer {
                format: Format::TKY2JGD,
                parameter: [
                    (
                        0,
                        Parameter {
                            latitude: 0.00001,
                            longitude: 0.00002,
                            altitude: 0.0,
                        },
                    ),
                    (
                        10000000,
                        Parameter {
                            latitude: -10.00001,
                            longitude: -10.00002,
                            altitude: 0.0,
                        },
                    ),
                ]
                .into_iter()
                .collect(),
                description: Some(("\n".repeat(1) + "MeshCode   dB(sec)   dL(sec)\n").to_string()),
            };

            transformer_eq!(expected, actual);
        }

        #[test]
        fn test_empty() {
            let text = r"JGD2000-TokyoDatum Ver.2.1.2
MeshCode   dB(sec)   dL(sec)
";
            let actual = from_str(&text, Format::TKY2JGD).unwrap();
            let expected = Transformer {
                format: Format::TKY2JGD,
                parameter: HashMap::new(),
                description: Some(
                    "JGD2000-TokyoDatum Ver.2.1.2\nMeshCode   dB(sec)   dL(sec)\n".to_string(),
                ),
            };

            transformer_eq!(expected, actual);
        }
    }

    #[allow(non_snake_case)]
    mod tests_PatchJGD {
        use super::*;

        #[test]
        fn test() {
            let text = "\n".repeat(15)
                + "MeshCode   dB(sec)   dL(sec)
00000000   0.00001   0.00002
10000000 -10.00001 -10.00002";
            let actual = from_str(&text, Format::PatchJGD).unwrap();
            let expected = Transformer {
                format: Format::PatchJGD,
                parameter: [
                    (
                        0,
                        Parameter {
                            latitude: 0.00001,
                            longitude: 0.00002,
                            altitude: 0.0,
                        },
                    ),
                    (
                        10000000,
                        Parameter {
                            latitude: -10.00001,
                            longitude: -10.00002,
                            altitude: 0.0,
                        },
                    ),
                ]
                .into_iter()
                .collect(),
                description: Some(("\n".repeat(15) + "MeshCode   dB(sec)   dL(sec)\n").to_string()),
            };

            transformer_eq!(expected, actual);
        }
    }

    #[allow(non_snake_case)]
    mod tests_PatchJGD_H {
        use super::*;

        #[test]
        fn test() {
            let text = "\n".repeat(15)
                + "MeshCode   dH(m)     0.00000
00000000   0.00003   0.00000
10000000 -10.00003   0.00000";
            let actual = from_str(&text, Format::PatchJGD_H).unwrap();
            let expected = Transformer {
                format: Format::PatchJGD_H,
                parameter: [
                    (
                        0,
                        Parameter {
                            latitude: 0.0,
                            longitude: 0.0,
                            altitude: 0.00003,
                        },
                    ),
                    (
                        10000000,
                        Parameter {
                            latitude: 0.0,
                            longitude: 0.0,
                            altitude: -10.00003,
                        },
                    ),
                ]
                .into_iter()
                .collect(),
                description: Some(("\n".repeat(15) + "MeshCode   dH(m)     0.00000\n").to_string()),
            };

            transformer_eq!(expected, actual);
        }
    }

    #[allow(non_snake_case)]
    mod tests_PatchJGD_HV {
        use super::*;

        #[test]
        fn test() {
            let text = "\n".repeat(15)
                + "MeshCode   dB(sec)   dL(sec)   dH(m)
00000000   0.00001   0.00002   0.00003
10000000 -10.00001 -10.00002 -10.00003";
            let actual = from_str(&text, Format::PatchJGD_HV).unwrap();
            let expected = Transformer {
                format: Format::PatchJGD_HV,
                parameter: [
                    (
                        0,
                        Parameter {
                            latitude: 0.00001,
                            longitude: 0.00002,
                            altitude: 0.00003,
                        },
                    ),
                    (
                        10000000,
                        Parameter {
                            latitude: -10.00001,
                            longitude: -10.00002,
                            altitude: -10.00003,
                        },
                    ),
                ]
                .into_iter()
                .collect(),
                description: Some(
                    ("\n".repeat(15) + "MeshCode   dB(sec)   dL(sec)   dH(m)\n").to_string(),
                ),
            };

            transformer_eq!(expected, actual);
        }
    }

    #[allow(non_snake_case)]
    mod tests_HyokoRev {
        use super::*;

        #[test]
        fn test() {
            let text = "\n".repeat(15)
                + "MeshCode      dH(m)     0.00000
00000000      0.00003   0.00000
10000000    -10.00003   0.00000";
            let actual = from_str(&text, Format::HyokoRev).unwrap();
            let expected = Transformer {
                format: Format::HyokoRev,
                parameter: [
                    (
                        0,
                        Parameter {
                            latitude: 0.0,
                            longitude: 0.0,
                            altitude: 0.00003,
                        },
                    ),
                    (
                        10000000,
                        Parameter {
                            latitude: 0.0,
                            longitude: 0.0,
                            altitude: -10.00003,
                        },
                    ),
                ]
                .into_iter()
                .collect(),
                description: Some(
                    ("\n".repeat(15) + "MeshCode      dH(m)     0.00000\n").to_string(),
                ),
            };

            transformer_eq!(expected, actual);
        }
    }

    #[allow(non_snake_case)]
    mod tests_SemiDynaEXE {
        use super::*;

        #[test]
        fn test() {
            let text = "\n".repeat(15)
                + "MeshCode dB(sec)  dL(sec) dH(m)
00000000   0.00001   0.00002   0.00003
10000000 -10.00001 -10.00002 -10.00003";
            let actual = from_str(&text, Format::SemiDynaEXE).unwrap();
            let expected = Transformer {
                format: Format::SemiDynaEXE,
                parameter: [
                    (
                        0,
                        Parameter {
                            latitude: 0.00001,
                            longitude: 0.00002,
                            altitude: 0.00003,
                        },
                    ),
                    (
                        10000000,
                        Parameter {
                            latitude: -10.00001,
                            longitude: -10.00002,
                            altitude: -10.00003,
                        },
                    ),
                ]
                .into_iter()
                .collect(),
                description: Some(
                    ("\n".repeat(15) + "MeshCode dB(sec)  dL(sec) dH(m)\n").to_string(),
                ),
            };

            transformer_eq!(expected, actual);
        }
    }

    #[allow(non_snake_case)]
    mod tests_geonetF3 {
        use super::*;

        #[test]
        fn test() {
            let text = "\n".repeat(17)
                + "END OF HEADER
00000000      0.00001   0.00002   0.00003
10000000    -10.00001 -10.00002 -10.00003";
            let actual = from_str(&text, Format::geonetF3).unwrap();
            let expected = Transformer {
                format: Format::geonetF3,
                parameter: [
                    (
                        0,
                        Parameter {
                            latitude: 0.00001,
                            longitude: 0.00002,
                            altitude: 0.00003,
                        },
                    ),
                    (
                        10000000,
                        Parameter {
                            latitude: -10.00001,
                            longitude: -10.00002,
                            altitude: -10.00003,
                        },
                    ),
                ]
                .into_iter()
                .collect(),
                description: Some(("\n".repeat(17) + "END OF HEADER\n").to_string()),
            };

            transformer_eq!(expected, actual);
        }
    }

    #[allow(non_snake_case)]
    mod tests_ITRF2014 {
        use super::*;

        #[test]
        fn test() {
            let text = "\n".repeat(17)
                + "END OF HEADER
00000000      0.00001   0.00002   0.00003
10000000    -10.00001 -10.00002 -10.00003";
            let actual = from_str(&text, Format::ITRF2014).unwrap();
            let expected = Transformer {
                format: Format::ITRF2014,
                parameter: [
                    (
                        0,
                        Parameter {
                            latitude: 0.00001,
                            longitude: 0.00002,
                            altitude: 0.00003,
                        },
                    ),
                    (
                        10000000,
                        Parameter {
                            latitude: -10.00001,
                            longitude: -10.00002,
                            altitude: -10.00003,
                        },
                    ),
                ]
                .into_iter()
                .collect(),
                description: Some(("\n".repeat(17) + "END OF HEADER\n").to_string()),
            };

            transformer_eq!(expected, actual);
        }
    }
}
