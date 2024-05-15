//! Provides deserializer of par file.
use std::collections::HashMap;
use std::error::Error;
use std::fmt::{Display, Formatter};
use std::num::{ParseFloatError, ParseIntError};
use std::ops::Range;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::mesh::MeshUnit;
use crate::transformer::Parameter;
use crate::Transformer;

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
    format.parse(s)
}

/// Represents format of par-formatted text.
///
/// # Notes
///
/// [`Format::PatchJGD_HV`] is for the same event,
/// e.g. `touhokutaiheiyouoki2011.par` and `touhokutaiheiyouoki2011_h.par`.
/// We note that transformation works fine with such data,
/// and GIAJ does not distribute such file.
///
/// It should fill by zero for the parameters of remaining transformation
/// in areas where it supports only part of the transformation as a result of composition
/// in order to support whole area of each parameter,
/// e.g. altitude of Chubu (<span lang="ja"></span>) on the composition of
/// `touhokutaiheiyouoki2011.par` and `touhokutaiheiyouoki2011_h.par`.
///
/// The composite data should be in the same format as SemiDynaEXE.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Format {
    TKY2JGD,
    PatchJGD,
    #[allow(non_camel_case_types)]
    PatchJGD_H,
    /// The format of composition of PatchJGD and PatchJGD(H) par files.
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
    /// # use std::error::Error;
    /// # use jgdtrans::{Format, mesh::MeshUnit};
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

    pub(crate) fn parse(self, s: &str) -> Result<Transformer, ParseParError> {
        let (parameter, description) = match self {
            Self::TKY2JGD => parse(s, 2, 0..8, Some(9..18), Some(19..28), None),
            Self::PatchJGD => parse(s, 16, 0..8, Some(9..18), Some(19..28), None),
            Self::PatchJGD_H => parse(s, 16, 0..8, None, None, Some(9..18)),
            Self::HyokoRev => parse(s, 16, 0..8, None, None, Some(12..21)),
            Self::PatchJGD_HV | Self::SemiDynaEXE => {
                parse(s, 16, 0..8, Some(9..18), Some(19..28), Some(29..38))
            }
            Self::geonetF3 | Self::ITRF2014 => {
                parse(s, 18, 0..8, Some(12..21), Some(22..31), Some(32..41))
            }
        }?;

        Ok(Transformer {
            format: self,
            parameter,
            description,
        })
    }
}

fn parse(
    text: &str,
    header: usize,
    meshcode: Range<usize>,
    latitude: Option<Range<usize>>,
    longitude: Option<Range<usize>>,
    altitude: Option<Range<usize>>,
) -> Result<(HashMap<u32, Parameter>, Option<String>), ParseParError> {
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

    let mut parameter: HashMap<u32, Parameter> = HashMap::new();
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

//
// Error
//

/// An error which can be returned on parsing par-formatted text.
///
/// This error is used as the error type for the [`from_str`].
#[derive(Debug)]
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
#[derive(Debug)]
pub enum ParseParErrorKind {
    Header,
    ColumnNotFound,
    ParseInt(ParseIntError),
    ParseFloat(ParseFloatError),
}

/// A column that error occurs.
#[derive(Debug)]
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

impl Error for ParseParError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match &self.kind {
            ParseParErrorKind::ParseInt(e) => Some(e),
            ParseParErrorKind::ParseFloat(e) => Some(e),
            _ => None,
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
mod tests {
    use super::*;

    mod tests_error {
        use super::*;
        #[test]
        fn test_empty() {
            let text = "JGD2000-TokyoDatum Ver.2.1.2
MeshCode   dB(sec)   dL(sec)";
            let actual = from_str(&text, Format::TKY2JGD);
            let expected = Transformer {
                format: Format::TKY2JGD,
                parameter: [].into_iter().collect(),
                description: Some(
                    ("JGD2000-TokyoDatum Ver.2.1.2\nMeshCode   dB(sec)   dL(sec)\n").to_string(),
                ),
            };
            assert_eq!(expected, actual.unwrap());

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

    mod tests_tky2jgd {
        use super::*;

        #[test]
        fn test() {
            let text = "\n".repeat(1)
                + "MeshCode   dB(sec)   dL(sec)
00000000   0.00001   0.00002
10000000 -10.00001 -10.00002";
            let actual = from_str(&text, Format::TKY2JGD);
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

            assert_eq!(expected, actual.unwrap());
        }

        #[test]
        fn test_empty() {
            let text = r"JGD2000-TokyoDatum Ver.2.1.2
MeshCode   dB(sec)   dL(sec)
";
            let actual = from_str(&text, Format::TKY2JGD);
            let expected = Transformer {
                format: Format::TKY2JGD,
                parameter: HashMap::new(),
                description: Some(
                    "JGD2000-TokyoDatum Ver.2.1.2\nMeshCode   dB(sec)   dL(sec)\n".to_string(),
                ),
            };

            assert_eq!(expected, actual.unwrap());
        }
    }

    mod tests_patch_jgd {
        use super::*;

        #[test]
        fn test() {
            let text = "\n".repeat(15)
                + "MeshCode   dB(sec)   dL(sec)
00000000   0.00001   0.00002
10000000 -10.00001 -10.00002";
            let actual = from_str(&text, Format::PatchJGD);
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

            assert_eq!(expected, actual.unwrap());
        }
    }

    mod tests_patch_jgd_h {
        use super::*;

        #[test]
        fn test() {
            let text = "\n".repeat(15)
                + "MeshCode   dH(m)     0.00000
00000000   0.00003   0.00000
10000000 -10.00003   0.00000";
            let actual = from_str(&text, Format::PatchJGD_H);
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

            assert_eq!(expected, actual.unwrap());
        }
    }

    mod tests_patch_jgd_hv {
        use super::*;

        #[test]
        fn test() {
            let text = "\n".repeat(15)
                + "MeshCode   dB(sec)   dL(sec)   dH(m)
00000000   0.00001   0.00002   0.00003
10000000 -10.00001 -10.00002 -10.00003";
            let actual = from_str(&text, Format::PatchJGD_HV);
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

            assert_eq!(expected, actual.unwrap());
        }
    }

    mod tests_hyoko_rev {
        use super::*;

        #[test]
        fn test() {
            let text = "\n".repeat(15)
                + "MeshCode      dH(m)     0.00000
00000000      0.00003   0.00000
10000000    -10.00003   0.00000";
            let actual = from_str(&text, Format::HyokoRev);
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

            assert_eq!(expected, actual.unwrap());
        }
    }

    mod tests_semi_dyna_exe {
        use super::*;

        #[test]
        fn test() {
            let text = "\n".repeat(15)
                + "MeshCode dB(sec)  dL(sec) dH(m)
00000000   0.00001   0.00002   0.00003
10000000 -10.00001 -10.00002 -10.00003";
            let actual = from_str(&text, Format::SemiDynaEXE);
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

            assert_eq!(expected, actual.unwrap());
        }
    }

    mod tests_geonet_f3 {
        use super::*;

        #[test]
        fn test() {
            let text = "\n".repeat(17)
                + "END OF HEADER
00000000      0.00001   0.00002   0.00003
10000000    -10.00001 -10.00002 -10.00003";
            let actual = from_str(&text, Format::geonetF3);
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

            assert_eq!(expected, actual.unwrap());
        }
    }

    mod tests_itrf_2014 {
        use super::*;

        #[test]
        fn test() {
            let text = "\n".repeat(17)
                + "END OF HEADER
00000000      0.00001   0.00002   0.00003
10000000    -10.00001 -10.00002 -10.00003";
            let actual = from_str(&text, Format::ITRF2014);
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

            assert_eq!(expected, actual.unwrap());
        }
    }
}
