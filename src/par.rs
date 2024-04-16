//! Provides deserializer of par file.
use std::collections::BTreeMap;
use std::ops::Range;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::error::{ParColumn, ParseParErrorKind};
use crate::mesh::MeshUnit;
use crate::transformer::Parameter;
use crate::{Error, Result, Transformer};

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
/// # use jgdtrans::{Transformer, Format, Point, par};
/// # fn main() -> Result<(), Box<dyn Error>> {
/// // deserialize SemiDynaEXE par file, e.g. SemiDyna2023.par
/// let s = fs::read_to_string("SemiDyna2023.par")?;
/// let tf = par::from_str(&s, Format::SemiDynaEXE)?;
///
/// // prints first 16 lines
/// println!("{:?}", tf.description);
/// // prints Format::SemiDynaEXE
/// println!("{:?}", tf.format);
/// // prints all parameter (be careful, long display)
/// println!("{:?}", tf.parameter);
///
/// // transform coordinate
/// let point: Point = (35.0, 135.0).try_into()?;
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
/// # fn main() -> Result<()> {
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
/// assert_eq!(
///     tf.parameter.get(&12345678),
///     Some(&Parameter {latitude: 0.00001, longitude: 0.00002, altitude: 0.00003})
/// );
/// # Ok(())}
/// ```
pub fn from_str(s: &str, format: Format) -> Result<Transformer> {
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
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// assert_eq!(Format::TKY2JGD.unit(), MeshUnit::One);
    /// assert_eq!(Format::SemiDynaEXE.unit(), MeshUnit::Five);
    /// # Ok(())}
    /// ```
    pub fn unit(&self) -> MeshUnit {
        match self {
            Self::TKY2JGD
            | Self::PatchJGD
            | Self::PatchJGD_H
            | Self::PatchJGD_HV
            | Self::HyokoRev => MeshUnit::One,
            Self::SemiDynaEXE | Self::geonetF3 | Self::ITRF2014 => MeshUnit::Five,
        }
    }

    pub(crate) fn parse(&self, s: &str) -> Result<Transformer> {
        use crate::par::*;
        match self {
            Self::TKY2JGD => parse(
                s,
                2,
                Some(0..8),
                Some(9..18),
                Some(19..28),
                None,
                self.clone(),
            ),
            Self::PatchJGD => parse(
                s,
                16,
                Some(0..8),
                Some(9..18),
                Some(19..28),
                None,
                self.clone(),
            ),
            Self::PatchJGD_H => parse(s, 16, Some(0..8), None, None, Some(9..18), self.clone()),
            Self::HyokoRev => parse(s, 16, Some(0..8), None, None, Some(12..21), self.clone()),
            Self::PatchJGD_HV | Self::SemiDynaEXE => parse(
                s,
                16,
                Some(0..8),
                Some(9..18),
                Some(19..28),
                Some(29..38),
                self.clone(),
            ),
            Self::geonetF3 | Self::ITRF2014 => parse(
                s,
                18,
                Some(0..8),
                Some(12..21),
                Some(22..31),
                Some(32..41),
                self.clone(),
            ),
        }
    }
}

fn parse(
    text: &str,
    header: usize,
    meshcode: Option<Range<usize>>,
    latitude: Option<Range<usize>>,
    longitude: Option<Range<usize>>,
    altitude: Option<Range<usize>>,
    format: Format,
) -> Result<Transformer> {
    let mut iter = text.lines().enumerate();

    let description = iter
        .by_ref()
        .take(header)
        .map(|(_, s)| s)
        .collect::<Vec<_>>()
        .join("\n");

    let mut parameter: BTreeMap<u32, Parameter> = BTreeMap::new();
    for (lineno, line) in iter {
        let meshcode: u32 = match meshcode {
            None => 0,
            Some(ref range) => line
                .get(range.clone())
                .ok_or(Error::new_parse_par(
                    range.start,
                    range.end,
                    lineno + 1,
                    ParseParErrorKind::Missing,
                    ParColumn::Meshcode,
                ))?
                .trim()
                .parse()
                .map_err(|err| {
                    Error::new_parse_par(
                        range.start,
                        range.end,
                        lineno + 1,
                        ParseParErrorKind::ParseInt(err),
                        ParColumn::Meshcode,
                    )
                })?,
        };

        let latitude: f64 = match latitude {
            None => 0.0,
            Some(ref range) => line
                .get(range.clone())
                .ok_or(Error::new_parse_par(
                    range.start,
                    range.end,
                    lineno + 1,
                    ParseParErrorKind::Missing,
                    ParColumn::Latitude,
                ))?
                .trim()
                .parse()
                .map_err(|err| {
                    Error::new_parse_par(
                        range.start,
                        range.end,
                        lineno + 1,
                        ParseParErrorKind::ParseFloat(err),
                        ParColumn::Latitude,
                    )
                })?,
        };

        let longitude: f64 = match longitude {
            None => 0.0,
            Some(ref range) => line
                .get(range.clone())
                .ok_or(Error::new_parse_par(
                    range.start,
                    range.end,
                    lineno + 1,
                    ParseParErrorKind::Missing,
                    ParColumn::Longitude,
                ))?
                .trim()
                .parse()
                .map_err(|err| {
                    Error::new_parse_par(
                        range.start,
                        range.end,
                        lineno + 1,
                        ParseParErrorKind::ParseFloat(err),
                        ParColumn::Longitude,
                    )
                })?,
        };

        let altitude: f64 = match altitude {
            None => 0.0,
            Some(ref range) => line
                .get(range.clone())
                .ok_or(Error::new_parse_par(
                    range.start,
                    range.end,
                    lineno + 1,
                    ParseParErrorKind::Missing,
                    ParColumn::Altitude,
                ))?
                .trim()
                .parse()
                .map_err(|err| {
                    Error::new_parse_par(
                        range.start,
                        range.end,
                        lineno + 1,
                        ParseParErrorKind::ParseFloat(err),
                        ParColumn::Altitude,
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

    Ok(Transformer {
        format,
        parameter,
        description: Some(description),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

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
                description: Some(("\n".repeat(1) + "MeshCode   dB(sec)   dL(sec)").to_string()),
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
                parameter: BTreeMap::new(),
                description: Some(
                    "JGD2000-TokyoDatum Ver.2.1.2\nMeshCode   dB(sec)   dL(sec)".to_string(),
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
                description: Some(("\n".repeat(15) + "MeshCode   dB(sec)   dL(sec)").to_string()),
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
                description: Some(("\n".repeat(15) + "MeshCode   dH(m)     0.00000").to_string()),
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
                    ("\n".repeat(15) + "MeshCode   dB(sec)   dL(sec)   dH(m)").to_string(),
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
                    ("\n".repeat(15) + "MeshCode      dH(m)     0.00000").to_string(),
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
                    ("\n".repeat(15) + "MeshCode dB(sec)  dL(sec) dH(m)").to_string(),
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
                description: Some(("\n".repeat(17) + "END OF HEADER").to_string()),
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
                description: Some(("\n".repeat(17) + "END OF HEADER").to_string()),
            };

            assert_eq!(expected, actual.unwrap());
        }
    }
}