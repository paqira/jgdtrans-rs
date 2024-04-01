use std::collections::BTreeMap;
use std::ops::Range;

use crate::error::{ParColumn, ParseParErrorKind};
use crate::mesh::MeshUnit;
use crate::transformer::Parameter;
use crate::{Error, Result, Transformer};

fn parser(
    text: &str,
    header: usize,
    meshcode: Option<Range<usize>>,
    latitude: Option<Range<usize>>,
    longitude: Option<Range<usize>>,
    altitude: Option<Range<usize>>,
    unit: MeshUnit,
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
        unit,
        parameter,
        description: Some(description),
    })
}

/// Provides deserializer of _TKY2JGD_-formatted [`&str`] into a [`Transformer`].
#[allow(non_snake_case)]
#[allow(unused)]
pub mod TKY2JGD {
    use super::*;

    /// The mesh unit of _TKY2JGD_, [`MeshUnit::One`].
    ///
    /// ```
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::parser::TKY2JGD;
    /// assert_eq!(TKY2JGD::UNIT, MeshUnit::One);
    /// ```
    pub const UNIT: MeshUnit = MeshUnit::One;

    /// Deserialize _TKY2JGD_-formatted [`&str`] into a [`Transformer`].
    ///
    /// ```no_run
    /// # use std::fs;
    /// # use std::error::Error;
    /// # use jgdtrans::{Format, TKY2JGD, Point};
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// // deserialize TKY2JGD par file
    /// let s = fs::read_to_string("TKY2JGD.par")?;
    /// let tf = TKY2JGD::from_str(&s)?;
    ///
    /// // prints first 2 lines
    /// println!("{:?}", tf.description);
    /// // prints MeshUnit::One (namely, the mesh unit is 1)
    /// println!("{:?}", tf.unit);
    /// // prints all parameter (be careful, long display)
    /// println!("{:?}", tf.parameter);
    ///
    /// // transform coordinate
    /// let point: Point = (35.0, 135.0).try_into()?;
    /// let result = tf.forward(&point);
    /// # Ok(())}
    /// ```
    ///
    /// This fill by 0 for the altitude parameter.
    ///
    /// # Errors
    ///
    /// If invalid data found.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::parser::TKY2JGD;
    /// # use jgdtrans::transformer::Parameter;
    /// # fn main() -> Result<()> {
    /// let s = r"<1 line>
    /// MeshCode   dB(sec)   dL(sec)
    /// 12345678   0.00001   0.00002";
    /// let tf = TKY2JGD::from_str(&s)?;
    /// assert_eq!(
    ///     tf.parameter.get(&12345678),
    ///     Some(&Parameter {latitude: 0.00001, longitude: 0.00002, altitude: 0.0})
    /// );
    /// # Ok(())}
    /// ```
    ///
    pub fn from_str(s: &str) -> Result<Transformer> {
        parser(
            s,
            2,
            Some(0..8),
            Some(9..18),
            Some(19..28),
            None,
            MeshUnit::One,
        )
    }
}

/// Provides deserializer of _PatchJGD_-formatted [`&str`] into a [`Transformer`].
#[allow(non_snake_case)]
#[allow(unused)]
pub mod PatchJGD {
    use super::*;

    /// The mesh unit of _PatchJGD_, [`MeshUnit::One`].
    ///
    /// ```
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::parser::PatchJGD;
    /// assert_eq!(PatchJGD::UNIT, MeshUnit::One);
    /// ```
    pub const UNIT: MeshUnit = MeshUnit::One;

    /// Deserialize _PatchJGD_-formatted [`&str`] into a [`Transformer`].
    ///
    /// ```no_run
    /// # use std::fs;
    /// # use std::error::Error;
    /// # use jgdtrans::{Format, PatchJGD, Point};
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// // deserialize PatchJGD par file, e.g. touhokutaiheiyouoki2011.par
    /// let s = fs::read_to_string("touhokutaiheiyouoki2011.par")?;
    /// let tf = PatchJGD::from_str(&s)?;
    ///
    /// // prints first 16 lines
    /// println!("{:?}", tf.description);
    /// // prints MeshUnit::One (namely, the mesh unit is 1)
    /// println!("{:?}", tf.unit);
    /// // prints all parameter (be careful, long display)
    /// println!("{:?}", tf.parameter);
    ///
    /// // transform coordinate
    /// let point: Point = (35.0, 135.0).try_into()?;
    /// let result = tf.forward(&point);
    /// # Ok(())}
    /// ```
    ///
    /// This fill by 0 for the altitude parameter.
    ///
    /// # Errors
    ///
    /// If invalid data found.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::parser::PatchJGD;
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
    /// MeshCode   dB(sec)   dL(sec)
    /// 12345678   0.00001   0.00002";
    /// let tf = PatchJGD::from_str(&s)?;
    /// assert_eq!(
    ///     tf.parameter.get(&12345678),
    ///     Some(&Parameter {latitude: 0.00001, longitude: 0.00002, altitude: 0.0})
    /// );
    /// # Ok(())}
    /// ```
    pub fn from_str(s: &str) -> Result<Transformer> {
        parser(
            s,
            16,
            Some(0..8),
            Some(9..18),
            Some(19..28),
            None,
            MeshUnit::One,
        )
    }
}

/// Provides deserializer of _PatchJGD(H)_-formatted [`&str`] into a [`Transformer`].
#[allow(non_snake_case)]
#[allow(unused)]
pub mod PatchJGD_H {
    use super::*;

    /// The mesh unit of _PatchJGD(H)_, [`MeshUnit::One`].
    ///
    /// ```
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::parser::PatchJGD_H;
    /// assert_eq!(PatchJGD_H::UNIT, MeshUnit::One);
    /// ```
    pub const UNIT: MeshUnit = MeshUnit::One;

    /// Deserialize _PatchJGD(H)_-formatted [`&str`] into a [`Transformer`].
    ///
    /// ```no_run
    /// # use std::fs;
    /// # use std::error::Error;
    /// # use jgdtrans::{Format, PatchJGD_H, Point};
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// // deserialize PatchJGD(H) par file, e.g. touhokutaiheiyouoki2011_h.par
    /// let s = fs::read_to_string("touhokutaiheiyouoki2011_h.par")?;
    /// let tf = PatchJGD_H::from_str(&s)?;
    ///
    /// // prints first 16 lines
    /// println!("{:?}", tf.description);
    /// // prints MeshUnit::One (namely, the mesh unit is 1)
    /// println!("{:?}", tf.unit);
    /// // prints all parameter (be careful, long display)
    /// println!("{:?}", tf.parameter);
    ///
    /// // transform coordinate
    /// let point: Point = (35.0, 135.0).try_into()?;
    /// let result = tf.forward(&point);
    /// # Ok(())}
    /// ```
    ///
    /// This fill by 0 for the latitude and the longitude parameter.
    ///
    /// # Errors
    ///
    /// If invalid data found.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// # use jgdtrans::parser::PatchJGD_H;
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
    /// MeshCode   dH(m)     0.00000
    /// 12345678   0.00001   0.00000";
    ///
    /// let tf = PatchJGD_H::from_str(&s)?;
    /// assert_eq!(
    ///     tf.parameter.get(&12345678),
    ///     Some(&Parameter {latitude: 0.0, longitude: 0.0, altitude: 0.00001})
    /// );
    /// # Ok(())}
    /// ```
    pub fn from_str(s: &str) -> Result<Transformer> {
        parser(s, 16, Some(0..8), None, None, Some(9..18), MeshUnit::One)
    }
}

/// Provides deserializer of _PatchJGD(HV)_-formatted [`&str`] into a [`Transformer`].
///
/// This provides deserializer of a composition of PatchJGD and PatchJGD(H) par files
/// for the same event, e.g. `touhokutaiheiyouoki2011.par` and `touhokutaiheiyouoki2011_h.par`.
/// We note that transformation works fine with such data,
/// and GIAJ does not distribute such file.
///
/// It should fill by zero for the parameters of remaining transformation
/// in areas where it supports only part of the transformation as a result of composition
/// in order to support whole area of each parameter,
/// e.g. altitude of Chubu (中部地方) on the composition of
/// `touhokutaiheiyouoki2011.par` and `touhokutaiheiyouoki2011_h.par`.
///
/// The composite data should be in the same format as SemiDynaEXE.
#[allow(non_snake_case)]
#[allow(unused)]
pub mod PatchJGD_HV {
    use super::*;

    /// The mesh unit of _PatchJGD(HV)_, [`MeshUnit::One`].
    ///
    /// ```
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::parser::PatchJGD_HV;
    /// assert_eq!(PatchJGD_HV::UNIT, MeshUnit::One);
    /// ```
    pub const UNIT: MeshUnit = MeshUnit::One;

    /// Deserialize _PatchJGD(HV)_-formatted [`&str`] into a [`Transformer`].
    ///
    /// See [`PatchJGD_HV`](self) for detail information.
    ///
    /// ```no_run
    /// # use std::fs;
    /// # use std::error::Error;
    /// # use jgdtrans::{Format, PatchJGD_HV, Point};
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// // deserialize PatchJGD(HV) par file
    /// let s = fs::read_to_string("touhokutaiheiyouoki2011_hv.par")?;
    /// let tf = PatchJGD_HV::from_str(&s)?;
    ///
    /// // prints first 16 lines
    /// println!("{:?}", tf.description);
    /// // prints MeshUnit::One (namely, the mesh unit is 1)
    /// println!("{:?}", tf.unit);
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
    /// # use jgdtrans::parser::PatchJGD_HV;
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
    /// MeshCode   dB(sec)   dL(sec)   dH(m)
    /// 12345678   0.00001   0.00002   0.00003";
    /// let tf = PatchJGD_HV::from_str(&s)?;
    /// assert_eq!(
    ///     tf.parameter.get(&12345678),
    ///     Some(&Parameter {latitude: 0.00001, longitude: 0.00002, altitude: 0.00003})
    /// );
    /// # Ok(())}
    /// ```
    pub fn from_str(s: &str) -> Result<Transformer> {
        parser(
            s,
            16,
            Some(0..8),
            Some(9..18),
            Some(19..28),
            Some(29..38),
            MeshUnit::One,
        )
    }
}

/// Provides deserializer of _HyokoRev_-formatted [`&str`] into a [`Transformer`].
#[allow(non_snake_case)]
#[allow(unused)]
pub mod HyokoRev {
    use super::*;

    /// The mesh unit of _HyokoRev_, [`MeshUnit::One`].
    ///
    /// ```
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::parser::HyokoRev;
    /// assert_eq!(HyokoRev::UNIT, MeshUnit::One);
    /// ```
    pub const UNIT: MeshUnit = MeshUnit::One;

    /// Deserialize _HyokoRev_-formatted [`&str`] into a [`Transformer`].
    ///
    /// This fill by 0 for the latitude and the longitude parameter.
    ///
    /// ```no_run
    /// # use std::fs;
    /// # use std::error::Error;
    /// # use jgdtrans::{Format, HyokoRev, Point};
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// // deserialize HyokoRev par file, e.g. hyokorev2014_geoid2011_h.par
    /// let s = fs::read_to_string("hyokorev2014_geoid2011_h.par")?;
    /// let tf = HyokoRev::from_str(&s)?;
    ///
    /// // prints first 16 lines
    /// println!("{:?}", tf.description);
    /// // prints MeshUnit::One (namely, the mesh unit is 1)
    /// println!("{:?}", tf.unit);
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
    /// # use jgdtrans::parser::HyokoRev;
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
    /// MeshCode      dH(m)     0.00000
    /// 12345678      0.00001   0.00000";
    /// let tf = HyokoRev::from_str(&s)?;
    /// assert_eq!(
    ///     tf.parameter.get(&12345678),
    ///     Some(&Parameter {latitude: 0.0, longitude: 0.0, altitude: 0.00001})
    /// );
    /// # Ok(())}
    /// ```
    pub fn from_str(s: &str) -> Result<Transformer> {
        parser(s, 16, Some(0..8), None, None, Some(12..21), MeshUnit::One)
    }
}

/// Provides deserializer of _SemiDynaEXE_-formatted [`&str`] into a [`Transformer`].
#[allow(non_snake_case)]
#[allow(unused)]
pub mod SemiDynaEXE {
    use super::*;

    /// The mesh unit of _SemiDynaEXE_, [`MeshUnit::Five`].
    ///
    /// ```
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::parser::SemiDynaEXE;
    /// assert_eq!(SemiDynaEXE::UNIT, MeshUnit::Five);
    /// ```
    pub const UNIT: MeshUnit = MeshUnit::Five;

    /// Deserialize _SemiDynaEXE_-formatted [`&str`] into a [`Transformer`].
    ///
    /// ```no_run
    /// # use std::fs;
    /// # use std::error::Error;
    /// # use jgdtrans::{Format, SemiDynaEXE, Point};
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// // deserialize SemiDynaEXE par file, e.g. SemiDyna2023.par
    /// let s = fs::read_to_string("SemiDyna2023.par")?;
    /// let tf = SemiDynaEXE::from_str(&s)?;
    ///
    /// // prints first 16 lines
    /// println!("{:?}", tf.description);
    /// // prints MeshUnit::Five (namely, the mesh unit is 5)
    /// println!("{:?}", tf.unit);
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
    /// # use jgdtrans::parser::SemiDynaEXE;
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
    /// let tf = SemiDynaEXE::from_str(&s)?;
    /// assert_eq!(
    ///     tf.parameter.get(&12345678),
    ///     Some(&Parameter {latitude: 0.00001, longitude: 0.00002, altitude: 0.00003})
    /// );
    /// # Ok(())}
    /// ```
    pub fn from_str(s: &str) -> Result<Transformer> {
        parser(
            s,
            16,
            Some(0..8),
            Some(9..18),
            Some(19..28),
            Some(29..38),
            MeshUnit::Five,
        )
    }
}

/// Provides deserializer of _geonetF3_-formatted [`&str`] into a [`Transformer`].
#[allow(non_snake_case)]
#[allow(unused)]
pub mod geonetF3 {
    use super::*;

    /// The mesh unit of _geonetF3_, [`MeshUnit::Five`].
    ///
    /// ```
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::parser::geonetF3;
    /// assert_eq!(geonetF3::UNIT, MeshUnit::Five);
    /// ```
    pub const UNIT: MeshUnit = MeshUnit::Five;

    /// Deserialize _geonetF3_-formatted [`&str`] into a [`Transformer`].
    ///
    /// ```no_run
    /// # use std::fs;
    /// # use std::error::Error;
    /// # use jgdtrans::{Format, geonetF3, Point};
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// // deserialize geonetF3 par file, e.g. pos2jgd_202101_geonetF3.par
    /// let s = fs::read_to_string("pos2jgd_202101_geonetF3.par")?;
    /// let tf = geonetF3::from_str(&s)?;
    ///
    /// // prints first 18 lines
    /// println!("{:?}", tf.description);
    /// // prints MeshUnit::Five (namely, the mesh unit is 5)
    /// println!("{:?}", tf.unit);
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
    /// # use jgdtrans::parser::geonetF3;
    /// # use jgdtrans::transformer::Parameter;
    /// # fn main() -> Result<()> {
    /// let s = r"<17 lines>
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
    /// # ...
    /// # ...
    /// END OF HEADER
    /// 12345678      0.00001   0.00002   0.00003";
    /// let tf = geonetF3::from_str(&s)?;
    /// assert_eq!(
    ///     tf.parameter.get(&12345678),
    ///     Some(&Parameter {latitude: 0.00001, longitude: 0.00002, altitude: 0.00003})
    /// );
    /// # Ok(())}
    pub fn from_str(s: &str) -> Result<Transformer> {
        parser(
            s,
            18,
            Some(0..8),
            Some(12..21),
            Some(22..31),
            Some(32..41),
            MeshUnit::Five,
        )
    }
}

/// Provides deserializer of _ITRF2014_-formatted [`&str`] into a [`Transformer`].
#[allow(non_snake_case)]
#[allow(unused)]
pub mod ITRF2014 {
    use super::*;

    /// The mesh unit of _ITRF2014_, [`MeshUnit::Five`].
    ///
    /// ```
    /// # use jgdtrans::mesh::MeshUnit;
    /// # use jgdtrans::parser::ITRF2014;
    /// assert_eq!(ITRF2014::UNIT, MeshUnit::Five);
    /// ```
    pub const UNIT: MeshUnit = MeshUnit::Five;

    /// Deserialize _ITRF2014_-formatted [`&str`] into a [`Transformer`].
    ///
    /// ```no_run
    /// # use std::fs;
    /// # use std::error::Error;
    /// # use jgdtrans::{Format, ITRF2014, Point};
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// // deserialize ITRF2014 par file, e.g. pos2jgd_202307_ITRF2014.par
    /// let s = fs::read_to_string("pos2jgd_202307_ITRF2014.par")?;
    /// let tf = ITRF2014::from_str(&s)?;
    ///
    /// // prints first 18 lines
    /// println!("{:?}", tf.description);
    /// // prints MeshUnit::Five (namely, the mesh unit is 5)
    /// println!("{:?}", tf.unit);
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
    /// # use jgdtrans::parser::ITRF2014;
    /// # use jgdtrans::transformer::Parameter;
    /// # fn main() -> Result<()> {
    /// let s = r"<17 lines>
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
    /// # ...
    /// # ...
    /// END OF HEADER
    /// 12345678      0.00001   0.00002   0.00003";
    /// let tf = ITRF2014::from_str(&s)?;
    /// assert_eq!(
    ///     tf.parameter.get(&12345678),
    ///     Some(&Parameter{latitude: 0.00001, longitude: 0.00002, altitude: 0.00003})
    /// );
    /// # Ok(())}
    pub fn from_str(s: &str) -> Result<Transformer> {
        parser(
            s,
            18,
            Some(0..8),
            Some(12..21),
            Some(22..31),
            Some(32..41),
            MeshUnit::Five,
        )
    }
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
            let actual = TKY2JGD::from_str(&text);
            let expected = Transformer {
                unit: MeshUnit::One,
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
            let actual = TKY2JGD::from_str(text);
            let expected = Transformer {
                unit: MeshUnit::One,
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
            let actual = PatchJGD::from_str(&text);
            let expected = Transformer {
                unit: MeshUnit::One,
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
            let actual = PatchJGD_H::from_str(&text);
            let expected = Transformer {
                unit: MeshUnit::One,
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
            let actual = PatchJGD_HV::from_str(&text);
            let expected = Transformer {
                unit: MeshUnit::One,
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
            let actual = HyokoRev::from_str(&text);
            let expected = Transformer {
                unit: MeshUnit::One,
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
            let actual = SemiDynaEXE::from_str(&text);
            let expected = Transformer {
                unit: MeshUnit::Five,
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
            let actual = geonetF3::from_str(&text);
            let expected = Transformer {
                unit: MeshUnit::Five,
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
            let actual = ITRF2014::from_str(&text);
            let expected = Transformer {
                unit: MeshUnit::Five,
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
