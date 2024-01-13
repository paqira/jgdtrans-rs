use std::collections::BTreeMap;

use crate::error;
use crate::transformer::Parameter;
use crate::{mesh::MeshUnit, Error, Result, Transformer};

struct Slice {
    start: usize,
    end: usize,
}

fn parser(
    text: &str,
    header: &usize,
    mesh_code: &Option<Slice>,
    latitude: &Option<Slice>,
    longitude: &Option<Slice>,
    altitude: &Option<Slice>,
    unit: MeshUnit,
) -> Result<Transformer> {
    let description = text.lines().take(*header).collect::<Vec<_>>().join("\n");

    macro_rules! make_error {
        ($slice:expr, $lineno:ident, $error:expr) => {
            Error {
                err: Box::new(error::ErrorImpl::ParseParError {
                    kind: $error,
                    lineno: $lineno,
                    start: $slice.start,
                    end: $slice.end,
                }),
            }
        };
    }

    let parameter: BTreeMap<u32, Parameter> =
        text.lines()
            .enumerate()
            .skip(*header)
            .map(|(lineno, line)| {
                let mesh_code: u32 = match mesh_code {
                    Some(slice) => line[slice.start..slice.end].trim().parse().map_err(|_| {
                        make_error!(slice, lineno, error::ParseParErrorImpl::Meshcode)
                    })?,
                    None => u32::default(),
                };

                let latitude: f64 = match latitude {
                    Some(slice) => line[slice.start..slice.end].trim().parse().map_err(|_| {
                        make_error!(slice, lineno, error::ParseParErrorImpl::Latitude)
                    })?,
                    None => f64::default(),
                };

                let longitude: f64 = match longitude {
                    Some(slice) => line[slice.start..slice.end].trim().parse().map_err(|_| {
                        make_error!(slice, lineno, error::ParseParErrorImpl::Longitude)
                    })?,
                    None => f64::default(),
                };

                let altitude: f64 = match altitude {
                    Some(slice) => line[slice.start..slice.end].trim().parse().map_err(|_| {
                        make_error!(slice, lineno, error::ParseParErrorImpl::Altitude)
                    })?,
                    None => f64::default(),
                };

                Ok((
                    mesh_code,
                    Parameter {
                        latitude,
                        longitude,
                        altitude,
                    },
                ))
            })
            .collect::<Result<_>>()?;

    Ok(Transformer {
        unit,
        parameter,
        description: Some(description),
    })
}

/// Represents format of par-formatted text.
pub enum Format {
    /// for TKY2JGD
    TKY2JGD,
    /// for PatchJGD
    PatchJGD,
    /// for PatchJGD(H)
    #[allow(non_camel_case_types)]
    PatchJGD_H,
    /// for PatchJGD(HV)
    ///
    /// We note that GIAJ does not distribute such file,
    /// see  [`PatchJGD_HV`] for detail.
    #[allow(non_camel_case_types)]
    PatchJGD_HV,
    /// for HyokoRev
    HyokoRev,
    /// for SemiDynaEXE
    #[allow(non_camel_case_types)]
    SemiDynaEXE,
    /// for geonetF3
    #[allow(non_camel_case_types)]
    geonetF3,
    /// for ITRF2014
    ITRF2014,
}

/// Deserialize par-formatted [`&str`] into a [`Transformer`].
///
/// Use `format` argument to specify the format of `s`.
///
/// This fills by 0.0 for altituse parameter when [`Format::TKY2JGD`] or [`Format::PatchJGD`] given,
/// and for latitude and longitude when [`Format::PatchJGD_H`] or [`Format::HyokoRev`] given.
///
/// ```no_run
/// # use std::fs;
/// # use std::error::Error;
/// # use jgdtrans::{from_str, Format};
/// # fn main() -> Result<(), Box<dyn Error>> {
/// // deserialize par file, e.g. SemiDyna2023.par
/// let s = fs::read_to_string("SemiDyna2023.par")?;
/// let tf = from_str(&s, Format::SemiDynaEXE)?;
///
/// // prints first 16 lines
/// println!("{:?}", tf.description);
/// // prints MeshUnit::Five (namely, the mesh unit is 5)
/// println!("{:?}", tf.unit);
/// // prints all of parameter (be careful, long long display)
/// println!("{:?}", tf.parameter);
///
/// // transform coordinate
/// let result = tf.forward(&(35.0, 135.0).into());
/// # Ok(())}
/// ```
///
/// # Errros
///
/// If invalid data found.
///
/// # Example
///
/// ```
/// # use jgdtrans::*;
/// # use jgdtrans::parser::Format;
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
    let f = match format {
        Format::TKY2JGD => TKY2JGD::from_str,
        Format::PatchJGD => PatchJGD::from_str,
        Format::PatchJGD_H => PatchJGD_H::from_str,
        Format::PatchJGD_HV => PatchJGD_HV::from_str,
        Format::HyokoRev => HyokoRev::from_str,
        Format::SemiDynaEXE => SemiDynaEXE::from_str,
        Format::geonetF3 => geonetF3::from_str,
        Format::ITRF2014 => ITRF2014::from_str,
    };
    f(s)
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
    /// # use jgdtrans::{from_str, Format, TKY2JGD};
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// // deserialize TKY2JGD par file
    /// let s = fs::read_to_string("TKY2JGD.par")?;
    /// let tf = TKY2JGD::from_str(&s)?;
    ///
    /// // prints first 2 lines
    /// println!("{:?}", tf.description);
    /// // prints MeshUnit::One (namely, the mesh unit is 1)
    /// println!("{:?}", tf.unit);
    /// // prints all of parameter (be careful, long long display)
    /// println!("{:?}", tf.parameter);
    ///
    /// // transform coordinate
    /// let result = tf.forward(&(35.0, 135.0).into());
    /// # Ok(())}
    /// ```
    ///
    /// This fill by 0 for the altitude parameter.
    ///
    /// # Errros
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
            &2,
            &Some(Slice { start: 0, end: 8 }),
            &Some(Slice { start: 9, end: 18 }),
            &Some(Slice { start: 19, end: 28 }),
            &None,
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
    /// # use jgdtrans::{from_str, Format, PatchJGD};
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// // deserialize PatchJGD par file, e.g. touhokutaiheiyouoki2011.par
    /// let s = fs::read_to_string("touhokutaiheiyouoki2011.par")?;
    /// let tf = PatchJGD::from_str(&s)?;
    ///
    /// // prints first 16 lines
    /// println!("{:?}", tf.description);
    /// // prints MeshUnit::One (namely, the mesh unit is 1)
    /// println!("{:?}", tf.unit);
    /// // prints all of parameter (be careful, long long display)
    /// println!("{:?}", tf.parameter);
    ///
    /// // transform coordinate
    /// let result = tf.forward(&(35.0, 135.0).into());
    /// # Ok(())}
    /// ```
    ///
    /// This fill by 0 for the altitude parameter.
    ///
    /// # Errros
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
            &16,
            &Some(Slice { start: 0, end: 8 }),
            &Some(Slice { start: 9, end: 18 }),
            &Some(Slice { start: 19, end: 28 }),
            &None,
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
    /// # use jgdtrans::{from_str, Format, PatchJGD_H};
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// // deserialize PatchJGD(H) par file, e.g. touhokutaiheiyouoki2011_h.par
    /// let s = fs::read_to_string("touhokutaiheiyouoki2011_h.par")?;
    /// let tf = PatchJGD_H::from_str(&s)?;
    ///
    /// // prints first 16 lines
    /// println!("{:?}", tf.description);
    /// // prints MeshUnit::One (namely, the mesh unit is 1)
    /// println!("{:?}", tf.unit);
    /// // prints all of parameter (be careful, long long display)
    /// println!("{:?}", tf.parameter);
    ///
    /// // transform coordinate
    /// let result = tf.forward(&(35.0, 135.0).into());
    /// # Ok(())}
    /// ```
    ///
    /// This fill by 0 for the latitude and the longitude parameter.
    ///
    /// # Errros
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
        parser(
            s,
            &16,
            &Some(Slice { start: 0, end: 8 }),
            &None,
            &None,
            &Some(Slice { start: 9, end: 18 }),
            MeshUnit::One,
        )
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
    /// # use jgdtrans::{from_str, Format, PatchJGD_HV};
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// // deserialize PatchJGD(HV) par file
    /// let s = fs::read_to_string("touhokutaiheiyouoki2011_hv.par")?;
    /// let tf = PatchJGD_HV::from_str(&s)?;
    ///
    /// // prints first 16 lines
    /// println!("{:?}", tf.description);
    /// // prints MeshUnit::One (namely, the mesh unit is 1)
    /// println!("{:?}", tf.unit);
    /// // prints all of parameter (be careful, long long display)
    /// println!("{:?}", tf.parameter);
    ///
    /// // transform coordinate
    /// let result = tf.forward(&(35.0, 135.0).into());
    /// # Ok(())}
    /// ```
    ///
    /// # Errros
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
            &16,
            &Some(Slice { start: 0, end: 8 }),
            &Some(Slice { start: 9, end: 18 }),
            &Some(Slice { start: 19, end: 28 }),
            &Some(Slice { start: 29, end: 38 }),
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
    /// # use jgdtrans::{from_str, Format, HyokoRev};
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// // deserialize HyokoRev par file, e.g. hyokorev2014_geoid2011_h.par
    /// let s = fs::read_to_string("hyokorev2014_geoid2011_h.par")?;
    /// let tf = HyokoRev::from_str(&s)?;
    ///
    /// // prints first 16 lines
    /// println!("{:?}", tf.description);
    /// // prints MeshUnit::One (namely, the mesh unit is 1)
    /// println!("{:?}", tf.unit);
    /// // prints all of parameter (be careful, long long display)
    /// println!("{:?}", tf.parameter);
    ///
    /// // transform coordinate
    /// let result = tf.forward(&(35.0, 135.0).into());
    /// # Ok(())}
    /// ```
    ///
    /// # Errros
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
        parser(
            s,
            &16,
            &Some(Slice { start: 0, end: 8 }),
            &None,
            &None,
            &Some(Slice { start: 12, end: 21 }),
            MeshUnit::One,
        )
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
    /// # use jgdtrans::{from_str, Format, SemiDynaEXE};
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// // deserialize SemiDynaEXE par file, e.g. SemiDyna2023.par
    /// let s = fs::read_to_string("SemiDyna2023.par")?;
    /// let tf = SemiDynaEXE::from_str(&s)?;
    ///
    /// // prints first 16 lines
    /// println!("{:?}", tf.description);
    /// // prints MeshUnit::Five (namely, the mesh unit is 5)
    /// println!("{:?}", tf.unit);
    /// // prints all of parameter (be careful, long long display)
    /// println!("{:?}", tf.parameter);
    ///
    /// // transform coordinate
    /// let result = tf.forward(&(35.0, 135.0).into());
    /// # Ok(())}
    /// ```
    ///
    /// # Errros
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
            &16,
            &Some(Slice { start: 0, end: 8 }),
            &Some(Slice { start: 9, end: 18 }),
            &Some(Slice { start: 19, end: 28 }),
            &Some(Slice { start: 29, end: 38 }),
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
    /// # use jgdtrans::{from_str, Format, geonetF3};
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// // deserialize geonetF3 par file, e.g. pos2jgd_202101_geonetF3.par
    /// let s = fs::read_to_string("pos2jgd_202101_geonetF3.par")?;
    /// let tf = geonetF3::from_str(&s)?;
    ///
    /// // prints first 18 lines
    /// println!("{:?}", tf.description);
    /// // prints MeshUnit::Five (namely, the mesh unit is 5)
    /// println!("{:?}", tf.unit);
    /// // prints all of parameter (be careful, long long display)
    /// println!("{:?}", tf.parameter);
    ///
    /// // transform coordinate
    /// let result = tf.forward(&(35.0, 135.0).into());
    /// # Ok(())}
    /// ```
    ///
    /// # Errros
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
            &18,
            &Some(Slice { start: 0, end: 8 }),
            &Some(Slice { start: 12, end: 21 }),
            &Some(Slice { start: 22, end: 31 }),
            &Some(Slice { start: 32, end: 41 }),
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
    /// # use jgdtrans::{from_str, Format, ITRF2014};
    /// # fn main() -> Result<(), Box<dyn Error>> {
    /// // deserialize ITRF2014 par file, e.g. pos2jgd_202307_ITRF2014.par
    /// let s = fs::read_to_string("pos2jgd_202307_ITRF2014.par")?;
    /// let tf = ITRF2014::from_str(&s)?;
    ///
    /// // prints first 18 lines
    /// println!("{:?}", tf.description);
    /// // prints MeshUnit::Five (namely, the mesh unit is 5)
    /// println!("{:?}", tf.unit);
    /// // prints all of parameter (be careful, long long display)
    /// println!("{:?}", tf.parameter);
    ///
    /// // transform coordinate
    /// let result = tf.forward(&(35.0, 135.0).into());
    /// # Ok(())}
    /// ```
    ///
    /// # Errros
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
            &18,
            &Some(Slice { start: 0, end: 8 }),
            &Some(Slice { start: 12, end: 21 }),
            &Some(Slice { start: 22, end: 31 }),
            &Some(Slice { start: 32, end: 41 }),
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
