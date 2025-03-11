//! Provides deserializer of par file.
use std::collections::HashMap;
use std::error::Error;
use std::fmt::{Display, Formatter};
use std::hash::{BuildHasher, Hash, RandomState};
use std::num::{ParseFloatError, ParseIntError};
use std::ops::Range;

use crate::mesh::MeshUnit;
use crate::{Parameter, ParameterData, ParameterSet};

/// Represents format of par-formatted text.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
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

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ParData<
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
            serialize = "HashMap<u32, Parameter, S>: serde::Serialize",
            deserialize = "HashMap<u32, Parameter, S>: serde::Deserialize<'de>"
        ))
    )]
    pub parameter: HashMap<u32, Parameter, S>,
    /// The description, or the header of par-formatted data.
    #[cfg_attr(feature = "serde", serde(skip_serializing_if = "Option::is_none"))]
    pub description: Option<String>,
}

impl<#[cfg(not(feature = "serde"))] S, #[cfg(feature = "serde")] S: Default> ParData<S> {
    /// Makes a [`Transformer`].
    ///
    /// We note that we provide a builder, see [`TransformerBuilder`](crate::ParDataBuilder).
    ///
    /// # Example
    ///
    /// ```
    /// # use std::collections::HashMap;
    /// # use jgdtrans::*;
    /// # use jgdtrans::mesh::MeshUnit;
    /// #
    /// // from SemiDynaEXE2023.par
    /// let tf = ParData::new(
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
    #[must_use]
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
    /// let tf = ParData::with_description(
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
    #[must_use]
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
}

impl ParData<RandomState> {
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
    /// let data = ParData::from_str(&s, Format::SemiDynaEXE)?;
    ///
    /// assert_eq!(data.format, Format::SemiDynaEXE);
    /// assert_eq!(
    ///     data.parameter.get(&12345678),
    ///     Some(&Parameter::new(0.00001, 0.00002, 0.00003))
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[inline]
    pub fn from_str(s: &str, format: Format) -> Result<Self, ParseParError> {
        ParParser::new(format).parse(s)
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
    /// let data = ParData::from_str_with_description(
    ///     &s,
    ///     Format::SemiDynaEXE,
    ///     "SemiDyna2023.par".to_string(),
    /// )?;
    ///
    /// assert_eq!(data.format, Format::SemiDynaEXE);
    /// assert_eq!(
    ///     data.parameter.get(&12345678),
    ///     Some(&Parameter::new(0.00001, 0.00002, 0.00003))
    /// );
    /// assert_eq!(data.description, Some("SemiDyna2023.par".to_string()));
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[inline]
    pub fn from_str_with_description(
        s: &str,
        format: Format,
        description: String,
    ) -> Result<Self, ParseParError> {
        ParParser::new(format).parse_with_description(s, description)
    }
}

impl<#[cfg(not(feature = "serde"))] S, #[cfg(feature = "serde")] S: Default> ParameterSet
    for ParData<S>
where
    S: BuildHasher,
{
    #[inline]
    fn mesh_unit(&self) -> MeshUnit {
        self.format.mesh_unit()
    }

    #[inline]
    fn get(&self, meshcode: &u32) -> Option<&Parameter> {
        self.parameter.get(meshcode)
    }
}

impl<#[cfg(not(feature = "serde"))] S, #[cfg(feature = "serde")] S: Default> ParameterData
    for ParData<S>
where
    S: BuildHasher,
{
    #[inline]
    fn to_vec(&self) -> Vec<(&u32, &Parameter)> {
        self.parameter.iter().collect()
    }
}

impl<#[cfg(not(feature = "serde"))] S, #[cfg(feature = "serde")] S: Default> PartialEq
    for ParData<S>
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

impl<#[cfg(not(feature = "serde"))] S, #[cfg(feature = "serde")] S: Default> Clone for ParData<S>
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

#[allow(clippy::too_many_arguments)]
#[allow(clippy::type_complexity)]
fn parse<S>(
    text: &str,
    header: usize,
    meshcode: Range<usize>,
    latitude: Option<Range<usize>>,
    longitude: Option<Range<usize>>,
    altitude: Option<Range<usize>>,
    capacity: Option<usize>,
    hash_builder: S,
) -> Result<(HashMap<u32, Parameter, S>, String), ParseParError>
where
    S: BuildHasher,
{
    if text.lines().count().lt(&header) {
        return Err(ParseParError::new(
            0,
            text.lines().by_ref().last().map_or(0, str::len),
            text.lines().count(),
            ParseParErrorKind::Header,
            None,
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

    let mut parameter = if let Some(cap) = capacity {
        HashMap::with_capacity_and_hasher(cap, hash_builder)
    } else {
        HashMap::with_hasher(hash_builder)
    };

    for (lineno, line) in lines {
        let meshcode = line
            .get(meshcode.clone())
            .ok_or(ParseParError::new(
                meshcode.start,
                meshcode.end,
                lineno + 1,
                ParseParErrorKind::ColumnNotFound,
                Some(Column::Meshcode),
            ))?
            .trim()
            .parse()
            .map_err(|e| {
                ParseParError::new(
                    meshcode.start,
                    meshcode.end,
                    lineno + 1,
                    ParseParErrorKind::ParseInt(e),
                    Some(Column::Meshcode),
                )
            })?;

        let latitude = match latitude {
            None => 0.0,
            Some(ref range) => line
                .get(range.clone())
                .ok_or(ParseParError::new(
                    range.start,
                    range.end,
                    lineno + 1,
                    ParseParErrorKind::ColumnNotFound,
                    Some(Column::Latitude),
                ))?
                .trim()
                .parse()
                .map_err(|e| {
                    ParseParError::new(
                        range.start,
                        range.end,
                        lineno + 1,
                        ParseParErrorKind::ParseFloat(e),
                        Some(Column::Latitude),
                    )
                })?,
        };

        let longitude = match longitude {
            None => 0.0,
            Some(ref range) => line
                .get(range.clone())
                .ok_or(ParseParError::new(
                    range.start,
                    range.end,
                    lineno + 1,
                    ParseParErrorKind::ColumnNotFound,
                    Some(Column::Longitude),
                ))?
                .trim()
                .parse()
                .map_err(|e| {
                    ParseParError::new(
                        range.start,
                        range.end,
                        lineno + 1,
                        ParseParErrorKind::ParseFloat(e),
                        Some(Column::Longitude),
                    )
                })?,
        };

        let altitude = match altitude {
            None => 0.0,
            Some(ref range) => line
                .get(range.clone())
                .ok_or(ParseParError::new(
                    range.start,
                    range.end,
                    lineno + 1,
                    ParseParErrorKind::ColumnNotFound,
                    Some(Column::Altitude),
                ))?
                .trim()
                .parse()
                .map_err(|e| {
                    ParseParError::new(
                        range.start,
                        range.end,
                        lineno + 1,
                        ParseParErrorKind::ParseFloat(e),
                        Some(Column::Altitude),
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

    Ok((parameter, description))
}

/// Parser of par-formatted [`&str`].
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
/// let data = ParParser::new(Format::SemiDynaEXE).parse(&s)?;
///
/// assert_eq!(
///     data.parameter.get(&12345678),
///     Some(&Parameter::new(0.00001, 0.00002, 0.00003))
/// );
/// # Ok::<(), Box<dyn Error>>(())
/// ```
#[derive(Debug)]
pub struct ParParser<S = RandomState> {
    format: Format,
    capacity: Option<usize>,
    hash_builder: S,
}

impl ParParser<RandomState> {
    /// Makes a parser.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::error::Error;
    /// # use jgdtrans::*;
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
    ///
    /// let parser = ParParser::new(Format::SemiDynaEXE);
    /// let tf = parser.parse(s)?;
    ///
    /// assert_eq!(
    ///     tf.parameter.get(&12345678),
    ///     Some(&Parameter::new(0.00001, 0.00002, 0.00003))
    /// );
    /// # Ok::<(), Box<dyn Error>>(())
    /// ```
    #[inline]
    #[must_use]
    pub fn new(format: Format) -> Self {
        Self::with_hasher(format, RandomState::new())
    }

    /// Makes a parser with at least the specified initial capacity.
    ///
    /// Notes, the capacity of resulting [`Transformer::parameter`]
    /// is shrunk as much as possible.
    ///
    /// See [`HashMap::with_capacity`], for detail.
    ///
    /// # Example
    ///
    /// ```
    /// # use jgdtrans::*;
    /// let parser = ParParser::with_capacity(Format::SemiDynaEXE, 10);
    /// ```
    #[inline]
    #[must_use]
    pub fn with_capacity(format: Format, capacity: usize) -> Self {
        Self::with_capacity_and_hasher(format, capacity, RandomState::new())
    }
}

impl<#[cfg(not(feature = "serde"))] S, #[cfg(feature = "serde")] S: Default> ParParser<S> {
    /// Makes a parser which uses the given hash builder to hash meshcode.
    ///
    /// See [`HashMap::with_hasher`], for detail.
    ///
    /// # Example
    ///
    /// ```
    /// use std::hash::RandomState;
    /// # use jgdtrans::*;
    ///
    /// let parser = ParParser::with_hasher(Format::SemiDynaEXE, RandomState::new());
    /// ```
    #[inline]
    pub const fn with_hasher(format: Format, hash_builder: S) -> Self {
        Self {
            format,
            capacity: None,
            hash_builder,
        }
    }

    /// Makes a parser with at least the specified initial capacity, which uses the given hash builder to hash meshcode.
    ///
    /// Notes, the capacity of resulting [`Transformer::parameter`]
    /// is shrunk as much as possible.
    ///
    /// See [`HashMap::with_capacity_and_hasher`], for detail.
    ///
    /// # Example
    ///
    /// ```
    /// use std::hash::RandomState;
    /// # use jgdtrans::*;
    ///
    /// let parser = ParParser::with_capacity_and_hasher(Format::SemiDynaEXE, 10, RandomState::new());
    /// ```
    #[inline]
    pub const fn with_capacity_and_hasher(
        format: Format,
        capacity: usize,
        hash_builder: S,
    ) -> Self {
        Self {
            format,
            capacity: Some(capacity),
            hash_builder,
        }
    }
}

impl<#[cfg(not(feature = "serde"))] S, #[cfg(feature = "serde")] S: Default> ParParser<S>
where
    S: BuildHasher,
{
    /// Deserialize par-formatted [`&str`] into a [`Transformer`].
    #[inline]
    pub fn parse(self, s: &str) -> Result<ParData<S>, ParseParError> {
        let (header, meshcode, latitude, longitude, altitude) = match self.format {
            Format::TKY2JGD => (2, 0..8, Some(9..18), Some(19..28), None),
            Format::PatchJGD => (16, 0..8, Some(9..18), Some(19..28), None),
            Format::PatchJGD_H => (16, 0..8, None, None, Some(9..18)),
            Format::HyokoRev => (16, 0..8, None, None, Some(12..21)),
            Format::PatchJGD_HV | Format::SemiDynaEXE => {
                (16, 0..8, Some(9..18), Some(19..28), Some(29..38))
            }
            Format::geonetF3 | Format::ITRF2014 => {
                (18, 0..8, Some(12..21), Some(22..31), Some(32..41))
            }
        };

        let (parameter, description) = parse(
            s,
            header,
            meshcode,
            latitude,
            longitude,
            altitude,
            self.capacity,
            self.hash_builder,
        )?;

        Ok(ParData {
            format: self.format,
            parameter,
            description: Some(description),
        })
    }

    /// Deserialize par-formatted [`&str`] into a [`Transformer`] with `description`.
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
    /// let tf = ParParser::new(Format::SemiDynaEXE)
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
    ) -> Result<ParData<S>, ParseParError> {
        let mut data = self.parse(s)?;
        data.description.replace(description);
        Ok(data)
    }
}

impl<#[cfg(not(feature = "serde"))] S, #[cfg(feature = "serde")] S: Default> Clone for ParParser<S>
where
    S: Clone,
{
    #[inline]
    fn clone(&self) -> Self {
        Self {
            format: self.format.clone(),
            capacity: self.capacity,
            hash_builder: self.hash_builder.clone(),
        }
    }

    #[inline]
    fn clone_from(&mut self, source: &Self) {
        self.format.clone_from(&source.format);
        self.capacity.clone_from(&source.capacity);
        self.hash_builder.clone_from(&source.hash_builder);
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
    /// Lineno of the data
    lineno: usize,
    /// Error part, `None` if `kind` is `Header`.
    column: Option<Column>,
    /// Start colum no. of the data
    start: usize,
    /// End colum no. of the data
    end: usize,
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
}

impl ParseParError {
    #[cold]
    const fn new(
        start: usize,
        end: usize,
        lineno: usize,
        kind: ParseParErrorKind,
        column: Option<Column>,
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

    /// Returns the error column name, `None` if it errors on header.
    pub const fn column(&self) -> &Option<Column> {
        &self.column
    }

    /// Returns the error line number.
    pub const fn lineno(&self) -> &usize {
        &self.lineno
    }

    /// Returns the error starts position.
    pub const fn start(&self) -> &usize {
        &self.start
    }

    /// Returns the error ends position.
    pub const fn end(&self) -> &usize {
        &self.end
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
            ParseParErrorKind::Header => f.write_str("parse error: header"),
            _ => match &self.column {
                None => unreachable!(),
                Some(name) => write!(
                    f,
                    "parse error: {} l{}:{}:{}",
                    name, self.lineno, self.start, self.end
                ),
            },
        }
    }
}

impl Display for Column {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        let s = match self {
            Self::Meshcode => "meshcode",
            Self::Latitude => "latitude",
            Self::Longitude => "longitude",
            Self::Altitude => "altitude",
        };
        f.write_str(s)
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
            let actual = ParData::from_str(&text, Format::TKY2JGD).unwrap();
            let expected = ParData {
                format: Format::TKY2JGD,
                parameter: [].into_iter().collect(),
                description: Some(
                    "JGD2000-TokyoDatum Ver.2.1.2
MeshCode   dB(sec)   dL(sec)
"
                    .to_string(),
                ),
            };
            transformer_eq!(expected, actual);

            let text = "JGD2000-TokyoDatum Ver.2.1.2";
            let actual = ParData::from_str(&text, Format::TKY2JGD);
            assert!(actual.is_err());

            let text = "";
            let actual = ParData::from_str(&text, Format::TKY2JGD);
            assert!(actual.is_err());
        }

        #[test]
        fn test_meshcode() {
            let text = "\n".repeat(15)
                + "MeshCode dB(sec)  dL(sec) dH(m)
000x0000   0.00001   0.00002   0.00003
10000000 -10.00001 -10.00002 -10.00003";
            let actual = ParData::from_str(&text, Format::SemiDynaEXE).unwrap_err();

            assert_eq!(actual.start, 0);
            assert_eq!(actual.end, 8);
            assert_eq!(actual.lineno, 17);
            assert!(matches!(actual.column, Some(Column::Meshcode)));
        }

        #[test]
        fn test_latitude() {
            let text = "\n".repeat(15)
                + "MeshCode dB(sec)  dL(sec) dH(m)
00000000   0.0000x   0.00002   0.00003
10000000 -10.00001 -10.00002 -10.00003";
            let actual = ParData::from_str(&text, Format::SemiDynaEXE).unwrap_err();

            assert_eq!(actual.start, 9);
            assert_eq!(actual.end, 18);
            assert_eq!(actual.lineno, 17);
            assert!(matches!(actual.column, Some(Column::Latitude)));
        }

        #[test]
        fn test_longitude() {
            let text = "\n".repeat(15)
                + "MeshCode dB(sec)  dL(sec) dH(m)
00000000   0.00001   0.0000x   0.00003
10000000 -10.00001 -10.00002 -10.00003";
            let actual = ParData::from_str(&text, Format::SemiDynaEXE).unwrap_err();

            assert_eq!(actual.start, 19);
            assert_eq!(actual.end, 28);
            assert_eq!(actual.lineno, 17);
            assert!(matches!(actual.column, Some(Column::Longitude)));
        }

        #[test]
        fn test_altitude() {
            let text = "\n".repeat(15)
                + "MeshCode dB(sec)  dL(sec) dH(m)
00000000   0.00001   0.00002   0.0000x
10000000 -10.00001 -10.00002 -10.00003";
            let actual = ParData::from_str(&text, Format::SemiDynaEXE).unwrap_err();

            assert_eq!(actual.start, 29);
            assert_eq!(actual.end, 38);
            assert_eq!(actual.lineno, 17);
            assert!(matches!(actual.column, Some(Column::Altitude)));
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
            let actual = ParData::from_str(&text, Format::TKY2JGD).unwrap();
            let expected = ParData {
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
            let actual = ParData::from_str(&text, Format::TKY2JGD).unwrap();
            let expected = ParData {
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
            let actual = ParData::from_str(&text, Format::PatchJGD).unwrap();
            let expected = ParData {
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
            let actual = ParData::from_str(&text, Format::PatchJGD_H).unwrap();
            let expected = ParData {
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
            let actual = ParData::from_str(&text, Format::PatchJGD_HV).unwrap();
            let expected = ParData {
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
            let actual = ParData::from_str(&text, Format::HyokoRev).unwrap();
            let expected = ParData {
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
            let actual = ParData::from_str(&text, Format::SemiDynaEXE).unwrap();
            let expected = ParData {
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
            let actual = ParData::from_str(&text, Format::geonetF3).unwrap();
            let expected = ParData {
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
            let actual = ParData::from_str(&text, Format::ITRF2014).unwrap();
            let expected = ParData {
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
