use std::num::{ParseFloatError, ParseIntError};

/// Alias for a `Result<T, jgdtrans::error::Error>`.
pub type Result<T> = std::result::Result<T, Error>;

/// Represents all possible errors that can occur by this crate.
#[derive(Debug)]
pub struct Error {
    err: Box<ErrorKind>,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.err)
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self.err.as_ref() {
            ErrorKind::ParseParError { kind, .. } => match kind {
                ParseParErrorKind::Missing => None,
                ParseParErrorKind::ParseInt(ref err) => Some(err),
                ParseParErrorKind::ParseFloat(ref err) => Some(err),
            },
            _ => None,
        }
    }
}

impl Error {
    /// Returns a error kind.
    pub fn kind(&self) -> &ErrorKind {
        &self.err
    }
}

impl Error {
    #[cold]
    pub(crate) fn new(err: ErrorKind) -> Self {
        Self { err: Box::new(err) }
    }
    #[cold]
    pub(crate) fn new_parse_par(
        start: usize,
        end: usize,
        lineno: usize,
        kind: ParseParErrorKind,
        column: ParColumn,
    ) -> Self {
        Self::new(ErrorKind::ParseParError {
            kind,
            column,
            lineno,
            start,
            end,
        })
    }
    #[cold]
    pub(crate) fn new_parse_dms(kind: ParseDMSErrorKind) -> Self {
        Self::new(ErrorKind::ParseDMSError { kind })
    }
    #[cold]
    pub(crate) fn new_try_from_dms(kind: TryFromDMSErrorKind) -> Self {
        Self::new(ErrorKind::TryFromDMSError { kind })
    }
    #[cold]
    pub(crate) fn new_transform(kind: TransformErrorKind) -> Self {
        Self::new(ErrorKind::TransformError { kind })
    }
}

#[derive(Debug)]
pub enum ErrorKind {
    /// Invalid data found in par-formatted data.
    ParseParError {
        /// Error kind
        kind: ParseParErrorKind,
        // Error Column
        column: ParColumn,
        /// Lineno of the data
        lineno: usize,
        /// Start colum no. of the data
        start: usize,
        /// End colum no. of the data
        end: usize,
    },
    ParseDMSError {
        kind: ParseDMSErrorKind,
    },
    TryFromDMSError {
        kind: TryFromDMSErrorKind,
    },
    TransformError {
        kind: TransformErrorKind,
    },
}

impl std::fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::ParseParError {
                column,
                lineno,
                start,
                end,
                ..
            } => write!(
                f,
                "parse error: {} at l{}:{}:{}",
                column, lineno, start, end
            ),
            Self::ParseDMSError { kind } => write!(f, "{}", kind),
            Self::TryFromDMSError { kind } => write!(f, "{}", kind),
            Self::TransformError { kind } => write!(f, "{}", kind),
        }
    }
}

// common

#[derive(Debug)]
pub enum ParColumn {
    Meshcode,
    Latitude,
    Longitude,
    Altitude,
}

impl std::fmt::Display for ParColumn {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Meshcode => write!(f, "meshcode"),
            Self::Latitude => write!(f, "latitude"),
            Self::Longitude => write!(f, "longitude"),
            Self::Altitude => write!(f, "altitude"),
        }
    }
}

#[derive(Debug)]
pub enum MeshCellCorner {
    NorthWest,
    NorthEast,
    SouthWest,
    SouthEast,
}

impl std::fmt::Display for MeshCellCorner {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::NorthWest => write!(f, "north-west"),
            Self::NorthEast => write!(f, "north-east"),
            Self::SouthWest => write!(f, "south-west"),
            Self::SouthEast => write!(f, "south-east"),
        }
    }
}

// error kind

#[derive(Debug)]
pub enum ParseParErrorKind {
    Missing,
    ParseInt(ParseIntError),
    ParseFloat(ParseFloatError),
}

impl std::fmt::Display for ParseParErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Missing => write!(f, "column not found"),
            Self::ParseInt(..) => write!(f, "parse error: u32"),
            Self::ParseFloat(..) => write!(f, "parse error: f64"),
        }
    }
}

#[derive(Debug)]
pub enum ParseDMSErrorKind {
    InvalidDigit,
    Overflow,
    Empty,
    OutOfBounds,
}

impl std::fmt::Display for ParseDMSErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::InvalidDigit => write!(f, "invalid digit found in string"),
            Self::Overflow => write!(f, "number too large to fit in DMS"),
            Self::Empty => write!(f, "cannot parse DMS from empty string"),
            Self::OutOfBounds => write!(f, "cannot parse out-of-bounds DMS"),
        }
    }
}

#[derive(Debug)]
pub enum TryFromDMSErrorKind {
    Overflow,
    NAN,
}

impl std::fmt::Display for TryFromDMSErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Overflow => write!(f, "number too large to fit in DMS"),
            Self::NAN => write!(f, "number would be NAN"),
        }
    }
}

#[derive(Debug)]
pub enum TransformErrorKind {
    ParameterNotFound {
        meshcode: u32,
        corner: MeshCellCorner,
    },
    CorrectionNotFound,
    Point,
}

impl std::fmt::Display for TransformErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::ParameterNotFound { meshcode, corner } => {
                write!(f, "parameter not found: {} at {}", meshcode, corner)
            }
            Self::CorrectionNotFound => write!(f, "correction not found"),
            Self::Point => write!(f, "location not supported for transformation"),
        }
    }
}
