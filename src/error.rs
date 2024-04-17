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
            ErrorKind::ParseMeshNodeError { kind } => match kind {
                ParseMeshNodeErrorKind::Parse(ref err) => Some(err),
                ParseMeshNodeErrorKind::Overflow(Some(ref err)) => Some(err),
                ParseMeshNodeErrorKind::Overflow(None) => None,
            },
            ErrorKind::TransformError {
                kind: TransformErrorKind::Point(ref err),
            } => Some(err),
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
    pub(crate) fn new_parse_mesh_coord(kind: ParseMeshCoordErrorKind, axis: ErrorAxis) -> Self {
        Self::new(ErrorKind::ParseMeshCoordError { kind, axis })
    }
    #[cold]
    pub(crate) fn new_parse_mesh_node(kind: ParseMeshNodeErrorKind) -> Self {
        Self::new(ErrorKind::ParseMeshNodeError { kind })
    }
    #[cold]
    pub(crate) fn new_parse_mesh_cell(source: Error) -> Self {
        Self::new(ErrorKind::ParseMeshCellError(source))
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
    pub(crate) fn new_point(axis: ErrorAxis, kind: PointErrorKind) -> Self {
        Self::new(ErrorKind::PointError { axis, kind })
    }
    #[cold]
    pub(crate) fn new_transformation(kind: TransformErrorKind) -> Self {
        Self::new(ErrorKind::TransformError { kind })
    }
    #[cold]
    pub(crate) fn new_mesh_coord(kind: MeshCoordErrorKind) -> Self {
        Self::new(ErrorKind::MeshCoordError { kind })
    }
    #[cold]
    pub(crate) fn new_mesh_node(kind: MeshNodeErrorKind) -> Self {
        Self::new(ErrorKind::MeshNodeError { kind })
    }
    #[cold]
    pub(crate) fn new_mesh_cell(kind: MeshCellErrorKind) -> Self {
        Self::new(ErrorKind::MeshCellError { kind })
    }
    #[cold]
    pub(crate) fn new_dms(kind: DMSErrorKind) -> Self {
        Self::new(ErrorKind::DMSError { kind })
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
    /// Invalid meshcode.
    ParseMeshCoordError {
        kind: ParseMeshCoordErrorKind,
        axis: ErrorAxis,
    },
    ParseMeshNodeError {
        kind: ParseMeshNodeErrorKind,
    },
    ParseMeshCellError(Error),
    /// Invalid DMS.
    ParseDMSError {
        kind: ParseDMSErrorKind,
    },
    TryFromDMSError {
        kind: TryFromDMSErrorKind,
    },
    PointError {
        kind: PointErrorKind,
        axis: ErrorAxis,
    },
    TransformError {
        kind: TransformErrorKind,
    },
    MeshCoordError {
        kind: MeshCoordErrorKind,
    },
    MeshNodeError {
        kind: MeshNodeErrorKind,
    },
    MeshCellError {
        kind: MeshCellErrorKind,
    },
    DMSError {
        kind: DMSErrorKind,
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
                "failed parsing {} at l{}:{}:{}",
                column, lineno, start, end
            ),
            Self::ParseMeshCoordError { kind, axis } => write!(f, "{} on {}", kind, axis),
            Self::ParseMeshNodeError { kind } => {
                write!(f, "ParseMeshNodeError: {}", kind)
            }
            Self::ParseMeshCellError(err) => write!(f, "failed conversion to MeshCell, {}", err),
            Self::ParseDMSError { kind } => write!(f, "{}", kind),
            Self::TryFromDMSError { kind } => write!(f, "{}", kind),
            Self::PointError { kind, axis } => write!(f, "{} on {}", kind, axis),
            Self::TransformError { kind } => write!(f, "{}", kind),
            Self::MeshCoordError { kind } => write!(f, "{}", kind),
            Self::MeshNodeError { kind } => write!(f, "{}", kind),
            Self::MeshCellError { kind } => write!(f, "{}", kind),
            Self::DMSError { kind } => write!(f, "{}", kind),
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
pub enum ErrorAxis {
    Latitude,
    Longitude,
    Altitude,
}

impl std::fmt::Display for ErrorAxis {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
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
            Self::ParseInt(..) => write!(f, "failed parsing to u32"),
            Self::ParseFloat(..) => write!(f, "failed parsing to f64"),
        }
    }
}

#[derive(Debug)]
pub enum ParseMeshCoordErrorKind {
    Overflow,
    NAN,
}

impl std::fmt::Display for ParseMeshCoordErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Overflow => write!(f, "number too large to fit in MeshNode"),
            Self::NAN => write!(f, "number would be NAN"),
        }
    }
}

#[derive(Debug)]
pub enum ParseMeshNodeErrorKind {
    Parse(ParseIntError),
    Overflow(Option<Error>),
}

impl std::fmt::Display for ParseMeshNodeErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Parse(..) => write!(f, "failed parsing to u32"),
            Self::Overflow(..) => write!(f, "number too large to fit in MeshNode"),
        }
    }
}

#[derive(Debug)]
pub enum ParseDMSErrorKind {
    InvalidDigit,
    Overflow,
    Empty,
}

impl std::fmt::Display for ParseDMSErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::InvalidDigit => write!(f, "invalid digit found in string"),
            Self::Overflow => write!(f, "number too large to fit in DMS"),
            Self::Empty => write!(f, "cannot parse DMS from empty string"),
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
pub enum PointErrorKind {
    Overflow,
    NAN,
}

impl std::fmt::Display for PointErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Overflow => write!(f, "number too large to fit in Point"),
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
    Point(Error),
    CorrectionNotFound,
}

impl std::fmt::Display for TransformErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::ParameterNotFound { meshcode, corner } => {
                write!(f, "missing parameter of {} at {}", meshcode, corner)
            }
            Self::Point(..) => write!(f, "location not supported for transformation"),
            Self::CorrectionNotFound => write!(f, "correction not found"),
        }
    }
}

#[derive(Debug)]
pub enum MeshCoordErrorKind {
    PosOverflow,
    NegOverflow,
    Overflow,
    MeshUnit,
}

impl std::fmt::Display for MeshCoordErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::PosOverflow => write!(f, "number too large to fit in MeshCoord"),
            Self::NegOverflow => write!(f, "number too large to fit in MeshCoord"),
            Self::Overflow => write!(f, "number too large to fit in the first of MeshCoord"),
            Self::MeshUnit => write!(f, "inconsistent mesh_unit with coords"),
        }
    }
}

#[derive(Debug)]
pub enum MeshNodeErrorKind {
    Overflow,
}

impl std::fmt::Display for MeshNodeErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Overflow => write!(f, "number too large to fit in MeshNode"),
        }
    }
}

#[derive(Debug)]
pub enum MeshCellErrorKind {
    Overflow,
    MeshUnit,
    NorthWestNode,
    SouthEastNode,
    NorthEastNode,
}

impl std::fmt::Display for MeshCellErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Overflow => {
                write!(f, "south-west node too large to find north/east next node")
            }
            Self::MeshUnit => write!(f, "inconsistent mesh_unit with nodes"),
            Self::NorthWestNode => write!(
                f,
                "inconsistent north-west node with south-west node and mesh_unit"
            ),
            Self::SouthEastNode => write!(
                f,
                "inconsistent south-east node with south-west node and mesh_unit"
            ),
            Self::NorthEastNode => write!(
                f,
                "inconsistent north-east node with south-west node and mesh_unit"
            ),
        }
    }
}

#[derive(Debug)]
pub enum DMSErrorKind {
    Overflow,
    NAN,
}

impl std::fmt::Display for DMSErrorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Overflow => write!(f, "number too large to fit in DMS"),
            Self::NAN => write!(f, "number would be NAN"),
        }
    }
}
