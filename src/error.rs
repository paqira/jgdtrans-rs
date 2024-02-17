use crate::mesh::{MeshCoord, MeshNode, MeshUnit};

/// Alias for a `Result<T, jgdtrans::error::Error>`.
pub type Result<T> = std::result::Result<T, Error>;

/// Represents all possible errors that can occur by this crate.
#[derive(Debug)]
pub struct Error {
    pub err: Box<ErrorImpl>,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.err)
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }
}

impl Error {
    /// Returns a error kind.
    pub fn kind(&self) -> &ErrorImpl {
        &self.err
    }
}

impl Error {
    pub(crate) fn new_parse_par(
        start: usize,
        end: usize,
        lineno: usize,
        kind: ParseParErrorImpl,
    ) -> Self {
        Self {
            err: Box::new(ErrorImpl::ParseParError {
                kind,
                lineno,
                start,
                end,
            }),
        }
    }

    pub(crate) fn new_out_of_range_meshcode(code: u32) -> Self {
        Self {
            err: Box::new(ErrorImpl::OutOfRangeMeshcode { value: code }),
        }
    }

    pub(crate) fn new_incosistent_mesh_unit(coord: MeshCoord, unit: MeshUnit) -> Self {
        Self {
            err: Box::new(ErrorImpl::IncosistentMeshUnit { unit, coord }),
        }
    }

    pub(crate) fn new_incosistent_mesh_cell(a: MeshNode, b: MeshNode, unit: MeshUnit) -> Self {
        Self {
            err: Box::new(ErrorImpl::IncosistentMeshCell { a, b, unit }),
        }
    }

    pub(crate) fn new_parameter_not_found(kind: ParameterNotFoundKind, meshcode: u32) -> Self {
        Self {
            err: Box::new(ErrorImpl::ParameterNotFound { kind, meshcode }),
        }
    }

    pub(crate) fn new_parse_dms_error(s: String) -> Self {
        Self {
            err: Box::new(ErrorImpl::ParseDMSError { s }),
        }
    }
}

#[derive(Debug)]
pub enum ErrorImpl {
    /// Invalid data found in par-formatted data.
    ParseParError {
        /// Kind of component
        kind: ParseParErrorImpl,
        /// Line no. of the data
        lineno: usize,
        /// Start colum no. of the data
        start: usize,
        /// End colum no. of the data
        end: usize,
    },
    /// Invalid DMS.
    ParseDMSError {
        /// Invalid data
        s: String,
    },
    /// Invalid meshcode.
    ParseMeshcodeError {
        /// Invalid data
        s: String,
    },
    /// Parameter not found
    ParameterNotFound {
        /// The corner of the cell
        kind: ParameterNotFoundKind,
        //// The meshcode
        meshcode: u32,
    },
    /// Error is still high even iteration exhausted
    NotCovergent {
        /// Resulting latitude
        latitude: f64,
        /// Resulting longitude
        longitude: f64,
        /// Error cirteria
        criteria: f64,
        /// Max iteration
        iteration: usize,
    },
    MeshCoordOverFlow,
    IncosistentMeshUnit {
        coord: MeshCoord,
        unit: MeshUnit,
    },
    IncosistentMeshCell {
        a: MeshNode,
        b: MeshNode,
        unit: MeshUnit,
    },
    OutOfRangePosition {
        kind: OutOfRangePositionKind,
        low: f64,
        high: f64,
    },
    OutOfRangeMeshCoordDigit {
        kind: OutOfRangeMeshCoordDigitKind,
        low: u8,
        high: u8,
    },
    OutOfRangeMeshCorrd {
        value: MeshCoord,
        low: MeshCoord,
        high: MeshCoord,
    },
    OutOfRangeMeshcode {
        value: u32,
    },
    OutOfRangeDMS {
        degree: u8,
        minute: u8,
        second: u8,
        fract: f64,
    },
    OutOfRangeDegree {
        degree: f64,
        low: f64,
        high: f64,
    },
}

#[derive(Debug)]
pub enum ParseParErrorImpl {
    Meshcode,
    Latitude,
    Longitude,
    Altitude,
}

impl std::fmt::Display for ParseParErrorImpl {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let s = match self {
            ParseParErrorImpl::Meshcode => "meshcode",
            ParseParErrorImpl::Latitude => "latitude",
            ParseParErrorImpl::Longitude => "longitude",
            ParseParErrorImpl::Altitude => "altitude",
        };
        f.write_str(s)
    }
}

#[derive(Debug)]
pub enum ParameterNotFoundKind {
    SouthWest,
    SouthEast,
    NorthWest,
    NorthEast,
}

impl std::fmt::Display for ParameterNotFoundKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            ParameterNotFoundKind::SouthWest => "south-west",
            ParameterNotFoundKind::SouthEast => "south-east",
            ParameterNotFoundKind::NorthWest => "north-west",
            ParameterNotFoundKind::NorthEast => "north-east",
        };
        f.write_str(s)
    }
}

#[derive(Debug)]
pub enum OutOfRangePositionKind {
    Latitude,
    Longitude,
}

impl std::fmt::Display for OutOfRangePositionKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            OutOfRangePositionKind::Latitude => "latitude",
            OutOfRangePositionKind::Longitude => "longitude",
        };
        f.write_str(s)
    }
}

#[derive(Debug)]
pub enum OutOfRangeMeshCoordDigitKind {
    First,
    Second,
    Third,
}

impl std::fmt::Display for OutOfRangeMeshCoordDigitKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            OutOfRangeMeshCoordDigitKind::First => "first",
            OutOfRangeMeshCoordDigitKind::Second => "second",
            OutOfRangeMeshCoordDigitKind::Third => "third",
        };
        f.write_str(s)
    }
}

impl std::fmt::Display for ErrorImpl {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            ErrorImpl::ParseParError {
                kind,
                lineno,
                start,
                end,
            } => write!(f, "invalid {kind}: line {lineno:?}, {start:?} to {end:?}",),
            ErrorImpl::ParseDMSError { s } => write!(f, "invalid DMS: '{s}'",),
            ErrorImpl::ParseMeshcodeError { s } => write!(f, "invalid meshcode: '{s}'",),
            ErrorImpl::ParameterNotFound { meshcode, kind } => {
                write!(f, "parameter not found: {meshcode:?} ({kind:?} corner)",)
            }
            ErrorImpl::NotCovergent {
                iteration,
                criteria,
                ..
            } => write!(
                f,
                "error is still higher than {criteria:?} even exhaust {iteration:?} iterations"
            ),
            ErrorImpl::MeshCoordOverFlow => write!(f, "MeshCoord over flow"),
            ErrorImpl::IncosistentMeshUnit { unit, .. } => {
                write!(f, "invalid unit: {unit:?} is incosistent with MeshCoord")
            }
            ErrorImpl::IncosistentMeshCell { unit, .. } => {
                write!(
                    f,
                    "invalid MeshCell: nodes not construct a unit cell in unit {unit:?}"
                )
            }
            ErrorImpl::OutOfRangePosition { kind, low, high } => {
                write!(f, "invalid {kind}: must satisfy {low:?} <= and <= {high:?}")
            }
            ErrorImpl::OutOfRangeMeshCoordDigit { kind, low, high } => {
                write!(
                    f,
                    "invalid MeshCoord: {kind} digit must satisfy {low:?} <= and <= {high:?}"
                )
            }
            ErrorImpl::OutOfRangeMeshCorrd { low, high, .. } => write!(
                f,
                "invalid MeshCoord: must satisfy {low:?} <= and <= {high:?}"
            ),
            ErrorImpl::OutOfRangeMeshcode { value } => {
                write!(f, "invalid meshcode: {}", value)
            }
            ErrorImpl::OutOfRangeDMS { .. } => write!(f, "invalid DMS"),
            ErrorImpl::OutOfRangeDegree { low, high, .. } => write!(
                f,
                "invalid degree: must satisfiy {low:?} <= and <= {high:?}"
            ),
        }
    }
}
