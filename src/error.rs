use std::error;
use std::fmt::{self, Display, Formatter};

#[derive(Debug, Clone, PartialEq)]
pub enum Error {
    ParseError(String),
    NameError(String),
}

impl Display for Error {
    fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
        match *self {
            Error::ParseError(ref message) => write!(fmt, "ParseError: {}", message),
            Error::NameError(ref message) => write!(fmt, "NameError: {}", message),
        }
    }
}

impl error::Error for Error {
    fn description(&self) -> &str {
        match *self {
            Error::ParseError(ref message) => message,
            Error::NameError(ref message) => message,
        }
    }

    fn cause(&self) -> Option<&error::Error> {
        match *self {
            Error::ParseError(_) => None,
            Error::NameError(_) => None,
        }
    }
}
