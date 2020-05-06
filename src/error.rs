#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Error {
    OutOfRange,
    ParseInt,
    InvalidString,
    InvalidChar(char),
}
