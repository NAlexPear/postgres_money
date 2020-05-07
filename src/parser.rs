use regex::{Match, Regex};

pub use crate::error::Error;

use crate::Money;
use std::str::Chars;

impl Money {
    pub fn parse_str(input: &str) -> Result<Money, Error> {
        parse_en_us_utf8(input)
    }

    pub fn from(cents: i64) -> Money {
        Money(cents)
    }
}

trait ParseInner {
    fn parse_inner(parseable: &str) -> Result<i64, Error>;
}

fn parse_en_us_utf8(input: &str) -> Result<Money, Error> {
    Amount::parse_inner(input).map(|inner| Money(inner))
}

#[derive(Clone, Copy, Debug)]
enum Sign {
    Minus,
    ParenOpen,
    ParenClose,
    Plus,
}

impl Sign {
    fn to_int(&self) -> i8 {
        match self {
            Sign::Minus| Sign::ParenOpen | Sign::ParenClose => -1,
            Sign::Plus => 1
        }
    }
}

#[derive(Debug)]
struct EnUsUtf8Parser {
    repr: String,
    decimals: Option<i8>,
    sign: Option<Sign>,
    seen_currency: bool,
}

impl EnUsUtf8Parser {
    fn new() -> Self {
        Self {
            repr: "0".to_string(),
            sign: None,
            decimals: None,
            seen_currency: false,
        }
    }

    // Get a consistent repr string accounting for decimals
    fn apply_decimals(&mut self) -> Self {
        let pad_to_add = 3 - self.decimals.unwrap_or(0) as usize;
        self.repr.push_str(&"0".repeat(pad_to_add));
        Self {
            repr: self.repr,
            decimals: Some(3),
            seen_currency: &self.seen_currency,
            sign: self.sign,
        }
    }

    fn to_i64(&self) -> Result<i64, Error> {
        let mut new = self.apply_decimals();
        println!("repr b4: {:?}", new.repr);
        let t = new.repr.pop().unwrap();
        println!("oh mah {:?}", t);
        println!("repr after: {:?}", new.repr);

        str::parse::<i64>(&new.repr)
            .map_err(|_| Error::InvalidString)
            .map(|i| i + t.to_digit(10).unwrap() as i64)
        // str::parse::<i64>(&self.repr)
        //     .map(|i| i + self.rounding_int())
        //     .map_err(|_| Error::InvalidString)

        // Ok(5)
    }

    fn parse(s: &str) -> Result<Self, Error> {
        fn num_handler(mut acc: EnUsUtf8Parser, c: char) -> Result<EnUsUtf8Parser, Error> {
            if acc.decimals.is_some() {
                acc.decimals = acc.decimals.map(|s| s + 1);
            }
            acc.repr.push(c);
            Ok(acc)
        }

        fn dec_handler(mut acc: EnUsUtf8Parser, c: char) -> Result<EnUsUtf8Parser, Error> {
            if acc.decimals.is_none() {
                acc.decimals = Some(0);
                Ok(acc)
            } else {
                Err(Error::InvalidChar(c))
            }
        }

        fn currency_handler(mut acc: EnUsUtf8Parser, c: char) -> Result<EnUsUtf8Parser, Error> {
            if acc.seen_currency {
                Err(Error::InvalidChar(c))
            } else {
                acc.seen_currency = true;
                Ok(acc)
            }
        }

        fn sign_handler(mut acc: EnUsUtf8Parser, c: char) -> Result<EnUsUtf8Parser, Error> {
            if acc.sign.is_some() {
                Err(Error::InvalidChar(c))
            } else {
                acc.sign = match c {
                    '-' => Some(Sign::Minus),
                    '(' => Some(Sign::ParenOpen),
                    '+' => Some(Sign::Plus),
                    _ => return Err(Error::InvalidChar(c))
                };
                Ok(acc)
            }
        }

        fn closed_paren_handler(acc: EnUsUtf8Parser, c: char) -> Result<EnUsUtf8Parser, Error> {
            match acc.sign {
                Some(Sign::ParenOpen) => Ok(acc),
                _ => Err(Error::InvalidChar(c)),
            }
        }

        fn handle_some(acc: EnUsUtf8Parser, c: char) -> Result<EnUsUtf8Parser, Error> {
            if let Some(Sign::ParenClose) = acc.sign {
                return Err(Error::InvalidChar(c));
            }

            match c {
                '0'..='9' => num_handler(acc, c),
                '.' => dec_handler(acc, c),
                '$' => currency_handler(acc, c),
                '-' | '(' | '+' => sign_handler(acc, c),
                ')' => closed_paren_handler(acc, c),
                _ => Err(Error::InvalidChar(c)),
            }
        }

        fn reduce(acc: EnUsUtf8Parser, mut it: Chars) -> Result<EnUsUtf8Parser, Error> {
            let new_acc = match it.next() {
                Some(c) => handle_some(acc, c),
                None => return Ok(acc)
            }?;

            reduce(new_acc, it)
        }

        reduce(EnUsUtf8Parser::new(), s.chars())
    }
}

#[test]
fn tkb2() {
    println!("{:?}", Some(3) < None);

    // println!("{:?}", EnUsUtf8Parser::parse("00.01"));
    // println!("{:?}", EnUsUtf8Parser::parse("0.01"));
    // println!("{:?}", EnUsUtf8Parser::parse(".01"));
    // println!("{:?}", EnUsUtf8Parser::parse("00.05"));
    // println!("{:?}", EnUsUtf8Parser::parse("00.10"));
    // println!("{:?}", EnUsUtf8Parser::parse("00.01"));
    // println!("{:?}", EnUsUtf8Parser::parse("$123.45"));
    // println!("{:?}", EnUsUtf8Parser::parse("$123.451"));
    // println!("{:?}", EnUsUtf8Parser::parse("$123.454"));
    // println!("{:?}", EnUsUtf8Parser::parse("$123.455"));
    // println!("{:?}", EnUsUtf8Parser::parse("$123.456"));
    // println!("{:?}", EnUsUtf8Parser::parse("$123.459"));
    println!("{:?}", EnUsUtf8Parser::parse("1234567890").map(|r| r.apply_decimals()));
    println!("{:?}", EnUsUtf8Parser::parse("1234567890.").map(|r| r.apply_decimals()));
    println!("{:?}", EnUsUtf8Parser::parse("1234567890.1").map(|r| r.apply_decimals()));
    println!("{:?}", EnUsUtf8Parser::parse("1234567890.12").map(|r| r.apply_decimals()));
    println!("{:?}", EnUsUtf8Parser::parse("1234567890.123").map(|r| r.apply_decimals()));

    println!("{:?}", EnUsUtf8Parser::parse("1234567890.123").unwrap().to_i64());
    // println!("{:?}", EnUsUtf8Parser::parse("-00.01"));
    // println!("{:?}", EnUsUtf8Parser::parse("-0.01"));
    // println!("{:?}", EnUsUtf8Parser::parse("-.01"));
    // println!("{:?}", EnUsUtf8Parser::parse("-00.05"));
    // println!("{:?}", EnUsUtf8Parser::parse("-00.10"));
    // println!("{:?}", EnUsUtf8Parser::parse("-00.01"));
    // println!("{:?}", EnUsUtf8Parser::parse("-$123.45"));
    // println!("{:?}", EnUsUtf8Parser::parse("-$123.451"));
    // println!("{:?}", EnUsUtf8Parser::parse("-$123.454"));
    // println!("{:?}", EnUsUtf8Parser::parse("-$123.455"));
    // println!("{:?}", EnUsUtf8Parser::parse("-$123.456"));
    // println!("{:?}", EnUsUtf8Parser::parse("-$123.459"));
    // println!("{:?}", EnUsUtf8Parser::parse("-1234567890"));
}

impl ParseInner for EnUsUtf8Parser {
    fn parse_inner(s: &str) -> Result<i64, Error> {
        Ok(5)
    }
}

// #[test]
// fn tkb() {
//     // println!("{:?}", Sign::Neg.to_int());
//     // println!("{:?}", Sign::Neg as i8);
//     //
//     // println!("{:?}", Sign::Pos.to_int());
//     // println!("{:?}", Sign::Pos as i8);
//     //
//     // println!("{:?}", str::parse::<i64>(""));
//     // println!("{:?}", str::parse::<i64>("00000000000000000000000000000000000000000000000000000000000000000000000000000000000008"));
//
//     println!("{:?}", '9'.to_digit(16));
//
//     println!("{:?}", EnUsUtf8Parser::parse_inner("hi"));
// }

#[derive(Clone, Eq, Hash, Ord, PartialEq, PartialOrd, Debug)]
enum AmountKind {
    Negative,
    Positive,
}

#[derive(Clone, Eq, Hash, Ord, PartialEq, PartialOrd, Debug)]
struct Amount {
    kind: AmountKind,
    dollars: String,
    cents: String,
}

impl Amount {
    fn new(kind: AmountKind, inner: &str) -> Result<Self, Error> {
        let caps = Self::valid_inner()
            .captures(inner)
            .ok_or(Error::InvalidString)?;

        if caps.len() != 3 {
            return Err(Error::InvalidString);
        }

        Ok(Amount {
            kind,
            dollars: Self::mk_string(caps.get(1)).replace(",", ""),
            cents: Self::mk_string(caps.get(2)),
        })
    }

    fn positive(s: &str) -> Result<Amount, Error> {
        Self::new(AmountKind::Positive, s)
    }

    fn negative(s: &str) -> Result<Amount, Error> {
        Self::new(AmountKind::Negative, s)
    }

    fn valid_inner() -> Regex {
        Regex::new(r"^\$?(?P<dollars>[\d,]*)\.?(?P<cents>\d*$)").unwrap()
    }

    fn mk_string(m: Option<Match>) -> String {
        m.map_or("", |m| m.as_str()).to_string()
    }

    fn apply_sign(&self) -> i64 {
        return if &self.kind == &AmountKind::Negative {
            -1
        } else {
            1
        };
    }

    fn combine_dollars_and_cents(&self) -> Result<i64, Error> {
        let dollars = mk_int(&self.dollars)? * self.apply_sign();
        let cents = mk_rounded_cents(&self.cents)? * self.apply_sign();

        dollars
            .checked_mul(100)
            .ok_or(Error::OutOfRange)?
            .checked_add(cents)
            .ok_or(Error::OutOfRange)
    }

    fn from(s: &str) -> Result<Self, Error> {
        let has_minus = Regex::new(r"-(.*)").unwrap();
        let has_paren = Regex::new(r"\((.*)\)").unwrap();

        let m: Vec<Regex> = vec![has_minus, has_paren]
            .into_iter()
            .filter(|r| r.is_match(s))
            .collect();

        return match m.len() {
            0 => Self::positive(s),
            1 => {
                let transformed = m
                    .into_iter()
                    .fold(s, |s, r| r.captures(s).unwrap().get(1).unwrap().as_str());
                Self::negative(transformed)
            }
            _ => Err(Error::InvalidString),
        };
    }
}

impl ParseInner for Amount {
    fn parse_inner(parseable: &str) -> Result<i64, Error> {
        Self::from(parseable)?.combine_dollars_and_cents()
    }
}

fn mk_rounded_cents(s: &String) -> Result<i64, Error> {
    return if s.len() > 2 {
        round_cents(s)
    } else {
        mk_int(s)
    };
}

fn round_cents(s: &String) -> Result<i64, Error> {
    let s = &s[..3];
    let (s1, s2) = s.split_at(s.len() - 1);
    let (i1, i2) = (mk_int(s1)?, mk_int(s2)?);
    if i2 >= 5 {
        Ok(i1 + 1)
    } else {
        Ok(i1)
    }
}

fn mk_int(s: &str) -> Result<i64, Error> {
    if s.is_empty() {
        return Ok(0);
    }

    str::parse::<i64>(&s).map_err(|e| {
        // This is a janky workaround until ParseIntError.kind() is stable
        match e.to_string().find("too large") {
            Some(_) => Error::OutOfRange,
            None => Error::ParseInt,
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    // Money::parse_str
    #[test]
    fn test_valid_123_45() {
        assert_eq!(Money::parse_str("$123.45"), Ok(Money(12345)))
    }

    #[test]
    fn test_valid_123_451() {
        assert_eq!(Money::parse_str("$123.451"), Ok(Money(12345)))
    }

    #[test]
    fn test_valid_123_454() {
        assert_eq!(Money::parse_str("$123.454"), Ok(Money(12345)))
    }

    #[test]
    fn test_valid_123_455() {
        assert_eq!(Money::parse_str("$123.455"), Ok(Money(12346)))
    }

    #[test]
    fn test_valid_123_456() {
        assert_eq!(Money::parse_str("$123.456"), Ok(Money(12346)))
    }

    #[test]
    fn test_valid_123_459() {
        assert_eq!(Money::parse_str("$123.459"), Ok(Money(12346)))
    }

    #[test]
    fn test_valid_1234567890() {
        assert_eq!(Money::parse_str("1234567890"), Ok(Money(123456789000)))
    }

    #[test]
    fn test_valid_12345678901234567() {
        assert_eq!(
            Money::parse_str("12345678901234567"),
            Ok(Money(1234567890123456700))
        )
    }

    #[test]
    fn test_invalid_123456789012345678() {
        assert_eq!(
            Money::parse_str("123456789012345678"),
            Err(Error::OutOfRange)
        )
    }

    #[test]
    fn test_invalid_9223372036854775807() {
        assert_eq!(
            Money::parse_str("9223372036854775807"),
            Err(Error::OutOfRange)
        )
    }

    #[test]
    fn test_valid_neg_12345() {
        assert_eq!(Money::parse_str("-12345"), Ok(Money(-1234500)))
    }

    #[test]
    fn test_valid_neg_1234567890() {
        assert_eq!(Money::parse_str("-1234567890"), Ok(Money(-123456789000)))
    }

    #[test]
    fn test_valid_neg_12345678901234567() {
        assert_eq!(
            Money::parse_str("-12345678901234567"),
            Ok(Money(-1234567890123456700))
        )
    }

    #[test]
    fn test_invalid_neg_123456789012345678() {
        assert_eq!(
            Money::parse_str("-123456789012345678"),
            Err(Error::OutOfRange)
        )
    }

    #[test]
    fn test_invalid_neg_9223372036854775808() {
        assert_eq!(
            Money::parse_str("-9223372036854775808"),
            Err(Error::OutOfRange)
        )
    }

    #[test]
    fn test_valid_paren_1() {
        assert_eq!(Money::parse_str("(1)"), Ok(Money(-100)))
    }

    #[test]
    fn test_valid_paren_123456_78() {
        assert_eq!(Money::parse_str("($123,456.78)"), Ok(Money(-12345678)))
    }

    #[test]
    fn test_valid_min() {
        assert_eq!(Money::parse_str("-92233720368547758.08"), Ok(Money::min()))
    }

    #[test]
    fn test_valid_max() {
        assert_eq!(Money::parse_str("92233720368547758.07"), Ok(Money::max()))
    }

    #[test]
    fn test_invalid_min() {
        assert_eq!(
            Money::parse_str("-92233720368547758.085"),
            Err(Error::OutOfRange)
        )
    }

    #[test]
    fn test_invalid_max() {
        assert_eq!(
            Money::parse_str("92233720368547758.075"),
            Err(Error::OutOfRange)
        )
    }

    // Money Ops

    // TODO: int parsing
    #[test]
    fn test_valid_123_45_int() {
        assert_eq!(Money::from(12345), Money(12345))
    }

    #[test]
    fn test_valid_123_451_int() {
        assert_eq!(Money::from(123451), Money(123451))
    }

    #[test]
    fn test_valid_123_454_int() {
        assert_eq!(Money::from(123454), Money(123454))
    }

    #[test]
    fn test_valid_1234567890_int() {
        assert_eq!(Money::from(1234567890), Money(1234567890))
    }

    #[test]
    fn test_valid_12345678901234567_int() {
        assert_eq!(Money::from(12345678901234567), Money(12345678901234567))
    }

    #[test]
    fn test_valid_neg_12345678901234567_int() {
        assert_eq!(Money::from(-12345678901234567), Money(-12345678901234567))
    }

    #[test]
    fn test_valid_neg_123456_78_int() {
        assert_eq!(Money::from(-12345678), Money(-12345678))
    }
}
