//! `parse-size` is an accurate, customizable, allocation-free library for
//! parsing byte size into integer.
//!
//! ```rust
//! use parse_size::parse_size;
//!
//! assert_eq!(parse_size("0.2 MiB"), Ok(209715));
//! assert_eq!(parse_size("14.2e+8"), Ok(14_2000_0000));
//! ```
//!
//! # Features
//!
//! Supports both binary and decimal based prefix up to exabytes.
//!
//! ```rust
//! # use parse_size::parse_size;
//! assert_eq!(parse_size("1 B"), Ok(1));
//! assert_eq!(parse_size("1 KiB"), Ok(1 << 10));
//! assert_eq!(parse_size("1 MiB"), Ok(1 << 20));
//! assert_eq!(parse_size("1 GiB"), Ok(1 << 30));
//! assert_eq!(parse_size("1 TiB"), Ok(1 << 40));
//! assert_eq!(parse_size("1 PiB"), Ok(1 << 50));
//! assert_eq!(parse_size("1 EiB"), Ok(1 << 60));
//! assert_eq!(parse_size("1 KB"), Ok(1_000));
//! assert_eq!(parse_size("1 MB"), Ok(1_000_000));
//! assert_eq!(parse_size("1 GB"), Ok(1_000_000_000));
//! assert_eq!(parse_size("1 TB"), Ok(1_000_000_000_000));
//! assert_eq!(parse_size("1 PB"), Ok(1_000_000_000_000_000));
//! assert_eq!(parse_size("1 EB"), Ok(1_000_000_000_000_000_000));
//! ```
//!
//! Numbers can be fractional and/or in scientific notation.
//! `parse-size` can accurately parse the input using the full 64-bit precision.
//!
//! ```rust
//! # use parse_size::parse_size;
//! assert_eq!(parse_size("2.999999999999999999e18"), Ok(2999999999999999999));
//! assert_eq!(parse_size("3.000000000000000001 EB"), Ok(3000000000000000001));
//! ```
//!
//! The unit is case-insensitive. The "B" suffix is also optional.
//!
//! ```rust
//! # use parse_size::parse_size;
//! assert_eq!(parse_size("5gb"), Ok(5_000_000_000));
//! assert_eq!(parse_size("2ki"), Ok(2048));
//! ```
//!
//! Fractional bytes are allowed, and rounded to nearest integer.
//!
//! ```rust
//! # use parse_size::parse_size;
//! assert_eq!(parse_size("0.333333 KB"), Ok(333));
//! assert_eq!(parse_size("2.666666 KB"), Ok(2667));
//! ```
//!
//! Underscores and spaces in the numbers are ignored to support digit grouping.
//!
//! ```rust
//! # use parse_size::parse_size;
//! assert_eq!(parse_size(" 69_420_000"), Ok(69_420_000));
//! ```
//!
//! Conventional units (KB, GB, ...) can be configured to use the binary system.
//!
//! ```rust
//! use parse_size::Config;
//!
//! let cfg = Config::new().with_binary();
//! assert_eq!(cfg.parse_size("1 KB"), Ok(1024));
//! assert_eq!(cfg.parse_size("1 KiB"), Ok(1024));
//! assert_eq!(cfg.parse_size("1 MB"), Ok(1048576));
//! assert_eq!(cfg.parse_size("1 MiB"), Ok(1048576));
//! ```
//!
//! # Integration examples
//!
//! Use with `clap` v4:
//!
//! ```rust
//! use clap::Parser;
//! use parse_size::parse_size;
//!
//! #[derive(Parser)]
//! pub struct Opt {
//      // FIXME: we need a closure because of https://github.com/clap-rs/clap/issues/4939
//!     #[arg(long, value_parser = |s: &str| parse_size(s))]
//!     pub size: u64,
//! }
//!
//! let opt = Opt::parse_from(&["./app", "--size", "2.5 K"]);
//! assert_eq!(opt.size, 2500);
//! ```

#![no_std]

use core::{convert::TryFrom, fmt, num::IntErrorKind};

/// The system to use when parsing prefixes like "KB" and "GB".
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum UnitSystem {
    /// Use powers of 1000 for prefixes. Parsing "1 KB" returns 1000.
    Decimal,
    /// Use powers of 1024 for prefixes. Parsing "1 KB" returns 1024.
    Binary,
}

impl UnitSystem {
    /// Obtains the power factor for the given prefix character.
    ///
    /// Returns None if the input is not a valid prefix.
    ///
    /// The only valid prefixes are K, M, G, T, P and E. The higher powers Z and
    /// Y exceed the `u64` range and thus considered invalid.
    fn factor(self, prefix: u8) -> Option<u64> {
        Some(match (self, prefix) {
            (Self::Decimal, b'k' | b'K') => 1_000,
            (Self::Decimal, b'm' | b'M') => 1_000_000,
            (Self::Decimal, b'g' | b'G') => 1_000_000_000,
            (Self::Decimal, b't' | b'T') => 1_000_000_000_000,
            (Self::Decimal, b'p' | b'P') => 1_000_000_000_000_000,
            (Self::Decimal, b'e' | b'E') => 1_000_000_000_000_000_000,
            (Self::Binary, b'k' | b'K') => 1_u64 << 10,
            (Self::Binary, b'm' | b'M') => 1_u64 << 20,
            (Self::Binary, b'g' | b'G') => 1_u64 << 30,
            (Self::Binary, b't' | b'T') => 1_u64 << 40,
            (Self::Binary, b'p' | b'P') => 1_u64 << 50,
            (Self::Binary, b'e' | b'E') => 1_u64 << 60,
            _ => return None,
        })
    }
}

/// How to deal with the "B" suffix.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum ByteSuffix {
    /// The "B" suffix must never appear. Parsing a string with the "B" suffix
    /// causes [`Error::InvalidDigit`] error.
    Deny,
    /// The "B" suffix is optional.
    Allow,
    /// The "B" suffix is required. Parsing a string without the "B" suffix
    /// causes [`Error::InvalidDigit`] error.
    Require,
}

/// Configuration of the parser.
#[derive(Clone, Debug)]
pub struct Config {
    unit_system: UnitSystem,
    default_factor: u64,
    byte_suffix: ByteSuffix,
}

impl Config {
    /// Creates a new parser configuration.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            unit_system: UnitSystem::Decimal,
            default_factor: 1,
            byte_suffix: ByteSuffix::Allow,
        }
    }

    /// Changes the configuration's unit system.
    ///
    /// The default system is decimal (powers of 1000).
    #[must_use]
    pub const fn with_unit_system(mut self, unit_system: UnitSystem) -> Self {
        self.unit_system = unit_system;
        self
    }

    /// Changes the configuration to use the binary unit system, which are
    /// defined to be powers of 1024.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use parse_size::Config;
    ///
    /// let cfg = Config::new().with_binary();
    /// assert_eq!(cfg.parse_size("1 KB"), Ok(1024));
    /// assert_eq!(cfg.parse_size("1 KiB"), Ok(1024));
    /// assert_eq!(cfg.parse_size("1 MB"), Ok(1048576));
    /// assert_eq!(cfg.parse_size("1 MiB"), Ok(1048576));
    /// ```
    #[must_use]
    pub const fn with_binary(self) -> Self {
        self.with_unit_system(UnitSystem::Binary)
    }

    /// Changes the configuration to use the decimal unit system, which are
    /// defined to be powers of 1000. This is the default setting.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use parse_size::Config;
    ///
    /// let cfg = Config::new().with_decimal();
    /// assert_eq!(cfg.parse_size("1 KB"), Ok(1000));
    /// assert_eq!(cfg.parse_size("1 KiB"), Ok(1024));
    /// assert_eq!(cfg.parse_size("1 MB"), Ok(1000000));
    /// assert_eq!(cfg.parse_size("1 MiB"), Ok(1048576));
    /// ```
    #[must_use]
    pub const fn with_decimal(self) -> Self {
        self.with_unit_system(UnitSystem::Decimal)
    }

    /// Changes the default factor when a byte unit is not provided.
    ///
    /// This is useful for keeping backward compatibility when migrating from an
    /// old user interface expecting non-byte input.
    ///
    /// The default value is 1.
    ///
    /// # Examples
    ///
    /// If the input is a pure number, we treat that as mebibytes.
    ///
    /// ```rust
    /// use parse_size::Config;
    ///
    /// let cfg = Config::new().with_default_factor(1048576);
    /// assert_eq!(cfg.parse_size("10"), Ok(10485760));
    /// assert_eq!(cfg.parse_size("0.5"), Ok(524288));
    /// assert_eq!(cfg.parse_size("128 B"), Ok(128)); // explicit units overrides the default
    /// assert_eq!(cfg.parse_size("16 KiB"), Ok(16384));
    /// ```
    #[must_use]
    pub const fn with_default_factor(mut self, factor: u64) -> Self {
        self.default_factor = factor;
        self
    }

    /// Changes the handling of the "B" suffix.
    ///
    /// Normally, the character "B" at the end of the input is optional. This
    /// can be changed to deny or require such suffix.
    ///
    /// Power prefixes (K, Ki, M, Mi, ...) are not affected.
    ///
    /// # Examples
    ///
    /// Deny the suffix.
    ///
    /// ```rust
    /// use parse_size::{ByteSuffix, Config, Error};
    ///
    /// let cfg = Config::new().with_byte_suffix(ByteSuffix::Deny);
    /// assert_eq!(cfg.parse_size("123"), Ok(123));
    /// assert_eq!(cfg.parse_size("123k"), Ok(123000));
    /// assert_eq!(cfg.parse_size("123B"), Err(Error::InvalidDigit));
    /// assert_eq!(cfg.parse_size("123KB"), Err(Error::InvalidDigit));
    /// ```
    ///
    /// Require the suffix.
    ///
    /// ```rust
    /// use parse_size::{ByteSuffix, Config, Error};
    ///
    /// let cfg = Config::new().with_byte_suffix(ByteSuffix::Require);
    /// assert_eq!(cfg.parse_size("123"), Err(Error::InvalidDigit));
    /// assert_eq!(cfg.parse_size("123k"), Err(Error::InvalidDigit));
    /// assert_eq!(cfg.parse_size("123B"), Ok(123));
    /// assert_eq!(cfg.parse_size("123KB"), Ok(123000));
    /// ```
    #[must_use]
    pub const fn with_byte_suffix(mut self, byte_suffix: ByteSuffix) -> Self {
        self.byte_suffix = byte_suffix;
        self
    }

    /// Parses the string input into the number of bytes it represents.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use parse_size::{Config, Error};
    ///
    /// let cfg = Config::new().with_binary();
    /// assert_eq!(cfg.parse_size("10 KB"), Ok(10240));
    /// assert_eq!(cfg.parse_size("20000"), Ok(20000));
    /// assert_eq!(cfg.parse_size("^_^"), Err(Error::InvalidDigit));
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an [`Error`] if the input has invalid digits or the result
    /// exceeded 2<sup>64</sup>−1.
    pub fn parse_size<T: AsRef<[u8]>>(&self, src: T) -> Result<u64, Error> {
        self.parse_size_inner(src.as_ref())
    }
}

impl Default for Config {
    fn default() -> Self {
        Self::new()
    }
}

/// The error returned when parse failed.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub enum Error {
    /// The input contains no numbers.
    Empty,
    /// An invalid character is encountered while parsing.
    InvalidDigit,
    /// The resulting number is too large to fit into a `u64`.
    PosOverflow,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Empty => "cannot parse integer from empty string",
            Self::InvalidDigit => "invalid digit found in string",
            Self::PosOverflow => "number too large to fit in target type",
        })
    }
}

impl core::error::Error for Error {}

impl From<Error> for IntErrorKind {
    fn from(e: Error) -> Self {
        match e {
            Error::Empty => Self::Empty,
            Error::InvalidDigit => Self::InvalidDigit,
            Error::PosOverflow => Self::PosOverflow,
        }
    }
}

/// Parses the string input into the number of bytes it represents using the
/// default configuration.
///
/// Equivalent to calling [`Config::parse_size()`] with the default
/// configuration ([`Config::new()`]).
///
/// # Examples
///
/// ```rust
/// use parse_size::{parse_size, Error};
///
/// assert_eq!(parse_size("10 KB"), Ok(10000));
/// assert_eq!(parse_size("20000"), Ok(20000));
/// assert_eq!(parse_size("0.2 MiB"), Ok(209715));
/// assert_eq!(parse_size("^_^"), Err(Error::InvalidDigit));
/// ```
///
/// # Errors
///
/// Returns an [`Error`] if the input has invalid digits or the result exceeded
/// 2<sup>64</sup>−1.
pub fn parse_size<T: AsRef<[u8]>>(src: T) -> Result<u64, Error> {
    Config::new().parse_size(src)
}

impl Config {
    fn parse_size_inner(&self, mut src: &[u8]) -> Result<u64, Error> {
        // if it ends with 'B' the default factor is always 1.
        let mut multiply = if let [init @ .., b'b' | b'B'] = src {
            if self.byte_suffix == ByteSuffix::Deny {
                return Err(Error::InvalidDigit);
            }
            src = init;
            1
        } else {
            if self.byte_suffix == ByteSuffix::Require {
                return Err(Error::InvalidDigit);
            }
            self.default_factor
        };

        // if it ends with an 'i' we always use binary prefix.
        let unit_system = if let [init @ .., b'i' | b'I'] = src {
            src = init;
            UnitSystem::Binary
        } else {
            self.unit_system
        };

        if let [init @ .., prefix] = src {
            if let Some(f) = unit_system.factor(*prefix) {
                multiply = f;
                src = init;
            }
        }

        parse_size_with_multiple(src, multiply)
    }
}

fn parse_size_with_multiple(src: &[u8], multiply: u64) -> Result<u64, Error> {
    #[derive(Copy, Clone, PartialEq)]
    enum Ps {
        Empty,
        Integer,
        IntegerOverflow,
        Fraction,
        FractionOverflow,
        PosExponent,
        NegExponent,
    }

    macro_rules! append_digit {
        ($before:expr, $method:ident, $digit_char:expr) => {
            $before
                .checked_mul(10)
                .and_then(|v| v.$method(($digit_char - b'0').into()))
        };
    }

    let mut mantissa = 0_u64;
    let mut fractional_exponent = 0;
    let mut exponent = 0_i32;
    let mut state = Ps::Empty;

    for b in src {
        match (state, *b) {
            (Ps::Integer | Ps::Empty, b'0'..=b'9') => {
                if let Some(m) = append_digit!(mantissa, checked_add, *b) {
                    mantissa = m;
                    state = Ps::Integer;
                } else {
                    if *b >= b'5' {
                        mantissa += 1;
                    }
                    state = Ps::IntegerOverflow;
                    fractional_exponent += 1;
                }
            }
            (Ps::IntegerOverflow, b'0'..=b'9') => {
                fractional_exponent += 1;
            }
            (Ps::Fraction, b'0'..=b'9') => {
                if let Some(m) = append_digit!(mantissa, checked_add, *b) {
                    mantissa = m;
                    fractional_exponent -= 1;
                } else {
                    if *b >= b'5' {
                        mantissa += 1;
                    }
                    state = Ps::FractionOverflow;
                }
            }
            (Ps::PosExponent, b'0'..=b'9') => {
                if let Some(e) = append_digit!(exponent, checked_add, *b) {
                    exponent = e;
                } else {
                    return Err(Error::PosOverflow);
                }
            }
            (Ps::NegExponent, b'0'..=b'9') => {
                if let Some(e) = append_digit!(exponent, checked_sub, *b) {
                    exponent = e;
                }
            }

            (_, b'_' | b' ') | (Ps::PosExponent, b'+') | (Ps::FractionOverflow, b'0'..=b'9') => {}
            (
                Ps::Integer | Ps::Fraction | Ps::IntegerOverflow | Ps::FractionOverflow,
                b'e' | b'E',
            ) => state = Ps::PosExponent,
            (Ps::PosExponent, b'-') => state = Ps::NegExponent,
            (Ps::Integer, b'.') => state = Ps::Fraction,
            (Ps::IntegerOverflow, b'.') => state = Ps::FractionOverflow,
            _ => return Err(Error::InvalidDigit),
        }
    }

    if state == Ps::Empty {
        return Err(Error::Empty);
    }

    let exponent = exponent.saturating_add(fractional_exponent);
    let abs_exponent = exponent.unsigned_abs();
    if exponent >= 0 {
        let power = 10_u64.checked_pow(abs_exponent).ok_or(Error::PosOverflow)?;
        let multiply = multiply.checked_mul(power).ok_or(Error::PosOverflow)?;
        mantissa.checked_mul(multiply).ok_or(Error::PosOverflow)
    } else if exponent >= -38 {
        let power = 10_u128.pow(abs_exponent);
        let result = (u128::from(mantissa) * u128::from(multiply) + power / 2) / power;
        u64::try_from(result).map_err(|_| Error::PosOverflow)
    } else {
        // (2^128) * 1e-39 < 1, always, and thus saturate to 0.
        Ok(0)
    }
}

#[test]
fn test_passes() {
    assert_eq!(parse_size("0"), Ok(0));
    assert_eq!(parse_size("3"), Ok(3));
    assert_eq!(parse_size("30"), Ok(30));
    assert_eq!(parse_size("32"), Ok(32));
    assert_eq!(parse_size("_5_"), Ok(5));
    assert_eq!(parse_size("1 234 567"), Ok(1_234_567));

    assert_eq!(
        parse_size("18_446_744_073_709_551_581"),
        Ok(18_446_744_073_709_551_581)
    );
    assert_eq!(
        parse_size("18_446_744_073_709_551_615"),
        Ok(18_446_744_073_709_551_615)
    );
    assert_eq!(
        parse_size("18_446_744_073_709_551_616"),
        Err(Error::PosOverflow)
    );
    assert_eq!(
        parse_size("18_446_744_073_709_551_620"),
        Err(Error::PosOverflow)
    );

    assert_eq!(parse_size("1kB"), Ok(1_000));
    assert_eq!(parse_size("2MB"), Ok(2_000_000));
    assert_eq!(parse_size("3GB"), Ok(3_000_000_000));
    assert_eq!(parse_size("4TB"), Ok(4_000_000_000_000));
    assert_eq!(parse_size("5PB"), Ok(5_000_000_000_000_000));
    assert_eq!(parse_size("6EB"), Ok(6_000_000_000_000_000_000));

    assert_eq!(parse_size("7 KiB"), Ok(7 << 10));
    assert_eq!(parse_size("8 MiB"), Ok(8 << 20));
    assert_eq!(parse_size("9 GiB"), Ok(9 << 30));
    assert_eq!(parse_size("10 TiB"), Ok(10 << 40));
    assert_eq!(parse_size("11 PiB"), Ok(11 << 50));
    assert_eq!(parse_size("12 EiB"), Ok(12 << 60));

    assert_eq!(parse_size("1mib"), Ok(1_048_576));

    assert_eq!(parse_size("5k"), Ok(5000));
    assert_eq!(parse_size("1.1 K"), Ok(1100));
    assert_eq!(parse_size("1.2345 K"), Ok(1235));
    assert_eq!(parse_size("1.2345m"), Ok(1_234_500));
    assert_eq!(parse_size("5.k"), Ok(5000));
    assert_eq!(parse_size("0.0025KB"), Ok(3));
    assert_eq!(
        parse_size("3.141_592_653_589_793_238e"),
        Ok(3_141_592_653_589_793_238)
    );

    assert_eq!(
        parse_size("18.446_744_073_709_551_615 EB"),
        Ok(18_446_744_073_709_551_615)
    );
    assert_eq!(
        parse_size("18.446_744_073_709_551_616 EB"),
        Err(Error::PosOverflow)
    );
    assert_eq!(
        parse_size("1.000_000_000_000_000_001 EB"),
        Ok(1_000_000_000_000_000_001)
    );

    assert_eq!(parse_size("1e2 KIB"), Ok(102_400));
    assert_eq!(parse_size("1E+6"), Ok(1_000_000));
    assert_eq!(parse_size("1e-4 MiB"), Ok(105));
    assert_eq!(parse_size("1.1e2"), Ok(110));
    assert_eq!(parse_size("5.7E3"), Ok(5700));

    assert_eq!(parse_size("20_000_000_000_000_000_000e-18"), Ok(20));
    assert_eq!(parse_size("98_765_432_109_876_543_210e-16"), Ok(9877));
    assert_eq!(parse_size("1e21"), Err(Error::PosOverflow));
    assert_eq!(parse_size("0.01e21"), Ok(10_000_000_000_000_000_000));
    assert_eq!(
        parse_size("3.333_333_333_333_333_333_333_333_333_333_333_333_333_333_333_333 EB"),
        Ok(3_333_333_333_333_333_333)
    );
    assert_eq!(parse_size("2e+0_9"), Ok(2_000_000_000));
    assert_eq!(
        parse_size("3e+66666666666666666666"),
        Err(Error::PosOverflow)
    );
    assert_eq!(parse_size("4e-77777777777777777777"), Ok(0));
    assert_eq!(parse_size("5e-88888888888888888888 EiB"), Ok(0));

    assert_eq!(
        parse_size("123_456_789_012_345_678_901_234_567.890e-16"),
        Ok(12_345_678_901)
    );
    assert_eq!(parse_size("0.1e-2147483648"), Ok(0));
    assert_eq!(parse_size("184467440737095516150e-38EiB"), Ok(2));
}

#[test]
fn test_parse_errors() {
    assert_eq!(parse_size(""), Err(Error::Empty));
    assert_eq!(parse_size("."), Err(Error::InvalidDigit));
    assert_eq!(parse_size(".5k"), Err(Error::InvalidDigit));
    assert_eq!(parse_size("k"), Err(Error::Empty));
    assert_eq!(parse_size("kb"), Err(Error::Empty));
    assert_eq!(parse_size("kib"), Err(Error::Empty));
    assert_eq!(parse_size("  "), Err(Error::Empty));
    assert_eq!(parse_size("__"), Err(Error::Empty));
    assert_eq!(parse_size("a"), Err(Error::InvalidDigit));
    assert_eq!(parse_size("-1"), Err(Error::InvalidDigit));
    assert_eq!(parse_size("1,5"), Err(Error::InvalidDigit));
    assert_eq!(parse_size("1e+f"), Err(Error::InvalidDigit));
    assert_eq!(parse_size("1e0.5"), Err(Error::InvalidDigit));
    assert_eq!(parse_size("1 ZiB"), Err(Error::InvalidDigit));
    assert_eq!(parse_size("1 YiB"), Err(Error::InvalidDigit));
}

#[test]
fn test_config() {
    let cfg = Config::new().with_binary().with_default_factor(1_048_576);
    assert_eq!(cfg.parse_size("3.5"), Ok(3_670_016));
    assert_eq!(cfg.parse_size("35 B"), Ok(35));
    assert_eq!(cfg.parse_size("5K"), Ok(5120));
    assert_eq!(cfg.parse_size("1.7e13"), Ok(17_825_792_000_000_000_000));
    assert_eq!(cfg.parse_size("1.8e13"), Err(Error::PosOverflow));
    assert_eq!(cfg.parse_size("1.8e18"), Err(Error::PosOverflow));

    let cfg = Config::new()
        .with_decimal()
        .with_byte_suffix(ByteSuffix::Require);
    assert_eq!(cfg.parse_size("3.5MB"), Ok(3_500_000));
    assert_eq!(cfg.parse_size("2.5KiB"), Ok(2560));
    assert_eq!(cfg.parse_size("7"), Err(Error::InvalidDigit));
    assert_eq!(cfg.parse_size("9b"), Ok(9));

    let cfg = Config::default().with_byte_suffix(ByteSuffix::Deny);
    assert_eq!(cfg.parse_size("3.5MB"), Err(Error::InvalidDigit));
    assert_eq!(cfg.parse_size("3.5M"), Ok(3_500_000));
    assert_eq!(cfg.parse_size("7b"), Err(Error::InvalidDigit));
}

#[test]
fn test_int_error_kind() {
    extern crate alloc;
    use alloc::string::ToString as _;

    let test_cases = [
        (Error::Empty, ""),
        (Error::InvalidDigit, "?"),
        (Error::PosOverflow, "99999999999999999999"),
    ];
    for (expected_error, parse_from) in test_cases {
        let std_error = parse_from.parse::<u64>().unwrap_err();
        let local_error = parse_size(parse_from).unwrap_err();
        assert_eq!(local_error, expected_error);
        assert_eq!(local_error.to_string(), std_error.to_string());
        assert_eq!(&IntErrorKind::from(local_error), std_error.kind());
    }
}
