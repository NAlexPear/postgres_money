use std::{fmt, str};

mod error;
mod parser;

use error::Error;
use std::ops::{Add, Div, Mul, Sub};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Money(Inner);
pub type Inner = i64;

impl Money {
    pub const MIN_INNER: Inner = std::i64::MIN;
    pub const MAX_INNER: Inner = std::i64::MAX;

    pub const fn min() -> Money {
        Money(Money::MIN_INNER)
    }

    pub const fn max() -> Money {
        Money(Money::MAX_INNER)
    }

    pub const fn none() -> Money {
        Money(0)
    }

    pub const fn inner(&self) -> Inner {
        self.0
    }

    fn dollars(&self) -> String {
        format!("{}", self.0 / 100)
    }

    fn cents(&self) -> String {
        let n = self.0.abs() % 100;
        let mut zero_pad = "";
        if n < 10 {
            zero_pad = "0"
        }
        format!("{}{}", zero_pad, n)
    }
}

impl fmt::Debug for Money {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "${}.{}", self.dollars(), self.cents())
    }
}

impl fmt::Display for Money {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "${}.{}", self.dollars(), self.cents())
    }
}

impl str::FromStr for Money {
    type Err = Error;

    fn from_str(money_str: &str) -> Result<Self, Self::Err> {
        Money::parse_str(money_str)
    }
}

impl Default for Money {
    #[inline]
    fn default() -> Self {
        Money::none()
    }
}

macro_rules! derive_op_trait_from_inner {
    (impl $imp:ident, $method:ident) => {
        impl $imp for Money {
            type Output = Self;

            fn $method(self, rhs: Money) -> Self::Output {
                Money(self.inner().$method(rhs.inner()))
            }
        }
    };
}

macro_rules! derive_trait_for_money_with_type {
    (impl $imp:ident with $t:ty, $method:ident) => {
        impl $imp<$t> for Money {
            type Output = Self;

            fn $method(self, rhs: $t) -> Self::Output {
                Money(self.inner().$method(rhs as i64))
            }
        }
    };
}

macro_rules! derive_trait_for_type_with_money {
    (impl $imp:ident with $t:ty, $method:ident) => {
        impl $imp<Money> for $t {
            type Output = Money;

            fn $method(self, rhs: Money) -> Self::Output {
                Money((self as i64).$method(rhs.inner()))
            }
        }
    };
}

macro_rules! add_mul_impl {
    ($($t:ty)+) => ($(
        derive_trait_for_money_with_type! { impl Mul with $t, mul }
        derive_trait_for_type_with_money! { impl Mul with $t, mul }
    )+)
}

macro_rules! add_div_impl {
    ($($t:ty)+) => ($(
        derive_trait_for_money_with_type! { impl Div with $t, div }
    )+)
}

derive_op_trait_from_inner!(impl Add, add);
derive_op_trait_from_inner!(impl Sub, sub);
add_mul_impl! { i64 i32 i16 i8 u32 u16 u8 f64 f32 }
add_div_impl! { i64 i32 i16 i8 u32 u16 u8 }

impl Div<f64> for Money {
    type Output = Self;

    fn div(self, rhs: f64) -> Self::Output {
        let inner = self.inner() as f64 / rhs;
        Money(inner.round() as i64)
    }
}

impl Div<f32> for Money {
    type Output = Self;

    fn div(self, rhs: f32) -> Self::Output {
        let inner = self.inner() as f32 / rhs;
        Money(inner.round() as i64)
    }
}

#[cfg(test)]
mod tests {
    use crate::Money;

    macro_rules! gen_mul_int_tests {
        ($t:ty, $success:ident, $success_reversed:ident, $of_max:ident, $of_min:ident) => {
            #[test]
            fn $success() {
                assert_eq!(Money(7) * 3 as $t, Money(21))
            }

            #[test]
            fn $success_reversed() {
                assert_eq!(3 as $t * Money(7), Money(21))
            }

            #[test]
            #[should_panic]
            #[allow(unused_must_use)]
            fn $of_max() {
                Money::max() * 100 as $t;
            }

            #[test]
            #[should_panic]
            #[allow(unused_must_use)]
            fn $of_min() {
                Money::min() * 100 as $t;
            }
        };
    }

    macro_rules! gen_div_int_tests {
        ($t:ty, $success:ident, $truncates:ident) => {
            #[test]
            fn $success() {
                assert_eq!(Money(21) / 3 as $t, Money(7))
            }

            #[test]
            fn $truncates() {
                assert_eq!(Money(21) / 2 as $t, Money(10))
            }
        };
    }

    #[test]
    fn test_money_default() {
        let default_money = Money::default();
        let nil_money = Money::none();

        assert_eq!(default_money, nil_money);
    }

    gen_mul_int_tests! {
        i64,
        test_mul_success_i64,
        test_mul_success_reversed_i64,
        test_mul_fail_overflow_max_i64,
        test_mul_fail_overflow_min_i64
    }

    gen_mul_int_tests! {
        i32,
        test_mul_success_i32,
        test_mul_success_reversed_i32,
        test_mul_fail_overflow_max_i32,
        test_mul_fail_overflow_min_i32
    }

    gen_mul_int_tests! {
        i16,
        test_mul_success_i16,
        test_mul_success_reversed_i16,
        test_mul_fail_overflow_max_i16,
        test_mul_fail_overflow_min_i16
    }

    gen_mul_int_tests! {
        i8,
        test_mul_success_i8,
        test_mul_success_reversed_i8,
        test_mul_fail_overflow_max_i8,
        test_mul_fail_overflow_min_i8
    }

    gen_mul_int_tests! {
        u32,
        test_mul_success_u32,
        test_mul_success_reversed_u32,
        test_mul_fail_overflow_max_u32,
        test_mul_fail_overflow_min_u32
    }

    gen_mul_int_tests! {
        u16,
        test_mul_success_u16,
        test_mul_success_reversed_u16,
        test_mul_fail_overflow_max_u16,
        test_mul_fail_overflow_min_u16
    }

    gen_mul_int_tests! {
        u8,
        test_mul_success_u8,
        test_mul_success_reversed_u8,
        test_mul_fail_overflow_max_u8,
        test_mul_fail_overflow_min_u8
    }

    gen_div_int_tests! {
        i64,
        test_div_success_i64,
        test_div_truncates_i64
    }

    gen_div_int_tests! {
        i32,
        test_div_success_i32,
        test_div_truncates_i32
    }

    gen_div_int_tests! {
        i16,
        test_div_success_i16,
        test_div_truncates_i16
    }

    gen_div_int_tests! {
        i8,
        test_div_success_i8,
        test_div_truncates_i8
    }

    gen_div_int_tests! {
        u32,
        test_div_success_u32,
        test_div_truncates_u32
    }

    gen_div_int_tests! {
        u16,
        test_div_success_u16,
        test_div_truncates_u16
    }

    gen_div_int_tests! {
        u8,
        test_div_success_u8,
        test_div_truncates_u8
    }

    #[test]
    fn test_addition_success() {
        assert_eq!(Money(1) + Money(1), Money(2))
    }

    #[test]
    #[should_panic]
    #[allow(unused_must_use)]
    fn test_addition_failure_overflow_max() {
        Money::max() + Money(1);
    }

    #[test]
    #[should_panic]
    #[allow(unused_must_use)]
    fn test_addition_failure_overflow_min() {
        Money::min() + Money(-1);
    }

    #[test]
    fn test_subtraction_success() {
        assert_eq!(Money(2) - Money(1), Money(1))
    }

    #[test]
    #[should_panic]
    #[allow(unused_must_use)]
    fn test_subtraction_failure_overflow_max() {
        Money::max() - Money(-1);
    }

    #[test]
    #[should_panic]
    #[allow(unused_must_use)]
    fn test_subtraction_failure_overflow_min() {
        Money::min() - Money(1);
    }

    #[test]
    fn test_money_multiply_f64() {
        assert_eq!(Money(12300) * 2 as f64, Money(24600))
    }

    #[test]
    fn test_f64_multiply_money() {
        assert_eq!(2 as f64 * Money(12300), Money(24600))
    }

    #[test]
    fn test_money_div_f64() {
        assert_eq!(Money(12300) / 2 as f64, Money(6150))
    }

    #[test]
    fn test_money_multiply_f32() {
        assert_eq!(Money(12300) * 2 as f32, Money(24600))
    }

    #[test]
    fn test_f32_multiply_money() {
        assert_eq!(2 as f32 * Money(12300), Money(24600))
    }

    #[test]
    fn test_money_div_f32() {
        assert_eq!(Money(12300) / 2 as f32, Money(6150))
    }

    // Comparisons
    #[test]
    fn test_eq() {
        assert_eq!(Money(12300), Money(12300))
    }

    #[test]
    fn test_not_eq() {
        assert_ne!(Money(12300), Money(12400))
    }

    #[test]
    fn test_lt_eq() {
        assert!(Money(12300) <= Money(12300))
    }

    #[test]
    fn test_gt_eq() {
        assert!(Money(12300) >= Money(12300))
    }

    #[test]
    fn test_lt() {
        assert!(Money(12300) < Money(12400))
    }

    #[test]
    fn test_gt() {
        assert!(Money(12300) > Money(12200))
    }

    #[test]
    fn test_eq_inverse() {
        assert_eq!(Money(12300) == Money(12301), false)
    }

    #[test]
    fn test_not_eq_inverse() {
        assert_eq!(Money(12300) != Money(12300), false)
    }

    #[test]
    fn test_lt_eq_inverse() {
        assert_eq!(Money(12300) <= Money(12299), false)
    }

    #[test]
    fn test_gt_eq_inverse() {
        assert_eq!(Money(12300) >= Money(12301), false)
    }

    #[test]
    fn test_lt_inverse() {
        assert_eq!(Money(12300) < Money(12200), false)
    }

    #[test]
    fn test_gt_inverse() {
        assert_eq!(Money(12300) > Money(12400), false)
    }

    // Rounding vs. Truncation in Division
    #[test]
    fn test_rounded_division_f64() {
        assert_eq!(Money(87808) / 11.0 as f64, Money(7983))
    }

    #[test]
    fn test_rounded_division_f32() {
        assert_eq!(Money(87808) / 11.0 as f32, Money(7983))
    }

    #[test]
    fn test_truncated_division_i64() {
        assert_eq!(Money(87808) / 11 as i64, Money(7982))
    }

    #[test]
    fn test_truncated_division_i32() {
        assert_eq!(Money(87808) / 11 as i32, Money(7982))
    }

    #[test]
    fn test_truncated_division_i16() {
        assert_eq!(Money(87808) / 11 as i16, Money(7982))
    }

    #[test]
    fn test_truncated_division_i8() {
        assert_eq!(Money(87808) / 11 as i8, Money(7982))
    }

    // Precision loss
    #[test]
    fn test_precision_loss_i64() {
        assert_eq!(
            Money(9000000000000009900) / 10 as i64,
            Money(900000000000000990)
        )
    }

    #[test]
    fn test_precision_loss_i32() {
        assert_eq!(
            Money(9000000000000009900) / 10 as i32,
            Money(900000000000000990)
        )
    }

    #[test]
    fn test_precision_loss_i16() {
        assert_eq!(
            Money(9000000000000009900) / 10 as i16,
            Money(900000000000000990)
        )
    }

    #[test]
    fn test_precision_loss_i8() {
        assert_eq!(
            Money(9000000000000009900) / 10 as i8,
            Money(900000000000000990)
        )
    }
}
