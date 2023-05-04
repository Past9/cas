use num::{traits::Pow, BigInt, BigRational, BigUint, FromPrimitive, One, Signed, Zero};
use rust_decimal::Decimal;

use super::Expr;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum ConstantKind {
    Integer(BigInt),
    Fraction(BigRational),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Constant {
    kind: ConstantKind,
}
impl Constant {
    pub(crate) fn unenforced_int(int: i128) -> Expr {
        Expr::Constant(Self {
            kind: ConstantKind::Integer(BigInt::from_i128(int).unwrap()),
        })
    }

    pub(crate) fn unenforced_frac(num: i128, den: i128) -> Expr {
        Expr::Constant(Self {
            kind: ConstantKind::Fraction(BigRational::new(
                BigInt::from_i128(num).unwrap(),
                BigInt::from_i128(den).unwrap(),
            )),
        })
    }

    pub fn zero() -> Self {
        Self {
            kind: ConstantKind::Integer(0.into()),
        }
    }

    pub fn one() -> Self {
        Self {
            kind: ConstantKind::Integer(1.into()),
        }
    }

    pub fn neg_one() -> Self {
        Self {
            kind: ConstantKind::Integer((-1).into()),
        }
    }

    pub fn is_zero(&self) -> bool {
        if let ConstantKind::Integer(int) = &self.kind {
            int.is_zero()
        } else {
            false
        }
    }

    pub fn is_int(&self) -> bool {
        if let ConstantKind::Integer(_) = &self.kind {
            true
        } else {
            false
        }
    }

    pub fn expect_int(self) -> BigInt {
        if let ConstantKind::Integer(int) = self.kind {
            int
        } else {
            panic!("Constant {:?} is not an integer", self)
        }
    }

    pub fn is_pos(&self) -> bool {
        match &self.kind {
            ConstantKind::Integer(integer) => integer.is_positive(),
            ConstantKind::Fraction(fraction) => fraction.is_positive(),
        }
    }

    pub fn is_pos_int(&self) -> bool {
        if let ConstantKind::Integer(int) = &self.kind {
            int.is_positive()
        } else {
            false
        }
    }

    pub fn expect_pos_int(self) -> BigUint {
        if let ConstantKind::Integer(int) = self.kind {
            if int.is_positive() {
                int.to_biguint().unwrap()
            } else {
                panic!("Constant {} is an integer but is not positive", int)
            }
        } else {
            panic!("Constant {:?} is not an integer", self)
        }
    }

    pub fn expect_frac(self) -> BigRational {
        if let ConstantKind::Fraction(frac) = self.kind {
            frac
        } else {
            panic!("Constant {:?} is not a fraction", self)
        }
    }

    pub fn is_one(&self) -> bool {
        if let ConstantKind::Integer(int) = &self.kind {
            int.is_one()
        } else {
            false
        }
    }

    pub fn from_dec(dec: Decimal) -> Self {
        Self::from_frac(BigRational::new(
            dec.mantissa().into(),
            10i128.pow(dec.scale()).into(),
        ))
    }

    pub fn from_int(int: BigInt) -> Self {
        Self {
            kind: ConstantKind::Integer(int),
        }
    }

    pub fn from_i128(int: i128) -> Self {
        Self::from_int(BigInt::from_i128(int).unwrap())
    }

    pub fn from_i128_frac(num: i128, den: i128) -> Self {
        Self::from_frac(BigRational::new(
            BigInt::from_i128(num).unwrap(),
            BigInt::from_i128(den).unwrap(),
        ))
    }

    pub fn from_frac(frac: BigRational) -> Self {
        if frac.is_integer() {
            Self::from_int(frac.to_integer())
        } else {
            Self {
                kind: ConstantKind::Fraction(frac),
            }
        }
    }

    pub fn as_expr(self) -> Expr {
        Expr::Constant(self)
    }

    pub fn negate(self) -> Self {
        match self.kind {
            ConstantKind::Integer(integer) => Self {
                kind: ConstantKind::Integer(integer * -1),
            },
            ConstantKind::Fraction(rational) => Self {
                kind: ConstantKind::Fraction(rational * BigInt::from(-1)),
            },
        }
    }

    pub fn add(self, rhs: Self) -> Self {
        match (self.kind, rhs.kind) {
            (ConstantKind::Integer(l), ConstantKind::Integer(r)) => Self::from_int(l + r),
            (ConstantKind::Fraction(l), ConstantKind::Fraction(r)) => Self::from_frac(l + r),
            (ConstantKind::Integer(int), ConstantKind::Fraction(frac))
            | (ConstantKind::Fraction(frac), ConstantKind::Integer(int)) => {
                Self::from_frac(frac + int)
            }
        }
    }

    pub fn multiply(self, rhs: Self) -> Self {
        match (self.kind, rhs.kind) {
            (ConstantKind::Integer(l), ConstantKind::Integer(r)) => Self::from_int(l * r),
            (ConstantKind::Fraction(l), ConstantKind::Fraction(r)) => Self::from_frac(l * r),
            (ConstantKind::Integer(int), ConstantKind::Fraction(frac))
            | (ConstantKind::Fraction(frac), ConstantKind::Integer(int)) => {
                Self::from_frac(frac * int)
            }
        }
    }

    pub fn reciprocal(self) -> Self {
        match self.kind {
            ConstantKind::Integer(integer) => {
                Self::from_frac(BigRational::new(BigInt::one(), integer))
            }
            ConstantKind::Fraction(fraction) => Self::from_frac(fraction.recip()),
        }
    }

    pub fn power_int(self, exponent: BigInt) -> Self {
        if exponent.is_positive() {
            match self.kind {
                ConstantKind::Integer(integer) => {
                    Self::from_int(integer.pow(exponent.to_biguint().unwrap()))
                }
                ConstantKind::Fraction(fraction) => {
                    Self::from_frac(fraction.pow(exponent.to_biguint().unwrap()))
                }
            }
        } else if exponent.is_negative() {
            self.reciprocal().power_int(exponent.abs())
        } else {
            // exponent is zero, return 1
            Self::one()
        }
    }
}

#[cfg(test)]
mod tests {
    use rust_decimal_macros::dec;

    use crate::expr::{
        constant::Constant,
        test_helpers::{frac, int, test_src},
        Expr,
    };

    #[test]
    fn dec_to_frac() {
        assert_eq!(Constant::from_dec(dec!(1.2)).as_expr(), frac(6, 5));
        assert_eq!(Constant::from_dec(dec!(-1.2)).as_expr(), frac(-6, 5));
        test_src("1.2", frac(6, 5));
    }

    #[test]
    fn dec_to_int() {
        assert_eq!(Constant::from_dec(dec!(2.0)).as_expr(), int(2));
        assert_eq!(Constant::from_dec(dec!(-2.0)).as_expr(), int(-2));
        test_src("2.0", int(2));
    }

    #[test]
    fn div_to_frac() {
        test_src("1/2", frac(1, 2));
        test_src("6/5", frac(6, 5));
        test_src("1/3", frac(1, 3));
    }

    #[test]
    fn div_to_int() {
        test_src("2/1", int(2));
        test_src("4/2", int(2));
    }

    #[test]
    fn negate() {
        test_src("-1.2", frac(-6, 5));
        test_src("-2.0", int(-2));
        test_src("-1/2", frac(-1, 2));
        test_src("1/-2", frac(-1, 2));
        test_src("-(1/2)", frac(-1, 2));
    }

    #[test]
    fn add() {
        test_src("1 + 2", int(3));
        test_src("1/2 + 1/2", int(1));
        test_src("1/2 + 2", frac(5, 2));
    }

    #[test]
    fn subtract() {
        test_src("2 - 1", int(1));
        test_src("1 - 2", int(-1));
        test_src("1/2 - 1/2", int(0));
        test_src("1/2 - 2", frac(-3, 2));
        test_src("2 - 1/2", frac(3, 2));
    }

    #[test]
    fn multiply() {
        test_src("2 * 1", int(2));
        test_src("2 * 2", int(4));
        test_src("2 * 0", int(0));
        test_src("1/2 * 2", int(1));
        test_src("-1/2 * 2", int(-1));
        test_src("1/-2 * 2", int(-1));
        test_src("1/2 * -2", int(-1));
    }

    #[test]
    fn reciprocal() {
        assert_eq!(Constant::from_i128(2).reciprocal().as_expr(), frac(1, 2));
        assert_eq!(Constant::from_i128(-2).reciprocal().as_expr(), frac(-1, 2));
        assert_eq!(
            Constant::from_i128_frac(1, 2).reciprocal().as_expr(),
            int(2)
        );
        assert_eq!(
            Constant::from_i128_frac(-1, 2).reciprocal().as_expr(),
            int(-2)
        );
    }

    #[test]
    fn power_int() {
        test_src("2 ^ -2", frac(1, 4));
        test_src("2 ^ -1", frac(1, 2));
        test_src("2 ^ 0", int(1));
        test_src("2 ^ 1", int(2));
        test_src("2 ^ 2", int(4));
    }
}
