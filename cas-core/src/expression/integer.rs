use super::{fraction::Fraction, product::Product, symbol::Symbol, Expr};
use std::ops::{Add, Mul, Neg};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Integer {
    pub(crate) integer: i128,
}
impl Integer {
    pub fn expr(integer: i128) -> Expr {
        Expr::Integer(Self { integer })
    }

    pub fn value(&self) -> i128 {
        self.integer
    }
}
impl Neg for Integer {
    type Output = Expr;

    fn neg(self) -> Self::Output {
        Self::expr(-self.integer)
    }
}
impl Add<Self> for Integer {
    type Output = Expr;

    fn add(self, rhs: Self) -> Self::Output {
        Self::expr(self.integer + rhs.integer)
    }
}
impl Add<Fraction> for Integer {
    type Output = Expr;

    fn add(self, rhs: Fraction) -> Self::Output {
        rhs + self
    }
}
impl Mul<Self> for Integer {
    type Output = Expr;

    fn mul(self, rhs: Self) -> Self::Output {
        Self::expr(self.integer * rhs.integer)
    }
}
impl Mul<Fraction> for Integer {
    type Output = Expr;

    fn mul(self, rhs: Fraction) -> Self::Output {
        rhs * self
    }
}
impl Mul<Symbol> for Integer {
    type Output = Expr;

    fn mul(self, rhs: Symbol) -> Self::Output {
        if self.integer == 0 {
            Expr::Integer(self)
        } else if self.integer == 1 {
            Expr::Symbol(rhs)
        } else {
            Expr::Product(Product {
                operands: vec![Expr::Integer(self), Expr::Symbol(rhs)],
            })
        }
    }
}
impl Mul<Product> for Integer {
    type Output = Expr;

    fn mul(self, rhs: Product) -> Self::Output {
        rhs * self
    }
}

#[cfg(test)]
mod tests {
    use crate::expression::{fraction, integer};

    use super::*;

    #[test]
    fn reads_integer() {
        assert_eq!(Expr::from_src("123"), integer(123));
        assert_eq!(Expr::from_src("0"), integer(0));
        assert_eq!(Expr::from_src("001"), integer(1));
        assert_eq!(Expr::from_src("100"), integer(100));
    }

    #[test]
    fn reads_negative_integer() {
        assert_eq!(Expr::from_src("-123"), integer(-123));
        assert_eq!(Expr::from_src("-0"), integer(0));
        assert_eq!(Expr::from_src("-001"), integer(-1));
        assert_eq!(Expr::from_src("-100"), integer(-100));
    }

    #[test]
    fn int_plus_int() {
        assert_eq!(Expr::from_src("1 + 2"), integer(3));
        assert_eq!(Expr::from_src("1 + -1"), integer(0));
        assert_eq!(Expr::from_src("1 + -2"), integer(-1));
        assert_eq!(Expr::from_src("-2 + 1"), integer(-1));
        assert_eq!(Expr::from_src("0 + 0"), integer(0));
        assert_eq!(Expr::from_src("1 + 2 + 3"), integer(6));
        assert_eq!(Expr::from_src("-1 + 2 + -3"), integer(-2));
    }

    #[test]
    fn int_plus_fraction() {
        assert_eq!(Expr::from_src("1 + 2.2"), fraction(32, 10));
        assert_eq!(Expr::from_src("1 + -2.2"), fraction(-12, 10));
        assert_eq!(Expr::from_src("-1 + 2.2"), fraction(12, 10));
        assert_eq!(Expr::from_src("1 + -1.0"), integer(0));
        assert_eq!(Expr::from_src("-1 + 1.0"), integer(0));
    }

    #[test]
    fn int_times_int() {
        assert_eq!(Expr::from_src("2 * 3"), integer(6));
        assert_eq!(Expr::from_src("2 * -3"), integer(-6));
        assert_eq!(Expr::from_src("-2 * 3"), integer(-6));
        assert_eq!(Expr::from_src("-2 * -3"), integer(6));
        assert_eq!(Expr::from_src("2 * 3 * 4"), integer(24));
        assert_eq!(Expr::from_src("1 * 2"), integer(2));
        assert_eq!(Expr::from_src("2 * 0"), integer(0));
    }

    #[test]
    fn int_times_fraction() {
        assert_eq!(Expr::from_src("2 * 2.3"), fraction(46, 10));
        assert_eq!(Expr::from_src("2 * -2.3"), fraction(-46, 10));
        assert_eq!(Expr::from_src("0 * -2.3"), integer(0));
        assert_eq!(Expr::from_src("2 * 0.5"), integer(1));
        assert_eq!(Expr::from_src("2 * 2.0"), integer(4));
        assert_eq!(Expr::from_src("2 * 2.3 * 0.5"), fraction(23, 10));
    }
}
