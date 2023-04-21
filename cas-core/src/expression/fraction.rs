use super::{gcd, integer::Integer, product::Product, symbol::Symbol, Expr};
use std::ops::{Add, Mul, Neg};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fraction {
    numerator: i128,
    denominator: i128,
}
impl Fraction {
    pub fn expr(numerator: i128, denominator: i128) -> Expr {
        if denominator == 0 {
            panic!("Denominator cannot be zero");
        }

        if numerator == 0 {
            return Integer::expr(0);
        }

        // Make sure that only the numerator is ever negative
        let (num, den) = match (numerator.is_negative(), denominator.is_negative()) {
            (true, true) => (-numerator, -denominator),
            (true, false) => (numerator, denominator),
            (false, true) => (-numerator, -denominator),
            (false, false) => (numerator, denominator),
        };

        // Get the Greatest Common Divisor and simplify the fraction
        let gcd = gcd(num as u128, den as u128) as i128;

        let (num_div, num_rem) = (num / gcd, num % gcd);
        let (den_div, den_rem) = (den / gcd, den % gcd);

        let (simplified_num, simplified_den) = if num_rem == 0 && den_rem == 0 {
            (num_div, den_div)
        } else {
            (num, den)
        };

        if simplified_den == 1 {
            // If the denominator is 1, the fraction simplifies to an integer
            Integer::expr(simplified_num)
        } else {
            // Otherwise it's a fraction
            Expr::Fraction(Self {
                numerator: simplified_num,
                denominator: simplified_den,
            })
        }
    }

    pub fn numerator(&self) -> i128 {
        self.numerator
    }

    pub fn denominator(&self) -> i128 {
        self.denominator
    }
}
impl Neg for Fraction {
    type Output = Expr;

    fn neg(self) -> Self::Output {
        Self::expr(self.numerator() * -1, self.denominator()).into()
    }
}
impl Add<Self> for Fraction {
    type Output = Expr;

    fn add(self, rhs: Self) -> Self::Output {
        Self::expr(
            self.numerator * rhs.denominator + rhs.numerator * self.denominator,
            self.denominator * rhs.denominator,
        )
    }
}
impl Add<Integer> for Fraction {
    type Output = Expr;

    fn add(self, rhs: Integer) -> Self::Output {
        Self::expr(
            self.numerator + rhs.value() * self.denominator,
            self.denominator,
        )
    }
}
impl Mul<Self> for Fraction {
    type Output = Expr;

    fn mul(self, rhs: Self) -> Self::Output {
        Self::expr(
            self.numerator * rhs.numerator,
            self.denominator * rhs.denominator,
        )
    }
}
impl Mul<Symbol> for Fraction {
    type Output = Expr;

    fn mul(self, rhs: Symbol) -> Self::Output {
        rhs * self
    }
}
impl Mul<Integer> for Fraction {
    type Output = Expr;

    fn mul(self, rhs: Integer) -> Self::Output {
        Self::expr(self.numerator * rhs.integer, self.denominator)
    }
}
impl Mul<Product> for Fraction {
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
    fn reads_decimal_fraction() {
        assert_eq!(Expr::from_src("1.2"), fraction(12, 10));
        assert_eq!(Expr::from_src("0.12"), fraction(12, 100));
        assert_eq!(Expr::from_src("12.0"), integer(12));
    }

    #[test]
    fn reads_negative_decimal_fraction() {
        assert_eq!(Expr::from_src("-1.2"), fraction(-12, 10));
        assert_eq!(Expr::from_src("-0.12"), fraction(-12, 100));
        assert_eq!(Expr::from_src("-12.0"), integer(-12));
    }

    #[test]
    fn only_numerator_is_negative() {
        assert_eq!(
            fraction(-1, 2),
            Expr::Fraction(Fraction {
                numerator: -1,
                denominator: 2
            })
        );
        assert_eq!(
            fraction(1, -2),
            Expr::Fraction(Fraction {
                numerator: -1,
                denominator: 2
            })
        );
        assert_eq!(
            fraction(-1, -2),
            Expr::Fraction(Fraction {
                numerator: 1,
                denominator: 2
            })
        );
        assert_eq!(
            fraction(1, 2),
            Expr::Fraction(Fraction {
                numerator: 1,
                denominator: 2
            })
        );
    }

    #[test]
    fn simplifies_fraction_to_fraction() {
        assert_eq!(
            fraction(12, 10),
            Expr::Fraction(Fraction {
                numerator: 6,
                denominator: 5
            })
        );
        assert_eq!(
            fraction(-12, 10),
            Expr::Fraction(Fraction {
                numerator: -6,
                denominator: 5
            })
        );
        assert_eq!(
            fraction(12, -10),
            Expr::Fraction(Fraction {
                numerator: -6,
                denominator: 5
            })
        );
        assert_eq!(
            fraction(-12, -10),
            Expr::Fraction(Fraction {
                numerator: 6,
                denominator: 5
            })
        );
    }

    #[test]
    fn simplifies_fraction_to_integer() {
        assert_eq!(fraction(0, 2), Expr::Integer(Integer { integer: 0 }));
        assert_eq!(fraction(4, 1), Expr::Integer(Integer { integer: 4 }));
        assert_eq!(fraction(4, 2), Expr::Integer(Integer { integer: 2 }));
        assert_eq!(fraction(-4, 2), Expr::Integer(Integer { integer: -2 }));
        assert_eq!(fraction(4, -2), Expr::Integer(Integer { integer: -2 }));
        assert_eq!(fraction(-4, -2), Expr::Integer(Integer { integer: 2 }));
    }

    #[test]
    fn fraction_plus_fraction() {
        assert_eq!(
            Fraction::expr(1, 3) + Fraction::expr(1, 2),
            Fraction::expr(5, 6)
        );
        assert_eq!(
            Fraction::expr(1, 3) + Fraction::expr(-1, 2),
            Fraction::expr(-1, 6)
        );
        assert_eq!(
            Fraction::expr(-1, 3) + Fraction::expr(-1, 2),
            Fraction::expr(-5, 6)
        );
        assert_eq!(
            Fraction::expr(2, 3) + Fraction::expr(3, 2),
            Fraction::expr(13, 6)
        );
        assert_eq!(
            Fraction::expr(-2, 3) + Fraction::expr(3, 2),
            Fraction::expr(5, 6)
        );
        assert_eq!(
            Fraction::expr(2, 3) + Fraction::expr(-3, 2),
            Fraction::expr(-5, 6)
        );
        assert_eq!(
            Fraction::expr(-2, 3) + Fraction::expr(-3, 2),
            Fraction::expr(-13, 6)
        );
        assert_eq!(
            Fraction::expr(1, 3) + Fraction::expr(-1, 3),
            Integer::expr(0)
        );
    }

    #[test]
    fn fraction_plus_int() {
        assert_eq!(Expr::from_src("2.2 + 1"), fraction(32, 10));
        assert_eq!(Expr::from_src("-2.2 + 1"), fraction(-12, 10));
        assert_eq!(Expr::from_src("2.2 + -1"), fraction(12, 10));
        assert_eq!(Expr::from_src("-1.0 + 1"), integer(0));
        assert_eq!(Expr::from_src("1.0 + -1"), integer(0));
    }

    #[test]
    fn fraction_times_int() {
        assert_eq!(Expr::from_src("2.3 * 2"), fraction(46, 10));
        assert_eq!(Expr::from_src("-2.3 * 2"), fraction(-46, 10));
        assert_eq!(Expr::from_src("-2.3 * 0"), integer(0));
        assert_eq!(Expr::from_src("0.5 * 2"), integer(1));
        assert_eq!(Expr::from_src("2.0 * 2"), integer(4));
        assert_eq!(Expr::from_src("2.3 * 0.5 * 2"), fraction(23, 10));
        assert_eq!(Expr::from_src("2.3 * 2 * 2"), fraction(92, 10));
    }
}
