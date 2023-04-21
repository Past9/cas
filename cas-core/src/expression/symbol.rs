use std::ops::Mul;

use super::{fraction::Fraction, integer::Integer, product::Product, Expr};

#[derive(Debug, PartialEq, Eq)]
pub struct Symbol {
    pub(crate) name: String,
}
impl Symbol {
    pub fn expr(name: String) -> Expr {
        Expr::Symbol(Self { name })
    }
}
impl Mul<Self> for Symbol {
    type Output = Expr;

    fn mul(self, rhs: Self) -> Self::Output {
        if self.name == rhs.name {
            // return power
            todo!()
        } else {
            Expr::Product(Product {
                operands: vec![Expr::Symbol(self), Expr::Symbol(rhs)],
            })
        }
    }
}
impl Mul<Integer> for Symbol {
    type Output = Expr;

    fn mul(self, rhs: Integer) -> Self::Output {
        Expr::Product(Product {
            operands: vec![Expr::Integer(rhs), Expr::Symbol(self)],
        })
    }
}
impl Mul<Fraction> for Symbol {
    type Output = Expr;

    fn mul(self, rhs: Fraction) -> Self::Output {
        Expr::Product(Product {
            operands: vec![Expr::Fraction(rhs), Expr::Symbol(self)],
        })
    }
}
impl Mul<Product> for Symbol {
    type Output = Expr;

    fn mul(self, rhs: Product) -> Self::Output {
        rhs * self
    }
}

#[cfg(test)]
mod tests {
    use crate::expression::symbol;

    use super::*;

    #[test]
    fn reads_symbol() {
        assert_eq!(Expr::from_src("x"), symbol("x"));
        assert_eq!(Expr::from_src("foo"), symbol("foo"));
    }
}
