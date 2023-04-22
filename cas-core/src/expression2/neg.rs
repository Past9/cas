use std::ops::Neg;

use super::Expr;

impl Neg for Expr {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            Expr::Symbol(symbol) => Expr::product(Some(Expr::Integer(-1)), [Expr::Symbol(symbol)]),
            Expr::Integer(integer) => Expr::Integer(-integer),
            Expr::Fraction(num, den) => Expr::Fraction(-num, den),
            Expr::Product(operands) => Expr::Product(operands) * Expr::Integer(-1),
            Expr::Sum(operands) => Expr::Sum(operands) * Expr::Integer(-1),
        }
    }
}
