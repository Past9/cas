use std::ops::Neg;

use super::Expr;

impl Neg for Expr {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            Expr::Symbol(symbol) => Expr::product(Some(Expr::Integer(-1)), [Expr::Symbol(symbol)]),
            Expr::Integer(integer) => Expr::Integer(-integer),
            Expr::Fraction(num, den) => Expr::Fraction(-num, den),
            Expr::Product {
                const_operand,
                expr_operands,
            } => {
                Expr::Product {
                    const_operand,
                    expr_operands,
                } * Expr::Integer(-1)
            }
            Expr::Sum {
                const_operand,
                expr_operands,
            } => {
                Expr::Sum {
                    const_operand,
                    expr_operands,
                } * Expr::Integer(-1)
            }
        }
    }
}
