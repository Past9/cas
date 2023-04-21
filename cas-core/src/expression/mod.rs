use self::{fraction::Fraction, integer::Integer, product::Product, symbol::Symbol};
use crate::parse::{ast::Ast, parse_src};
use rust_decimal::prelude::ToPrimitive;
use std::ops::{Add, Mul, Neg};

mod fraction;
mod integer;
mod product;
mod symbol;

#[derive(Debug, PartialEq, Eq)]
pub enum Expr {
    Symbol(Symbol),
    Integer(Integer),
    Fraction(Fraction),
    Product(Product),
}
impl Expr {
    pub fn from_src(src: &str) -> Self {
        let result = parse_src(src);
        Self::from_ast(result.ast.unwrap())
    }

    pub fn from_ast(ast: Ast) -> Self {
        match ast {
            Ast::Symbol(name) => Symbol::expr(name),
            Ast::Constant(decimal) => {
                let rounded = decimal.round();
                if decimal == rounded {
                    // Decimal is an integer
                    Integer::expr(rounded.to_i128().unwrap())
                } else {
                    // Decimal is a fraction where the numerator is a power of 10
                    Fraction::expr(decimal.mantissa(), 10i128.pow(decimal.scale()))
                }
            }
            Ast::UnaryOp(unary) => match unary.op {
                crate::parse::ast::UnaryOp::Neg => -Self::from_ast(*unary.operand),
                crate::parse::ast::UnaryOp::Fac => todo!(),
            },
            Ast::BinaryOp(binary) => match binary.op {
                crate::parse::ast::BinaryOp::Add => {
                    Expr::from_ast(*binary.l) + Expr::from_ast(*binary.r)
                }
                crate::parse::ast::BinaryOp::Sub => todo!(),
                crate::parse::ast::BinaryOp::Mul => {
                    Expr::from_ast(*binary.l) * Expr::from_ast(*binary.r)
                }
                crate::parse::ast::BinaryOp::Div => todo!(),
                crate::parse::ast::BinaryOp::Exp => todo!(),
            },
        }
    }
}
impl Neg for Expr {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            Expr::Symbol(symbol) => Expr::Product(Product {
                operands: vec![Integer::expr(-1), Expr::Symbol(symbol)],
            }),
            Expr::Integer(integer) => -integer,
            Expr::Fraction(fraction) => -fraction,
            Expr::Product(product) => Expr::Product(product) * Integer::expr(-1),
        }
    }
}
impl Add for Expr {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Expr::Symbol(_), Expr::Symbol(_)) => todo!(),
            (Expr::Symbol(_), Expr::Integer(_)) => todo!(),
            (Expr::Symbol(_), Expr::Fraction(_)) => todo!(),
            (Expr::Integer(_), Expr::Symbol(_)) => todo!(),
            (Expr::Fraction(_), Expr::Symbol(_)) => todo!(),
            (Expr::Integer(l), Expr::Integer(r)) => l + r,
            (Expr::Integer(l), Expr::Fraction(r)) => l + r,
            (Expr::Fraction(l), Expr::Integer(r)) => l + r,
            (Expr::Fraction(l), Expr::Fraction(r)) => l + r,
            (Expr::Symbol(_), Expr::Product(_)) => todo!(),
            (Expr::Integer(_), Expr::Product(_)) => todo!(),
            (Expr::Fraction(_), Expr::Product(_)) => todo!(),
            (Expr::Product(_), Expr::Symbol(_)) => todo!(),
            (Expr::Product(_), Expr::Integer(_)) => todo!(),
            (Expr::Product(_), Expr::Fraction(_)) => todo!(),
            (Expr::Product(_), Expr::Product(_)) => todo!(),
        }
    }
}
impl Mul for Expr {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Expr::Symbol(l), Expr::Symbol(r)) => l * r,
            (Expr::Symbol(l), Expr::Integer(r)) => l * r,
            (Expr::Symbol(l), Expr::Fraction(r)) => l * r,
            (Expr::Symbol(l), Expr::Product(r)) => l * r,
            (Expr::Integer(l), Expr::Symbol(r)) => l * r,
            (Expr::Integer(l), Expr::Integer(r)) => l * r,
            (Expr::Integer(l), Expr::Fraction(r)) => l * r,
            (Expr::Integer(l), Expr::Product(r)) => l * r,
            (Expr::Fraction(l), Expr::Symbol(r)) => l * r,
            (Expr::Fraction(l), Expr::Integer(r)) => l * r,
            (Expr::Fraction(l), Expr::Fraction(r)) => l * r,
            (Expr::Fraction(l), Expr::Product(r)) => l * r,
            (Expr::Product(l), Expr::Symbol(r)) => l * r,
            (Expr::Product(l), Expr::Integer(r)) => l * r,
            (Expr::Product(l), Expr::Fraction(r)) => l * r,
            (Expr::Product(l), Expr::Product(r)) => l * r,
        }
    }
}

pub(crate) fn gcd(a: u128, b: u128) -> u128 {
    let mut a = a;
    let mut b = b;
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }

    a
}

pub fn symbol(name: &str) -> Expr {
    Symbol::expr(name.into())
}

pub fn integer(integer: i128) -> Expr {
    Integer::expr(integer)
}

pub fn fraction(numerator: i128, denominator: i128) -> Expr {
    Fraction::expr(numerator, denominator)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gcd() {
        assert_eq!(0, gcd(0, 0));
        assert_eq!(10, gcd(0, 10));
        assert_eq!(10, gcd(10, 0));
        assert_eq!(10, gcd(10, 10));
        assert_eq!(7, gcd(49, 21));
    }
}
