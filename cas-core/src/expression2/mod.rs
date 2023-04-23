mod add;
mod mul;
mod neg;

use std::collections::BTreeSet;

use self::mul::ProductOperands;
use crate::parse::ast::Ast;
use rust_decimal::prelude::ToPrimitive;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Expr {
    Symbol(String),
    Integer(i128),
    Fraction(i128, i128),
    Product {
        const_operand: Option<Box<Expr>>,
        expr_operands: BTreeSet<Expr>,
    },
    Sum {
        const_operand: Option<Box<Expr>>,
        expr_operands: BTreeSet<Expr>,
    },
}
impl Expr {
    pub fn from_ast(ast: Ast) -> Self {
        match ast {
            Ast::Symbol(name) => Self::Symbol(name),
            Ast::Constant(decimal) => {
                let rounded = decimal.round();
                if decimal == rounded {
                    // Decimal is an integer
                    Self::Integer(rounded.to_i128().unwrap())
                } else {
                    // Decimal is a fraction where the numerator is a power of 10
                    Self::simplify_fraction(decimal.mantissa(), 10i128.pow(decimal.scale()))
                }
            }
            Ast::UnaryOp(unary) => match unary.op {
                crate::parse::ast::UnaryOp::Neg => -Self::from_ast(*unary.operand),
                crate::parse::ast::UnaryOp::Fac => todo!(),
            },
            Ast::BinaryOp(binary) => match binary.op {
                crate::parse::ast::BinaryOp::Add => todo!(),
                crate::parse::ast::BinaryOp::Sub => todo!(),
                crate::parse::ast::BinaryOp::Mul => {
                    Self::from_ast(*binary.l) * Self::from_ast(*binary.r)
                }
                crate::parse::ast::BinaryOp::Div => todo!(),
                crate::parse::ast::BinaryOp::Exp => todo!(),
            },
        }
    }

    pub fn const_multiple_of(&self, expr: &Expr) -> Option<Expr> {
        match self {
            Expr::Product {
                const_operand,
                expr_operands,
            } => {
                if expr_operands.len() == 1 && expr_operands.get(expr).is_some() {
                    match &const_operand {
                        Some(const_operand) => Some((**const_operand).clone()),
                        None => Some(Expr::Integer(1)),
                    }
                } else {
                    None
                }
            }
            other if other == expr => Some(Expr::Integer(1)),
            _ => None,
        }
    }

    pub fn const_multiple_of_zeroed(&self, expr: &Expr) -> Expr {
        self.const_multiple_of(expr).unwrap_or(Expr::Integer(0))
    }

    pub fn is_const(&self) -> bool {
        match self {
            Expr::Integer(_) | Expr::Fraction(_, _) => true,
            _ => false,
        }
    }

    fn sum<const N: usize>(const_operand: Option<Expr>, expr_operands: [Expr; N]) -> Self {
        Self::Sum {
            const_operand: const_operand.map(Box::new),
            expr_operands: BTreeSet::from(expr_operands),
        }
    }

    fn product<const N: usize>(const_operand: Option<Expr>, expr_operands: [Expr; N]) -> Self {
        Self::Product {
            const_operand: const_operand.map(Box::new),
            expr_operands: BTreeSet::from(expr_operands),
        }
    }

    fn simplify_fraction(numerator: i128, denominator: i128) -> Self {
        if denominator == 0 {
            panic!("Denominator cannot be zero");
        }

        if numerator == 0 {
            return Self::Integer(0);
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
            Self::Integer(simplified_num)
        } else {
            // Otherwise it's a fraction
            Self::simplify_fraction(simplified_num, simplified_den)
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
