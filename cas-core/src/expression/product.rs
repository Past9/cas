use std::{
    f32::consts::E,
    ops::{Add, Mul},
};

use super::{fraction::Fraction, integer::Integer, symbol::Symbol, Expr};

#[derive(Debug, PartialEq, Eq)]
pub struct Product {
    pub(crate) operands: Vec<Expr>,
}
impl Product {}
impl Mul<Symbol> for Product {
    type Output = Expr;

    fn mul(self, rhs: Symbol) -> Self::Output {
        for operand in self.operands.iter() {
            if let Expr::Symbol(ref symbol) = operand {
                if symbol.name == rhs.name {
                    // Increment power and return
                    todo!()
                }
            }
        }

        let mut operands = self.operands;
        operands.push(Expr::Symbol(rhs));
        Expr::Product(Self { operands })
    }
}
impl Mul<Integer> for Product {
    type Output = Expr;

    fn mul(self, rhs: Integer) -> Self::Output {
        if rhs.integer == 0 {
            return Integer::expr(0);
        }

        if rhs.integer == 1 {
            return Expr::Product(self);
        }

        let mut operands = self
            .operands
            .into_iter()
            .enumerate()
            .flat_map(|(i, operand)| {
                if i == 0 {
                    let mut first_operands = match operand {
                        // Only the first operand can be a constant. If it is a constant,
                        // multiply it by the integer.
                        Expr::Integer(integer) => vec![integer * rhs],
                        Expr::Fraction(fraction) => vec![fraction * rhs],
                        // If it's not a constant, insert the integer as the first operand
                        other => vec![Expr::Integer(rhs), other],
                    };

                    // If the constant multiplication above happened to result in a
                    // constant of 1, remove it.
                    if let Expr::Integer(Integer { integer: 1 }) = first_operands[0] {
                        first_operands.remove(0);
                    }

                    first_operands
                } else {
                    vec![operand]
                }
            })
            .collect::<Vec<_>>();

        if operands.len() == 1 {
            // If we're only left with one operand (which could happen due to the removal
            // of 1 above), just return that operand.
            operands.swap_remove(0)
        } else {
            Expr::Product(Self { operands })
        }
    }
}
impl Mul<Fraction> for Product {
    type Output = Expr;

    fn mul(self, rhs: Fraction) -> Self::Output {
        let mut operands = self
            .operands
            .into_iter()
            .enumerate()
            .flat_map(|(i, operand)| {
                if i == 0 {
                    let mut first_operands = match operand {
                        // Only the first operand can be a constant. If it is a constant,
                        // multiply it by the integer.
                        Expr::Integer(integer) => vec![integer * rhs],
                        Expr::Fraction(fraction) => vec![fraction * rhs],
                        // If it's not a constant, insert the fraction as the first operand
                        other => vec![Expr::Fraction(rhs), other],
                    };

                    // If the constant multiplication above happened to result in a
                    // constant of 1, remove it.
                    if let Expr::Integer(Integer { integer: 1 }) = first_operands[0] {
                        first_operands.remove(0);
                    }

                    first_operands
                } else {
                    vec![operand]
                }
            })
            .collect::<Vec<_>>();

        if operands.len() == 1 {
            // If we're only left with one operand (which could happen due to the removal
            // of 1 above), just return that operand.
            operands.swap_remove(0)
        } else {
            Expr::Product(Self { operands })
        }
    }
}
impl Mul<Self> for Product {
    type Output = Expr;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut product = Expr::Product(self);

        for operand in rhs.operands.into_iter() {
            product = product * operand;
        }

        product
    }
}
