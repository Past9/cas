use std::{collections::BTreeSet, ops::Mul};

use super::Expr;

impl Mul for Expr {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Expr::Symbol(l_name), Expr::Symbol(r_name)) => {
                if l_name == r_name {
                    // Symbol ^ 2
                    todo!()
                } else {
                    Expr::product(None, [Expr::Symbol(l_name), Expr::Symbol(r_name)])
                }
            }

            (Expr::Integer(l_integer), Expr::Integer(r_integer)) => {
                Expr::Integer(l_integer * r_integer)
            }

            (Expr::Fraction(l_num, l_den), Expr::Fraction(r_num, r_den)) => {
                Expr::simplify_fraction(l_num * r_num, l_den * r_den)
            }

            (Expr::Product(l_operands), Expr::Product(r_operands)) => {
                let mut product = Expr::Product(l_operands);

                if let Some(const_operand) = r_operands.const_operand {
                    product = product * *const_operand;
                }

                for operand in r_operands.expr_operands.into_iter() {
                    product = product * operand;
                }

                product
            }

            (Expr::Sum(_), Expr::Sum(_)) => todo!(),

            (Expr::Symbol(name), Expr::Integer(integer))
            | (Expr::Integer(integer), Expr::Symbol(name)) => {
                if integer == 0 {
                    Expr::Integer(0)
                } else if integer == 1 {
                    Expr::Symbol(name)
                } else {
                    Expr::product(Some(Expr::Integer(integer)), [Expr::Symbol(name)])
                }
            }

            (Expr::Symbol(name), Expr::Fraction(numerator, denominator))
            | (Expr::Fraction(numerator, denominator), Expr::Symbol(name)) => Expr::product(
                Some(Expr::Fraction(numerator, denominator)),
                [Expr::Symbol(name)],
            ),

            (Expr::Symbol(name), Expr::Product(operands))
            | (Expr::Product(operands), Expr::Symbol(name)) => {
                for operand in operands.expr_operands.iter() {
                    if let Expr::Symbol(ref operand_name) = operand {
                        if *operand_name == name {
                            // return product with Symbol -> Symbol ^ 2
                            todo!()
                        }
                    }
                }

                let mut operands = operands;
                operands.expr_operands.insert(Expr::Symbol(name));
                Expr::Product(operands)
            }

            (Expr::Integer(integer), Expr::Fraction(num, den))
            | (Expr::Fraction(num, den), Expr::Integer(integer)) => {
                Expr::simplify_fraction(num * integer, den)
            }

            (Expr::Integer(integer), Expr::Product(operands))
            | (Expr::Product(operands), Expr::Integer(integer)) => {
                if integer == 0 {
                    return Expr::Integer(0);
                }

                if integer == 1 {
                    return Expr::Product(operands);
                }

                let const_operand = match operands.const_operand {
                    Some(expr) => *expr * Expr::Integer(integer),
                    None => Expr::Integer(integer),
                };

                let const_operand = if const_operand == Expr::Integer(1) {
                    None
                } else {
                    Some(const_operand)
                };

                if const_operand.is_none() && operands.expr_operands.len() == 1 {
                    operands.expr_operands.into_iter().find(|_| true).unwrap()
                } else {
                    Expr::Product(ProductOperands {
                        const_operand: const_operand.map(Box::new),
                        expr_operands: operands.expr_operands,
                    })
                }
            }

            (Expr::Fraction(num, den), Expr::Product(operands))
            | (Expr::Product(operands), Expr::Fraction(num, den)) => {
                let const_operand = match operands.const_operand {
                    Some(expr) => *expr * Expr::Fraction(num, den),
                    None => Expr::Fraction(num, den),
                };

                let const_operand = if const_operand == Expr::Integer(1) {
                    None
                } else {
                    Some(const_operand)
                };

                if const_operand.is_none() && operands.expr_operands.len() == 1 {
                    operands.expr_operands.into_iter().find(|_| true).unwrap()
                } else {
                    Expr::Product(ProductOperands {
                        const_operand: const_operand.map(Box::new),
                        expr_operands: operands.expr_operands,
                    })
                }
            }

            (Expr::Symbol(name), Expr::Sum(operands))
            | (Expr::Sum(operands), Expr::Symbol(name)) => {
                Expr::product(None, [Expr::Symbol(name), Expr::Sum(operands)])
            }

            (Expr::Integer(integer), Expr::Sum(operands))
            | (Expr::Sum(operands), Expr::Integer(integer)) => {
                Expr::product(Some(Expr::Integer(integer)), [Expr::Sum(operands)])
            }

            (Expr::Fraction(num, den), Expr::Sum(operands))
            | (Expr::Sum(operands), Expr::Fraction(num, den)) => {
                Expr::product(Some(Expr::Fraction(num, den)), [Expr::Sum(operands)])
            }

            (Expr::Product(product_operands), Expr::Sum(sum_operands))
            | (Expr::Sum(sum_operands), Expr::Product(product_operands)) => {
                let mut expr_operands = product_operands.expr_operands;
                expr_operands.insert(Expr::Sum(sum_operands));
                Expr::Product(ProductOperands {
                    const_operand: product_operands.const_operand,
                    expr_operands: expr_operands,
                })
            }
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct ProductOperands {
    pub const_operand: Option<Box<Expr>>,
    pub expr_operands: BTreeSet<Expr>,
}
impl ProductOperands {
    pub(crate) fn new<const N: usize>(
        const_operand: Option<Expr>,
        expr_operands: [Expr; N],
    ) -> Self {
        ProductOperands {
            const_operand: const_operand.map(Box::new),
            expr_operands: BTreeSet::from(expr_operands),
        }
    }
}