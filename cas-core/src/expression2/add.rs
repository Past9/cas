use std::{collections::BTreeSet, ops::Add};

use super::{Expr, ProductOperands};

impl Add for Expr {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Expr::Symbol(l_name), Expr::Symbol(r_name)) => {
                if l_name == r_name {
                    Expr::product(Some(Expr::Integer(2)), [Expr::Symbol(l_name)])
                } else {
                    Expr::sum(None, [Expr::Symbol(l_name), Expr::Symbol(r_name)])
                }
            }

            (Expr::Integer(l_integer), Expr::Integer(r_integer)) => {
                Expr::Integer(l_integer + r_integer)
            }

            (Expr::Fraction(l_num, l_den), Expr::Fraction(r_num, r_den)) => {
                Expr::simplify_fraction(l_num * r_den + r_num * l_den, l_den * r_den)
            }

            (Expr::Product(l_operands), Expr::Product(r_operands)) => {
                if l_operands.expr_operands == r_operands.expr_operands {
                    // If all the non-const operands are the same, the result is the sum of
                    // the const operands times the non-const operands.
                    let const_operand = match (l_operands.const_operand, r_operands.const_operand) {
                        (None, None) => Expr::Integer(2),
                        (None, Some(r)) => Expr::Integer(1) + *r,
                        (Some(l), None) => *l + Expr::Integer(1),
                        (Some(l), Some(r)) => *l + *r,
                    };

                    // If the summed const operand is 1, don't include it
                    let const_operand = if const_operand == Expr::Integer(1) {
                        None
                    } else {
                        Some(Box::new(const_operand))
                    };

                    Expr::Product(ProductOperands {
                        const_operand,
                        expr_operands: l_operands.expr_operands,
                    })
                } else {
                    Expr::sum(None, [Expr::Product(l_operands), Expr::Product(r_operands)])
                }
            }

            (Expr::Sum(l_operands), Expr::Sum(r_operands)) => {
                // Add const operands.
                // Find all like non-const operands and convert them into
                // "2 * operand" products.
                todo!()
            }

            (Expr::Symbol(name), Expr::Integer(integer))
            | (Expr::Integer(integer), Expr::Symbol(name)) => {
                if integer == 0 {
                    Expr::Symbol(name)
                } else {
                    Expr::sum(Some(Expr::Integer(integer)), [Expr::Symbol(name)])
                }
            }

            (Expr::Symbol(name), Expr::Fraction(num, den))
            | (Expr::Fraction(num, den), Expr::Symbol(name)) => {
                Expr::sum(Some(Expr::Fraction(num, den)), [Expr::Symbol(name)])
            }

            (Expr::Symbol(name), Expr::Product(operands))
            | (Expr::Product(operands), Expr::Symbol(name)) => {
                // If the product operands are an optional const and the symbol,
                // increment the const. Otherwise return symbol + product.
                todo!()
            }

            (Expr::Integer(integer), Expr::Fraction(num, den))
            | (Expr::Fraction(num, den), Expr::Integer(integer)) => {
                if integer == 0 {
                    Expr::Fraction(num, den)
                } else {
                    Expr::simplify_fraction(num + integer * den, den)
                }
            }

            (Expr::Integer(integer), Expr::Product(operands))
            | (Expr::Product(operands), Expr::Integer(integer)) => {
                if integer == 0 {
                    Expr::Product(operands)
                } else {
                    //
                    todo!()
                }
            }

            (Expr::Fraction(num, den), Expr::Product(operands))
            | (Expr::Product(operands), Expr::Fraction(num, den)) => {
                todo!()
            }

            (Expr::Symbol(name), Expr::Sum(operands))
            | (Expr::Sum(operands), Expr::Symbol(name)) => todo!(),

            (Expr::Integer(integer), Expr::Sum(operands))
            | (Expr::Sum(operands), Expr::Integer(integer)) => {
                if integer == 0 {
                    Expr::Sum(operands)
                } else {
                    let integer = Expr::Integer(integer);
                    let const_operand = match operands.const_operand {
                        Some(const_operand) => *const_operand + integer,
                        None => integer,
                    };

                    let const_operand = if const_operand != Expr::Integer(1) {
                        Some(Box::new(const_operand))
                    } else {
                        None
                    };

                    Expr::Sum(SumOperands {
                        const_operand,
                        expr_operands: operands.expr_operands,
                    })
                }
            }

            (Expr::Fraction(num, den), Expr::Sum(operands))
            | (Expr::Sum(operands), Expr::Fraction(num, den)) => {
                let fraction = Expr::Fraction(num, den);
                let const_operand = match operands.const_operand {
                    Some(const_operand) => *const_operand + fraction,
                    None => fraction,
                };

                let const_operand = if const_operand != Expr::Integer(1) {
                    Some(Box::new(const_operand))
                } else {
                    None
                };

                Expr::Sum(SumOperands {
                    const_operand,
                    expr_operands: operands.expr_operands,
                })
            }

            (Expr::Product(product_operands), Expr::Sum(sum_operands))
            | (Expr::Sum(sum_operands), Expr::Product(product_operands)) => {
                todo!()
            }
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct SumOperands {
    const_operand: Option<Box<Expr>>,
    expr_operands: BTreeSet<Expr>,
}
impl SumOperands {
    pub(crate) fn new<const N: usize>(
        const_operand: Option<Expr>,
        expr_operands: [Expr; N],
    ) -> Self {
        SumOperands {
            const_operand: const_operand.map(Box::new),
            expr_operands: BTreeSet::from(expr_operands),
        }
    }

    /*
    fn find_const_multiple_of(&mut self, expr: &Expr) -> Option<&Expr> {
        self.expr_operands.iter().find(|op| {
            if let Expr::Product(operands) = op {
                if operands.len() == 2 {
                    if &operands[1] == expr {
                        if operands[0].is_const() {
                            true
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                } else {
                    false
                }
            } else {
                false
            }
        })
    }
    */

    /*
    fn add(&mut self, expr: Expr) {
        match expr {
            Expr::Symbol(name) => {
                let symbol = Expr::Symbol(name);
                if self.expr_operands.contains(&symbol) {
                    self.expr_operands.remove(&symbol);
                    self.expr_operands
                        .insert(Expr::Product(vec![Expr::Integer(2), symbol]));
                } else if let Some(const_multiple) = self.find_const_multiple_of(&symbol) {
                    self.expr_operands.remove(const_multiple);
                    self.expr_operands
                        .insert(const_multiple * Expr::Integer(()))
                }
            }
            Expr::Integer(_) => todo!(),
            Expr::Fraction(_, _) => todo!(),
            Expr::Product(_) => todo!(),
            Expr::Sum(_) => todo!(),
        };
    }
    */
}
