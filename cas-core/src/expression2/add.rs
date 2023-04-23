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

            (
                Expr::Product {
                    const_operand: l_const_operand,
                    expr_operands: l_expr_operands,
                },
                Expr::Product {
                    const_operand: r_const_operand,
                    expr_operands: r_expr_operands,
                },
            ) => {
                if l_expr_operands == r_expr_operands {
                    // If all the non-const operands are the same, the result is the sum of
                    // the const operands times the non-const operands.
                    let const_operand = match (l_const_operand, r_const_operand) {
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

                    Expr::Product {
                        const_operand,
                        expr_operands: l_expr_operands,
                    }
                } else {
                    Expr::sum(
                        None,
                        [
                            Expr::Product {
                                const_operand: l_const_operand,
                                expr_operands: l_expr_operands,
                            },
                            Expr::Product {
                                const_operand: r_const_operand,
                                expr_operands: r_expr_operands,
                            },
                        ],
                    )
                }
            }

            (
                Expr::Sum {
                    const_operand: l_const_operand,
                    expr_operands: l_expr_operands,
                },
                Expr::Sum {
                    const_operand: r_const_operand,
                    expr_operands: r_expr_operands,
                },
            ) => {
                // Add const operands.
                // Find all like non-const operands and convert them into
                // "2 * operand" products.

                let mut sum = Expr::Sum {
                    const_operand: l_const_operand,
                    expr_operands: l_expr_operands,
                };

                if let Some(r_const_operand) = r_const_operand {
                    sum = sum + *r_const_operand;
                }

                for r_operand in r_expr_operands.into_iter() {
                    sum = sum + r_operand;
                }

                sum
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

            (
                Expr::Symbol(name),
                Expr::Product {
                    const_operand,
                    mut expr_operands,
                },
            )
            | (
                Expr::Product {
                    const_operand,
                    mut expr_operands,
                },
                Expr::Symbol(name),
            ) => {
                let symbol = Expr::Symbol(name);

                // If the product operands are an optional const and the symbol,
                // increment the const. Otherwise return symbol + product.
                if expr_operands.len() == 1 && expr_operands.contains(&symbol) {
                    let const_operand = match const_operand {
                        Some(const_operand) => *const_operand,
                        None => Expr::Integer(1),
                    } + Expr::Integer(1);
                    Expr::Product {
                        const_operand: Some(Box::new(const_operand)),
                        expr_operands: expr_operands,
                    }
                } else {
                    expr_operands.insert(symbol);
                    Expr::Sum {
                        const_operand,
                        expr_operands,
                    }
                }
            }

            (Expr::Integer(integer), Expr::Fraction(num, den))
            | (Expr::Fraction(num, den), Expr::Integer(integer)) => {
                if integer == 0 {
                    Expr::Fraction(num, den)
                } else {
                    Expr::simplify_fraction(num + integer * den, den)
                }
            }

            (
                Expr::Integer(integer),
                Expr::Product {
                    const_operand,
                    expr_operands,
                },
            )
            | (
                Expr::Product {
                    const_operand,
                    expr_operands,
                },
                Expr::Integer(integer),
            ) => {
                if integer == 0 {
                    Expr::Product {
                        const_operand,
                        expr_operands,
                    }
                } else {
                    Expr::sum(
                        Some(Expr::Integer(integer)),
                        [Expr::Product {
                            const_operand,
                            expr_operands,
                        }],
                    )
                }
            }

            (
                Expr::Fraction(num, den),
                Expr::Product {
                    const_operand,
                    expr_operands,
                },
            )
            | (
                Expr::Product {
                    const_operand,
                    expr_operands,
                },
                Expr::Fraction(num, den),
            ) => Expr::sum(
                Some(Expr::Fraction(num, den)),
                [Expr::Product {
                    const_operand,
                    expr_operands,
                }],
            ),

            (
                Expr::Symbol(name),
                Expr::Sum {
                    const_operand,
                    expr_operands,
                },
            )
            | (
                Expr::Sum {
                    const_operand,
                    expr_operands,
                },
                Expr::Symbol(name),
            ) => todo!(),

            (
                Expr::Integer(integer),
                Expr::Sum {
                    const_operand,
                    expr_operands,
                },
            )
            | (
                Expr::Sum {
                    const_operand,
                    expr_operands,
                },
                Expr::Integer(integer),
            ) => {
                if integer == 0 {
                    Expr::Sum {
                        const_operand,
                        expr_operands,
                    }
                } else {
                    let integer = Expr::Integer(integer);
                    let const_operand = match const_operand {
                        Some(const_operand) => *const_operand + integer,
                        None => integer,
                    };

                    let const_operand = if const_operand != Expr::Integer(1) {
                        Some(Box::new(const_operand))
                    } else {
                        None
                    };

                    Expr::Sum {
                        const_operand,
                        expr_operands: expr_operands,
                    }
                }
            }

            (
                Expr::Fraction(num, den),
                Expr::Sum {
                    const_operand,
                    expr_operands,
                },
            )
            | (
                Expr::Sum {
                    const_operand,
                    expr_operands,
                },
                Expr::Fraction(num, den),
            ) => {
                let fraction = Expr::Fraction(num, den);
                let const_operand = match const_operand {
                    Some(const_operand) => *const_operand + fraction,
                    None => fraction,
                };

                let const_operand = if const_operand != Expr::Integer(1) {
                    Some(Box::new(const_operand))
                } else {
                    None
                };

                Expr::Sum {
                    const_operand,
                    expr_operands: expr_operands,
                }
            }

            (
                Expr::Product {
                    const_operand: product_const_operand,
                    expr_operands: product_expr_operands,
                },
                Expr::Sum {
                    const_operand: sum_const_operand,
                    expr_operands: sum_expr_operands,
                },
            )
            | (
                Expr::Sum {
                    const_operand: sum_const_operand,
                    expr_operands: sum_expr_operands,
                },
                Expr::Product {
                    const_operand: product_const_operand,
                    expr_operands: product_expr_operands,
                },
            ) => {
                todo!()
            }
        }
    }
}
