use std::{collections::BTreeSet, ops::Add};

use crate::parse::ast::{con, exp};

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

                    if const_operand == Expr::Integer(1) {
                        if l_expr_operands.len() == 1 {
                            l_expr_operands.into_iter().next().unwrap()
                        } else {
                            Expr::Product {
                                const_operand: None,
                                expr_operands: l_expr_operands,
                            }
                        }
                    } else if const_operand == Expr::Integer(0) {
                        Expr::Integer(0)
                    } else {
                        Expr::Product {
                            const_operand: Some(Box::new(const_operand)),
                            expr_operands: l_expr_operands,
                        }
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
                    expr_operands,
                },
            )
            | (
                Expr::Product {
                    const_operand,
                    expr_operands,
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

                    if const_operand == Expr::Integer(0) {
                        Expr::Integer(0)
                    } else {
                        Expr::Product {
                            const_operand: Some(Box::new(const_operand)),
                            expr_operands: expr_operands,
                        }
                    }
                } else {
                    Expr::sum(
                        None,
                        [
                            Expr::Product {
                                const_operand,
                                expr_operands,
                            },
                            symbol,
                        ],
                    )
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
                    mut expr_operands,
                },
            )
            | (
                Expr::Sum {
                    const_operand,
                    mut expr_operands,
                },
                Expr::Symbol(name),
            ) => {
                let symbol = Expr::Symbol(name);

                if expr_operands.contains(&symbol) {
                    // If the sum contains the symbol, replace that symbol with 2 * <symbol>
                    expr_operands.remove(&symbol);
                    expr_operands.insert(Expr::product(Some(Expr::Integer(2)), [symbol]));
                    Expr::Sum {
                        const_operand,
                        expr_operands,
                    }
                } else {
                    // If any operand in the sum is a product that is a constant multiple of the symbol,
                    // increment that constant.
                    let mut operands = BTreeSet::new();
                    let mut found_multiple = false;
                    for operand in expr_operands.into_iter() {
                        if !found_multiple && operand.const_multiple_of(&symbol).is_some() {
                            operands.insert(operand + symbol.clone());
                            found_multiple = true;
                        } else {
                            operands.insert(operand);
                        }
                    }

                    // Otherwise, insert the symbol into the sum
                    if !found_multiple {
                        operands.insert(symbol);
                    }

                    Expr::Sum {
                        const_operand,
                        expr_operands: operands,
                    }
                    .simplify_sum()
                }
            }

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

                    let const_operand = if const_operand != Expr::Integer(0) {
                        Some(Box::new(const_operand))
                    } else {
                        None
                    };

                    Expr::Sum {
                        const_operand,
                        expr_operands: expr_operands,
                    }
                    .simplify_sum()
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
                .simplify_sum()
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
                let mut product = Expr::Product {
                    const_operand: product_const_operand,
                    expr_operands: product_expr_operands,
                };

                if let Some(sum_const_operand) = sum_const_operand {
                    product = product + *sum_const_operand;
                }

                for sum_expr_operand in sum_expr_operands.into_iter() {
                    product = product + sum_expr_operand;
                }

                product

                /*
                sum_expr_operands.insert(Expr::Product {
                    const_operand: product_const_operand,
                    expr_operands: product_expr_operands,
                });
                Expr::Sum {
                    const_operand: sum_const_operand,
                    expr_operands: sum_expr_operands,
                }
                */
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn symbol_plus_symbol() {
        assert_eq!(
            Expr::from_src("x + x"),
            Expr::product(Some(Expr::Integer(2)), [Expr::Symbol("x".into())])
        );
        assert_eq!(
            Expr::from_src("x + y"),
            Expr::sum(None, [Expr::Symbol("x".into()), Expr::Symbol("y".into())])
        );
    }

    #[test]
    fn integer_plus_integer() {
        assert_eq!(Expr::from_src("1 + 1"), Expr::Integer(2));
        assert_eq!(Expr::from_src("1 + -1"), Expr::Integer(0));
        assert_eq!(Expr::from_src("1 - 1"), Expr::Integer(0));
        assert_eq!(Expr::from_src("-1 + 1"), Expr::Integer(0));
        assert_eq!(Expr::from_src("100 + 23"), Expr::Integer(123));
        assert_eq!(Expr::from_src("-100 + 23"), Expr::Integer(-77));
        assert_eq!(Expr::from_src("23 - 100"), Expr::Integer(-77));
    }

    #[test]
    fn fraction_plus_fraction() {
        assert_eq!(Expr::from_src("1.2 + 1.3"), Expr::Fraction(5, 2));
        assert_eq!(Expr::from_src("1.2 + -1.3"), Expr::Fraction(-1, 10));
        assert_eq!(Expr::from_src("-1.2 + 1.3"), Expr::Fraction(1, 10));
        assert_eq!(Expr::from_src("-1.2 + 1.3"), Expr::Fraction(1, 10));
        assert_eq!(Expr::from_src("-1.2 + -1.3"), Expr::Fraction(-5, 2));
        assert_eq!(Expr::from_src("-1.2 - 1.3"), Expr::Fraction(-5, 2));
        assert_eq!(Expr::from_src("1.2 + 0.8"), Expr::Integer(2));
        assert_eq!(Expr::from_src("1.2 - 3.2"), Expr::Integer(-2));
        assert_eq!(Expr::from_src("1.2 - 1.2"), Expr::Integer(0));
    }

    #[test]
    fn product_plus_product() {
        assert_eq!(
            Expr::from_src("2 * x + 3 * x"),
            Expr::product(Some(Expr::Integer(5)), [Expr::Symbol("x".into())])
        );
        assert_eq!(
            Expr::from_src("2 * x - 3 * x"),
            Expr::product(Some(Expr::Integer(-1)), [Expr::Symbol("x".into())])
        );
        assert_eq!(
            Expr::from_src("2 * x + 3 * -x"),
            Expr::product(Some(Expr::Integer(-1)), [Expr::Symbol("x".into())])
        );
        assert_eq!(
            Expr::from_src("2 * x - 3 * -x"),
            Expr::product(Some(Expr::Integer(5)), [Expr::Symbol("x".into())])
        );
        assert_eq!(
            Expr::from_src("2 * x + x * 3"),
            Expr::product(Some(Expr::Integer(5)), [Expr::Symbol("x".into())])
        );
        assert_eq!(
            Expr::from_src("2 * x * y + 3 * y * x"),
            Expr::product(
                Some(Expr::Integer(5)),
                [Expr::Symbol("x".into()), Expr::Symbol("y".into())]
            )
        );
        assert_eq!(Expr::from_src("3 * x - 2 * x"), Expr::Symbol("x".into()));
        assert_eq!(
            Expr::from_src("3 * x * y - y * 2 * x"),
            Expr::product(None, [Expr::Symbol("x".into()), Expr::Symbol("y".into())])
        );
        assert_eq!(Expr::from_src("2 * x - 2 * x"), Expr::Integer(0));
        assert_eq!(
            Expr::from_src("x * y + y * x"),
            Expr::product(
                Some(Expr::Integer(2)),
                [Expr::Symbol("x".into()), Expr::Symbol("y".into()),]
            )
        );
        assert_eq!(
            Expr::from_src("x * y + x * z"),
            Expr::sum(
                None,
                [
                    Expr::product(None, [Expr::Symbol("x".into()), Expr::Symbol("y".into())]),
                    Expr::product(None, [Expr::Symbol("x".into()), Expr::Symbol("z".into())])
                ]
            )
        );
        assert_eq!(
            Expr::from_src("x * y - x * z"),
            Expr::sum(
                None,
                [
                    Expr::product(None, [Expr::Symbol("x".into()), Expr::Symbol("y".into())]),
                    Expr::product(
                        Some(Expr::Integer(-1)),
                        [Expr::Symbol("x".into()), Expr::Symbol("z".into())]
                    )
                ]
            )
        );
        assert_eq!(
            Expr::from_src("x * 2 * y - x * z"),
            Expr::sum(
                None,
                [
                    Expr::product(
                        Some(Expr::Integer(2)),
                        [Expr::Symbol("x".into()), Expr::Symbol("y".into())]
                    ),
                    Expr::product(
                        Some(Expr::Integer(-1)),
                        [Expr::Symbol("x".into()), Expr::Symbol("z".into())]
                    )
                ]
            )
        );
    }

    #[test]
    fn sum_plus_sum() {
        assert_eq!(
            Expr::from_src("2 + x + 3 + y"),
            Expr::sum(
                Some(Expr::Integer(5)),
                [Expr::Symbol("x".into()), Expr::Symbol("y".into())]
            )
        );
        assert_eq!(
            Expr::from_src("2 + x - 3 + y"),
            Expr::sum(
                Some(Expr::Integer(-1)),
                [Expr::Symbol("x".into()), Expr::Symbol("y".into())]
            )
        );
        assert_eq!(
            Expr::from_src("3 + x - 2 + y"),
            Expr::sum(
                Some(Expr::Integer(1)),
                [Expr::Symbol("x".into()), Expr::Symbol("y".into())]
            )
        );
        assert_eq!(
            Expr::from_src("2 + x - 2 + y"),
            Expr::sum(None, [Expr::Symbol("x".into()), Expr::Symbol("y".into())])
        );
    }

    #[test]
    fn symbol_plus_integer() {
        assert_eq!(
            Expr::from_src("x + 2"),
            Expr::sum(Some(Expr::Integer(2)), [Expr::Symbol("x".into())])
        );
        assert_eq!(Expr::from_src("x + 0"), Expr::Symbol("x".into()));
        assert_eq!(Expr::from_src("x - 0"), Expr::Symbol("x".into()));
        assert_eq!(Expr::from_src("0 + x"), Expr::Symbol("x".into()));
    }

    #[test]
    fn symbol_plus_fraction() {
        assert_eq!(
            Expr::from_src("x + 1.2"),
            Expr::sum(Some(Expr::Fraction(6, 5)), [Expr::Symbol("x".into())])
        );
        assert_eq!(
            Expr::from_src("x - 1.2"),
            Expr::sum(Some(Expr::Fraction(-6, 5)), [Expr::Symbol("x".into())])
        );
    }

    #[test]
    fn symbol_plus_product() {
        assert_eq!(
            Expr::from_src("x + y * z"),
            Expr::sum(
                None,
                [
                    Expr::Symbol("x".into()),
                    Expr::product(None, [Expr::Symbol("y".into()), Expr::Symbol("z".into()),])
                ]
            )
        );
        assert_eq!(
            Expr::from_src("x + 2 * x"),
            Expr::product(Some(Expr::Integer(3)), [Expr::Symbol("x".into()),])
        );
        assert_eq!(
            Expr::from_src("x - 2 * x"),
            Expr::product(Some(Expr::Integer(-1)), [Expr::Symbol("x".into()),])
        );
        assert_eq!(
            Expr::from_src("x + 2 * -x"),
            Expr::product(Some(Expr::Integer(-1)), [Expr::Symbol("x".into()),])
        );
        assert_eq!(Expr::from_src("x + x + -2 * x"), Expr::Integer(0));
    }

    #[test]
    fn integer_plus_fraction() {
        assert_eq!(Expr::from_src("2 + 1.2"), Expr::Fraction(16, 5));
        assert_eq!(Expr::from_src("2 - 1.2"), Expr::Fraction(4, 5));
        assert_eq!(Expr::from_src("-2 + 1.2"), Expr::Fraction(-4, 5));
        assert_eq!(Expr::from_src("-2 - 1.2"), Expr::Fraction(-16, 5));
        assert_eq!(Expr::from_src("1.2 - 1.2"), Expr::Integer(0));
        assert_eq!(Expr::from_src("1.8 + 1.2"), Expr::Integer(3));
        assert_eq!(Expr::from_src("-1.8 + -1.2"), Expr::Integer(-3));
        assert_eq!(Expr::from_src("-1.8 - 1.2"), Expr::Integer(-3));
    }

    #[test]
    fn integer_plus_product() {
        assert_eq!(
            Expr::from_src("2 + x * y"),
            Expr::sum(
                Some(Expr::Integer(2)),
                [Expr::product(
                    None,
                    [Expr::Symbol("x".into()), Expr::Symbol("y".into()),]
                )]
            )
        );
        assert_eq!(
            Expr::from_src("0 + x * y"),
            Expr::product(None, [Expr::Symbol("x".into()), Expr::Symbol("y".into()),])
        );
        assert_eq!(
            Expr::from_src("2 + 2 * x"),
            Expr::sum(
                Some(Expr::Integer(2)),
                [Expr::product(
                    Some(Expr::Integer(2)),
                    [Expr::Symbol("x".into()),]
                )]
            )
        );
        assert_eq!(
            Expr::from_src("0 + 2 * x"),
            Expr::product(Some(Expr::Integer(2)), [Expr::Symbol("x".into()),])
        );
    }

    #[test]
    fn fraction_plus_product() {
        assert_eq!(
            Expr::from_src("1.2 + x * y"),
            Expr::sum(
                Some(Expr::Fraction(6, 5)),
                [Expr::product(
                    None,
                    [Expr::Symbol("x".into()), Expr::Symbol("y".into()),]
                )]
            )
        );
    }

    #[test]
    fn symbol_plus_sum() {
        assert_eq!(
            Expr::from_src("2 + x + y"),
            Expr::sum(
                Some(Expr::Integer(2)),
                [Expr::Symbol("x".into()), Expr::Symbol("y".into()),]
            )
        );
        assert_eq!(
            Expr::from_src("2 + x + x"),
            Expr::sum(
                Some(Expr::Integer(2)),
                [Expr::product(
                    Some(Expr::Integer(2)),
                    [Expr::Symbol("x".into())]
                )]
            )
        );
        assert_eq!(Expr::from_src("2 - x + x"), Expr::Integer(2));
        assert_eq!(Expr::from_src("2 - x + x + -x + x"), Expr::Integer(2));
    }

    #[test]
    fn integer_plus_sum() {
        assert_eq!(
            Expr::from_src("2 + x + 2"),
            Expr::sum(Some(Expr::Integer(4)), [Expr::Symbol("x".into())])
        );
        assert_eq!(Expr::from_src("2 + x - 2"), Expr::Symbol("x".into()));
        assert_eq!(
            Expr::from_src("2 + x + y - 2"),
            Expr::sum(None, [Expr::Symbol("x".into()), Expr::Symbol("y".into())])
        );
    }

    #[test]
    fn fraction_plus_sum() {
        assert_eq!(
            Expr::from_src("1.2 + x + 1.2"),
            Expr::sum(Some(Expr::Fraction(12, 5)), [Expr::Symbol("x".into())])
        );
        assert_eq!(Expr::from_src("1.2 + x - 1.2"), Expr::Symbol("x".into()));
        assert_eq!(
            Expr::from_src("1.2 + x + y - 1.2"),
            Expr::sum(None, [Expr::Symbol("x".into()), Expr::Symbol("y".into())])
        );
    }

    #[test]
    fn product_plus_sum() {
        assert_eq!(
            Expr::from_src("w + x + y * z"),
            Expr::sum(
                None,
                [
                    Expr::Symbol("w".into()),
                    Expr::Symbol("x".into()),
                    Expr::product(None, [Expr::Symbol("y".into()), Expr::Symbol("z".into()),])
                ]
            )
        );

        assert_eq!(
            Expr::from_src("x + y + 2 * x"),
            Expr::sum(
                None,
                [
                    Expr::product(Some(Expr::Integer(3)), [Expr::Symbol("x".into())]),
                    Expr::Symbol("y".into()),
                ]
            )
        );

        panic!("Below results in stack overflow");
        assert_eq!(
            Expr::from_src("2 * x + y + 2 * x"),
            Expr::sum(
                None,
                [
                    Expr::product(Some(Expr::Integer(4)), [Expr::Symbol("x".into())]),
                    Expr::Symbol("y".into()),
                ]
            )
        );
    }
}
