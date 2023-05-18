use crate::ast::{helpers::*, Ast};

impl Ast {
    pub fn deriv(self, respect: Ast) -> Self {
        if self == respect {
            // DERIV-1
            int(1)
        } else {
            match self {
                Ast::Und => {
                    return Ast::Und;
                }

                // DERIV-2
                Ast::Pow(base, exp) => {
                    let base = *base;
                    let exp = *exp;
                    return sum([
                        prd([
                            exp.clone(),
                            pow(base.clone(), dif(exp.clone(), int(1))),
                            base.clone().deriv(respect.clone()),
                        ]),
                        prd([
                            exp.clone().deriv(respect),
                            pow(base.clone(), exp),
                            fun("ln", [base]),
                        ]),
                    ])
                    .simplify();
                }

                // DERIV-3
                Ast::Sum(operands) => {
                    let mut iter = operands.into_iter();
                    let first = iter.next().unwrap();
                    let rest = Ast::Sum(iter.collect()).simplify();

                    return sum([first.deriv(respect.clone()), rest.deriv(respect)]).simplify();
                }

                // DERIV-4
                Ast::Prd(operands) => {
                    let mut iter = operands.into_iter();
                    let first = iter.next().unwrap();
                    let rest = Ast::Prd(iter.collect()).simplify();

                    return sum([
                        prd([first.clone().deriv(respect.clone()), rest.clone()]),
                        prd([first, rest.deriv(respect)]),
                    ])
                    .simplify();
                }

                // DERIV-5
                Ast::Fun(ref name, ref args) => {
                    if name == "sin" {
                        if args.len() != 1 {
                            panic!("sin expects 1, argument, {} found", args.len())
                        }

                        let arg = args.iter().next().map(|arg| arg.to_owned()).unwrap();

                        return prd([fun("cos", [arg.clone()]), arg.deriv(respect)]).simplify();
                    }
                }

                _ => {}
            };

            // DERIV-6
            if self.is_free_of(&respect) {
                return int(0);
            }

            // DERIV-7
            return fun("deriv", [self, respect]);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{ast::helpers::*, helpers::expect_ast};

    #[test]
    fn derives() {
        assert_eq!(
            expect_ast("x^2").simplify().deriv(sym("x")),
            expect_ast("2*x").simplify()
        );

        assert_eq!(
            expect_ast("x^-1").simplify().deriv(sym("x")),
            expect_ast("-(x^-2)").simplify()
        );

        assert_eq!(
            expect_ast("5*x^2 + 3*x + 6").simplify().deriv(sym("x")),
            expect_ast("10*x + 3").simplify()
        );
    }
}
