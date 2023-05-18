use crate::ast::{helpers::*, Ast};

impl Ast {
    pub fn trig_substitue(self) -> Self {
        match self {
            ast @ (Ast::Fail | Ast::Und | Ast::Sym(_) | Ast::Int(_) | Ast::Frc(_)) => ast,

            Ast::Neg(operand) => neg(operand.trig_substitue()),
            Ast::Fac(operand) => fac(operand.trig_substitue()),
            Ast::Sum(operands) => {
                Ast::Sum(operands.into_iter().map(Self::trig_substitue).collect())
            }
            Ast::Prd(operands) => {
                Ast::Prd(operands.into_iter().map(Self::trig_substitue).collect())
            }
            Ast::Dif(l, r) => dif(l.trig_substitue(), r.trig_substitue()),
            Ast::Quo(l, r) => quo(l.trig_substitue(), r.trig_substitue()),
            Ast::Pow(base, exp) => pow(base.trig_substitue(), exp.trig_substitue()),

            Ast::Fun(name, args) => {
                let args = args
                    .into_iter()
                    .map(Self::trig_substitue)
                    .collect::<Vec<_>>();

                if name == "tan" {
                    // TRIGSUB-1
                    quo(
                        Ast::Fun("sin".into(), args.clone()),
                        Ast::Fun("cos".into(), args),
                    )
                } else if name == "cot" {
                    // TRIGSUB-2
                    quo(
                        Ast::Fun("cos".into(), args.clone()),
                        Ast::Fun("sin".into(), args),
                    )
                } else if name == "sec" {
                    // TRIGSUB-3
                    quo(int(1), Ast::Fun("cos".into(), args))
                } else if name == "csc" {
                    // TRIGSUB-4
                    quo(int(1), Ast::Fun("sin".into(), args))
                } else {
                    Ast::Fun(name, args)
                }
            }
        }
        .simplify()
    }
}

#[cfg(test)]
mod tests {
    use crate::{ast::helpers::*, helpers::expect_ast};

    #[test]
    pub fn simplifies_trig() {
        assert_eq!(
            expect_ast("tan(x)").simplify().trig_substitue(),
            expect_ast("sin(x) / cos(x)").simplify()
        );

        assert_eq!(
            expect_ast("cot(x)").simplify().trig_substitue(),
            expect_ast("cos(x) / sin(x)").simplify()
        );

        assert_eq!(
            expect_ast("sec(x)").simplify().trig_substitue(),
            expect_ast("1 / cos(x)").simplify()
        );

        assert_eq!(
            expect_ast("csc(x)").simplify().trig_substitue(),
            expect_ast("1 / sin(x)").simplify()
        );

        assert_eq!(
            expect_ast("tan(x) * cot(x)").simplify().trig_substitue(),
            int(1)
        );
    }
}
