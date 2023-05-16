use std::{borrow::Borrow, collections::BTreeSet};

use crate::ast::{
    helpers::{int, pow, prd, quo, sum},
    Ast,
};

#[derive(PartialEq, Debug)]
pub struct NumDen {
    pub num: Ast,
    pub den: Ast,
}
impl NumDen {
    pub fn new(num: Ast, den: Ast) -> Self {
        Self { num, den }
    }
}

impl Ast {
    pub fn num_den(self) -> Option<NumDen> {
        match self {
            Ast::Und => None,

            // ND-1
            Ast::Frc(frc) => Some(NumDen::new(
                Ast::Int(frc.numer().clone()),
                Ast::Int(frc.denom().clone()),
            )),

            // ND-2
            Ast::Pow(base, exp) => {
                if exp.is_neg_const() {
                    Some(NumDen::new(
                        int(1),
                        pow(Ast::Pow(base, exp), int(-1)).simplify(),
                    ))
                } else {
                    Some(NumDen::new(Ast::Pow(base, exp), int(1)))
                }
            }

            // ND-3
            Ast::Prd(operands) => {
                let mut iter = operands.into_iter();
                let first = iter.next().unwrap();
                let rest = Ast::Prd(iter.collect()).simplify();

                let (first_num, first_den) = {
                    if let Some(NumDen { num, den }) = first.num_den() {
                        (num, den)
                    } else {
                        return None;
                    }
                };

                let (rest_num, rest_den) = {
                    if let Some(NumDen { num, den }) = rest.num_den() {
                        (num, den)
                    } else {
                        return None;
                    }
                };

                Some(NumDen::new(
                    prd([first_num, rest_num]).simplify(),
                    prd([first_den, rest_den]).simplify(),
                ))
            }

            // ND-4
            _ => Some(NumDen::new(self, int(1))),
        }
    }

    pub fn is_gre<T: Borrow<Ast>, I: IntoIterator<Item = T> + Clone>(&self, variables: I) -> bool {
        if let Some(NumDen { num, den }) = self.clone().num_den() {
            num.is_gpe(variables.clone()) && den.is_gpe(variables.clone())
        } else {
            false
        }
    }

    pub fn vars_gre(&self) -> BTreeSet<Ast> {
        if let Some(NumDen { num, den }) = self.clone().num_den() {
            let mut vars = num.vars_gpe();
            vars.extend(den.vars_gpe());
            vars
        } else {
            BTreeSet::new()
        }
    }

    pub fn rationalize(self) -> Ast {
        match self {
            Ast::Pow(base, exp) => pow(base.rationalize(), *exp).simplify(),
            Ast::Prd(operands) => {
                let mut iter = operands.into_iter();
                let first = iter.next().unwrap().simplify();
                let rest = Ast::Prd(iter.collect()).simplify();
                prd([first.rationalize(), rest.rationalize()]).simplify()
            }
            Ast::Sum(operands) => {
                let mut iter = operands.into_iter();
                let first = iter.next().unwrap().simplify();
                let rest = Ast::Sum(iter.collect()).simplify();
                Self::rationalize_sum(first.rationalize(), rest.rationalize())
            }

            _ => self,
        }
    }

    pub(self) fn rationalize_sum(u: Ast, v: Ast) -> Self {
        let (m, r) = if let Some(NumDen { num, den }) = u.clone().num_den() {
            (num, den)
        } else {
            return Ast::Und;
        };

        let (n, s) = if let Some(NumDen { num, den }) = v.clone().num_den() {
            (num, den)
        } else {
            return Ast::Und;
        };

        if r.is_int_one() && s.is_int_one() {
            sum([u, v]).simplify()
        } else {
            quo(
                Self::rationalize_sum(
                    prd([m, s.clone()]).simplify(),
                    prd([n, r.clone()]).simplify(),
                ),
                prd([r, s]).simplify(),
            )
            .simplify()
        }
    }

    pub fn rational_expand(self) -> Self {
        if let Some(NumDen { num, den }) = self.rationalize().num_den() {
            let den = den.algebraic_expand().simplify();
            if den.is_int_zero() {
                Ast::Und
            } else {
                quo(num.algebraic_expand(), den).simplify()
            }
        } else {
            Ast::Und
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::{
        ast::{
            helpers::{int, pow, sym},
            Ast,
        },
        helpers::expect_ast,
        rational::NumDen,
    };

    #[test]
    fn gets_num_and_den() {
        assert_eq!(
            expect_ast("(2/3) * ((x * (x + 1)) / (x + 2)) * y^n")
                .simplify()
                .num_den(),
            Some(NumDen::new(
                expect_ast("2 * x * (x + 1) * y ^ n").simplify(),
                expect_ast("3 * (x + 2)").simplify(),
            ))
        );
    }

    #[test]
    fn identifies_gre() {
        assert!(expect_ast("(x^2 + 1) / (2 * x + 3)")
            .simplify()
            .is_gre(&[sym("x")]));

        assert!(!expect_ast("(1 / x) + (1 / y)")
            .simplify()
            .is_gre(&[sym("x"), sym("y")]));
    }

    #[test]
    fn gets_rational_variables() {
        assert_eq!(
            expect_ast("(2 * x + 3 * y) / (z + 4)")
                .simplify()
                .vars_gre(),
            BTreeSet::from([sym("x"), sym("y"), sym("z")])
        );

        assert_eq!(
            expect_ast("1 / x + 1 / y").simplify().vars_gre(),
            BTreeSet::from([pow(sym("x"), int(-1)), pow(sym("y"), int(-1))])
        );
    }

    #[test]
    fn rationalizes_expression() {
        assert_eq!(
            expect_ast("(1 + 1 / x)^2").simplify().rationalize(),
            expect_ast("(x + 1)^2 / x^2").simplify()
        );

        assert_eq!(
            expect_ast("(1 + 1 / x)^(1/2)").simplify().rationalize(),
            expect_ast("((x + 1) / x)^(1/2)").simplify()
        );

        assert_eq!(
            expect_ast("m/r + n/s").simplify().rationalize(),
            expect_ast("(m * s + n * r) / (r * s)").simplify()
        );

        assert_eq!(
            expect_ast("1 / ((1 + 1/x)^(1/2)) + (1 + 1/x)^(3/2)")
                .simplify()
                .rationalize(),
            expect_ast("(x^2 + (x + 1)^2) / (x^2 * ((x + 1) / x) ^ (1/2))").simplify()
        );

        assert_eq!(
            expect_ast("a/b + c/d + e/f").simplify().rationalize(),
            expect_ast("(a * d * f + b * (c * f + d * e)) / (b * d * f)").simplify()
        );

        assert_eq!(
            expect_ast("1 / (1/a + c/(a * b)) + (a*b*c + a*c^2) / (b+c)^2 - a")
                .simplify()
                .rationalize(),
            expect_ast(
                "((b+c)^2*a^2*b + (a*b*c + a*c^2 - a*(b+c)^2) * (a*b + c*a)) / ((a*b + c*a) * (b+c)^2)"
            )
            .simplify()
        );
    }

    #[test]
    fn does_rational_expansion() {
        // Denominator is 0, so expression is undefined
        assert_eq!(
            expect_ast("1 / (1/a + c/(a * b)) + (a*b*c + a*c^2) / (b+c)^2 - a")
                .simplify()
                .rational_expand(),
            int(0)
        );
    }
}
