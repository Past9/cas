use crate::ast::{
    helpers::{int, pow, quo, sum},
    Ast,
};

use num::{bigint::ToBigInt, BigInt, BigUint, Zero};
use std::collections::BTreeSet;

pub struct GpeCoefficient {
    pub coefficient: Ast,
    pub degree: BigUint,
}
impl GpeCoefficient {
    pub fn new(coefficient: Ast, degree: BigUint) -> Self {
        Self {
            coefficient,
            degree,
        }
    }
}

impl Ast {
    /// Returns all the general variable expressions for which `self` is a
    /// generalized polynomial expression.
    pub fn variables(&self) -> BTreeSet<Ast> {
        match self {
            // VAR-1
            Ast::Und | Ast::Int(_) | Ast::Frc(_) => BTreeSet::new(),

            // VAR-2
            pow @ Ast::Pow(base, exp) => {
                if exp.is_int() && **exp > int(1) {
                    BTreeSet::from_iter(std::iter::once((**base).clone()))
                } else {
                    BTreeSet::from_iter(std::iter::once(pow.clone()))
                }
            }

            // VAR-3
            Ast::Sum(operands) => {
                let mut set = BTreeSet::new();

                for operand in operands.iter() {
                    set.extend(operand.variables());
                }

                set
            }

            // VAR-4
            Ast::Prd(operands) => {
                let mut set = BTreeSet::new();

                for operand in operands.iter() {
                    if operand.is_sum() {
                        set.insert(operand.clone());
                    } else {
                        set.extend(operand.variables());
                    }
                }

                set
            }

            other @ (Ast::Sym(_)
            | Ast::Neg(_)
            | Ast::Fac(_)
            | Ast::Dif(_, _)
            | Ast::Quo(_, _)
            | Ast::Fun(_, _)) => BTreeSet::from_iter(std::iter::once(other.clone())),
        }
    }

    /// Returns whether `self` is a generalized monomial expression in
    /// `variables`.
    pub fn is_monomial_gpe(&self, variables: &[Ast]) -> bool {
        if variables.contains(self) {
            return true;
        } else if let Ast::Pow(base, exp) = self {
            if variables.contains(base) && exp.is_int() && **exp > int(1) {
                return true;
            }
        } else if let Ast::Prd(operands) = self {
            if operands.iter().any(|op| !op.is_monomial_gpe(variables)) {
                return false;
            } else {
                return true;
            }
        }

        variables.iter().all(|var| self.is_free_of(var))
    }

    /// Returns the degree of the generalized monomial expression in `variables`.
    /// If `self` is not a monomial in `variables`, returns `Ast::Und`.
    pub fn monomial_degree_gpe(&self, variables: &[Ast]) -> Ast {
        if variables.contains(self) {
            return int(1);
        } else if let Ast::Pow(base, exp) = self {
            if variables.contains(base) && exp.is_int() && **exp > int(1) {
                return (**exp).clone();
            }
        } else if let Ast::Prd(operands) = self {
            let mut degree: BigInt = 0.into();
            for operand in operands.iter() {
                match operand.monomial_degree_gpe(variables) {
                    Ast::Int(deg) => degree += deg,
                    _ => {
                        return Ast::Und;
                    }
                }
            }

            return Ast::Int(degree);
        }

        if variables.iter().all(|var| self.is_free_of(var)) {
            return int(0);
        } else {
            return Ast::Und;
        }
    }

    /// Returns whether `self` is a generalized polynomial expression in
    /// `variables`.
    pub fn is_gpe(&self, variables: &[Ast]) -> bool {
        if !self.is_sum() {
            self.is_monomial_gpe(variables)
        } else {
            if variables.contains(self) {
                return true;
            }

            match self {
                Ast::Sum(ops) => ops.iter().all(|op| op.is_monomial_gpe(variables)),
                _ => unreachable!(),
            }
        }
    }

    /// Returns the degree of the generalized polynomial expression in `variables`.
    /// If `self` is not a polynomial in `variables`, returns `Ast::Und`.
    pub fn degree_gpe(&self, variables: &[Ast]) -> Ast {
        if !self.is_sum() {
            self.monomial_degree_gpe(variables)
        } else {
            if variables.contains(self) {
                return int(1);
            }

            match self {
                Ast::Sum(ops) => {
                    let mut max: BigInt = 0.into();
                    for op in ops.iter() {
                        let deg = op.monomial_degree_gpe(variables);
                        if let Ast::Int(deg) = deg {
                            if deg > max {
                                max = deg;
                            }
                        } else {
                            return Ast::Und;
                        }
                    }

                    Ast::Int(max)
                }
                _ => unreachable!(),
            }
        }
    }

    pub fn coefficient_monomial_gpe(&self, variable: &Ast) -> Option<GpeCoefficient> {
        if self == variable {
            return Some(GpeCoefficient::new(int(1), 1u32.into()));
        } else if let Ast::Pow(base, exp) = self {
            if &**base == variable && exp.is_int() && **exp > int(1) {
                return Some(GpeCoefficient::new(int(1), exp.expect_uint()));
            }
        } else if let Ast::Prd(operands) = self {
            let mut out_degree: BigUint = 0u32.into();
            let mut out_coefficient = self.clone();
            for operand in operands.iter() {
                let gpe_coefficient = operand.coefficient_monomial_gpe(variable);
                if let Some(GpeCoefficient { degree, .. }) = gpe_coefficient {
                    if !degree.is_zero() {
                        out_degree = degree;
                        out_coefficient = quo(
                            self.clone(),
                            pow(variable.clone(), Ast::Int(out_degree.to_bigint().unwrap())),
                        )
                        .simplify();
                    }
                } else {
                    return None;
                }
            }

            return Some(GpeCoefficient::new(out_coefficient, out_degree));
        }

        if self.is_free_of(&variable) {
            Some(GpeCoefficient::new(self.clone(), 0u32.into()))
        } else {
            None
        }
    }

    pub fn coefficient_gpe(&self, variable: &Ast, monomial_index: BigUint) -> Ast {
        if !self.is_sum() {
            let mono_co = self.coefficient_monomial_gpe(variable);
            match mono_co {
                Some(co) => {
                    if monomial_index == co.degree {
                        return co.coefficient;
                    } else {
                        return int(0);
                    }
                }
                None => {
                    return Ast::Und;
                }
            }
        } else {
            if self == variable {
                if monomial_index == 1u32.into() {
                    return int(1);
                } else {
                    return int(0);
                }
            }

            let mut co = int(0);
            for operand in self.iter_operands() {
                match operand.coefficient_monomial_gpe(variable) {
                    Some(gpe_co) => {
                        if gpe_co.degree == monomial_index {
                            co = sum([co, gpe_co.coefficient]).simplify();
                        }
                    }
                    None => {
                        return Ast::Und;
                    }
                }
            }

            co
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::{ast::helpers::*, helpers::expect_ast};

    #[test]
    fn identifies_monomial_gpe() {
        assert!(expect_ast("a * x ^ 2 * y ^ 2")
            .simplify()
            .is_monomial_gpe(&[sym("x"), sym("y")]));

        assert!(!expect_ast("x ^ 2 + y ^ 2")
            .simplify()
            .is_monomial_gpe(&[sym("x"), sym("y")]));

        assert!(!expect_ast("x / y")
            .simplify()
            .is_monomial_gpe(&[sym("x"), sym("y")]));

        assert!(expect_ast("(a + b)")
            .simplify()
            .is_monomial_gpe(&[sum([sym("a"), sym("b")])]));

        assert!(expect_ast("(a + b) ^ 2")
            .simplify()
            .is_monomial_gpe(&[sum([sym("a"), sym("b")])]));
    }

    #[test]
    fn identifies_polynomial_gpe() {
        assert!(expect_ast("x ^ 2 + y ^ 2")
            .simplify()
            .is_gpe(&[sym("x"), sym("y")]));

        assert!(expect_ast("sin(x) ^ 2 + 2 * sin(x) + 3")
            .simplify()
            .is_gpe(&[fun("sin", [sym("x")])]));

        assert!(!expect_ast("(x / y) + (2 * y)")
            .simplify()
            .is_gpe(&[sym("x"), sym("y")]));

        assert!(!expect_ast("(x + 1) * (x + 3)")
            .simplify()
            .is_gpe(&[sym("x")]));

        assert!(expect_ast("a + b")
            .simplify()
            .is_gpe(&[sum([sym("a"), sym("b")])]));

        assert!(expect_ast("(a + b) ^ 2")
            .simplify()
            .is_gpe(&[sum([sym("a"), sym("b")])]));
    }

    #[test]
    fn gets_variables() {
        assert_eq!(
            expect_ast("x ^ 3 + 3 * x ^ 2 * y + 3 * x * y ^ 2 + y ^ 3")
                .simplify()
                .variables(),
            BTreeSet::from([sym("x"), sym("y")])
        );

        assert_eq!(
            expect_ast("3 * x * (x + 1) * y ^ 2 * z ^ n")
                .simplify()
                .variables(),
            BTreeSet::from([
                sym("x"),
                sum([int(1), sym("x")]),
                sym("y"),
                pow(sym("z"), sym("n"))
            ])
        );

        assert_eq!(
            expect_ast("a * sin(x) ^ 2 + 2 * b * sin(x) + 3 * c")
                .simplify()
                .variables(),
            BTreeSet::from([sym("a"), sym("b"), sym("c"), fun("sin", [sym("x")])])
        );

        assert_eq!(expect_ast("1/2").simplify().variables(), BTreeSet::new());

        assert_eq!(
            expect_ast("2 ^ (1/2) * x ^ 2 + 3 ^ (1/2) * x + 5 ^ (1/2)")
                .simplify()
                .variables(),
            BTreeSet::from([
                sym("x"),
                pow(int(2), frc(1, 2)),
                pow(int(3), frc(1, 2)),
                pow(int(5), frc(1, 2)),
            ])
        );
    }

    #[test]
    fn gets_monomial_degree() {
        assert_eq!(
            expect_ast("3 * w * x^2 * y^3 * z^4")
                .simplify()
                .monomial_degree_gpe(&[sym("x"), sym("z")]),
            int(6)
        );
    }

    #[test]
    fn gets_polynomial_degree() {
        assert_eq!(
            expect_ast("3 * w * x^2 * y^3 * z^4")
                .simplify()
                .degree_gpe(&[sym("x"), sym("z")]),
            int(6)
        );

        assert_eq!(
            expect_ast("a * x^2 + b * x + c")
                .simplify()
                .degree_gpe(&[sym("x")]),
            int(2)
        );

        assert_eq!(
            expect_ast("a * sin(x)^2 + b * sin(x) + c")
                .simplify()
                .degree_gpe(&[fun("sin", [sym("x")])]),
            int(2)
        );

        assert_eq!(
            expect_ast("2 * x^2 * y * z^3 + w * x * z^6")
                .simplify()
                .degree_gpe(&[sym("x"), sym("z")]),
            int(7)
        );
    }

    #[test]
    fn total_degree() {
        let ast = expect_ast("a * x^2 + b * x + c").simplify();
        let vars = ast.variables();

        assert_eq!(
            vars,
            BTreeSet::from([sym("a"), sym("b"), sym("c"), sym("x"),])
        );

        assert_eq!(
            ast.degree_gpe(&vars.into_iter().collect::<Vec<_>>()),
            int(3)
        );
    }

    #[test]
    fn gets_coefficient_gpe() {
        assert_eq!(
            expect_ast("a * x^2 + b * x + c")
                .simplify()
                .coefficient_gpe(&sym("x"), 2u32.into()),
            sym("a")
        );

        assert_eq!(
            expect_ast("3 * x * y^2 + 5 * x^2 * y + 7 * x + 9")
                .simplify()
                .coefficient_gpe(&sym("x"), 1u32.into()),
            // 3 * y^2 + 7
            sum([int(7), prd([int(3), pow(sym("y"), int(2))])])
        );

        assert_eq!(
            expect_ast("3 * x * y^2 + 5 * x^2 * y + 7 * x + 9")
                .simplify()
                .coefficient_gpe(&sym("x"), 3u32.into()),
            int(0)
        );

        assert_eq!(
            expect_ast("(3 * sin(x)) * x^2 + (2 * ln(x)) * x + 4")
                .simplify()
                .coefficient_gpe(&sym("x"), 2u32.into()),
            und()
        );
    }
}
