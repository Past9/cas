use std::collections::{BTreeSet, HashSet};

use crate::ast::{helpers::int, Ast};

impl Ast {
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

    pub fn is_polynomial_gpe(&self, variables: &[Ast]) -> bool {
        if !self.is_sum() {
            self.is_monomial_gpe(variables)
        } else {
            if variables.contains(self) {
                return true;
            }

            match self {
                Ast::Und => false,
                sym @ Ast::Sym(_) => sym.is_monomial_gpe(variables),
                int @ Ast::Int(_) => int.is_monomial_gpe(variables),
                frc @ Ast::Frc(_) => frc.is_monomial_gpe(variables),
                Ast::Neg(op) => op.is_monomial_gpe(variables),
                Ast::Fac(op) => op.is_monomial_gpe(variables),
                Ast::Prd(ops) => ops.iter().all(|op| op.is_monomial_gpe(variables)),
                Ast::Dif(l, r) => l.is_monomial_gpe(variables) && r.is_monomial_gpe(variables),
                Ast::Sum(ops) => ops.iter().all(|op| op.is_monomial_gpe(variables)),
                Ast::Quo(l, r) => l.is_monomial_gpe(variables) && r.is_monomial_gpe(variables),
                Ast::Pow(base, exp) => {
                    base.is_monomial_gpe(variables) && exp.is_monomial_gpe(variables)
                }
                Ast::Fun(_, args) => args.iter().all(|arg| arg.is_monomial_gpe(variables)),
            }
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
    }

    #[test]
    fn identifies_polynomial_gpe() {
        assert!(expect_ast("x ^ 2 + y ^ 2")
            .simplify()
            .is_polynomial_gpe(&[sym("x"), sym("y")]));

        assert!(expect_ast("sin(x) ^ 2 + 2 * sin(x) + 3")
            .simplify()
            .is_polynomial_gpe(&[fun("sin", [sym("x")])]));

        assert!(!expect_ast("(x / y) + (2 * y)")
            .simplify()
            .is_polynomial_gpe(&[sym("x"), sym("y")]));

        assert!(!expect_ast("(x + 1) * (x + 3)")
            .simplify()
            .is_polynomial_gpe(&[sym("x")]));
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
}
