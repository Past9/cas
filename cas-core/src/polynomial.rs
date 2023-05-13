use crate::ast::{helpers::int, Ast};

impl Ast {
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
}
