use vec1::vec1;

use num::{BigInt, Zero};
use vec1::Vec1;

use crate::operands;

use super::{
    constant::Constant, factorial::Factorial, power::Power, sum::Sum, symbol::Symbol, Expr,
    OperandHelpers, Operands,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Product {
    constant: Constant,
    factors: Operands<Factor>,
}
impl Product {
    pub(crate) fn unenforced(factors: Vec<Expr>) -> Expr {
        let mut iter = factors.into_iter();

        let constant = iter.next().unwrap().expect_constant();
        let mut new_factors: Operands<Factor> = operands![iter.next().unwrap().expect_factor()];

        for factor in iter {
            new_factors.insert(factor.expect_factor());
        }

        Expr::Product(Self {
            constant,
            factors: new_factors,
        })
    }

    pub(crate) fn new(constant: Constant, factors: Operands<Factor>) -> Expr {
        if constant.is_zero() {
            Constant::zero().as_expr()
        } else if constant.is_one() && factors.len() == 1 {
            factors.into_iter().next().unwrap().as_expr()
        } else {
            Self { constant, factors }.as_expr()
        }
    }

    pub fn negate(self) -> Self {
        Self {
            constant: self.constant.negate(),
            factors: self.factors,
        }
    }

    pub fn as_expr(self) -> Expr {
        Expr::Product(self)
    }

    pub fn multiply(self, rhs: Expr) -> Expr {
        let Self {
            constant: self_constant,
            factors: mut self_factors,
        } = self;

        let (constant, factors) = match rhs {
            Expr::Undefined => {
                return Expr::Undefined;
            }
            Expr::Symbol(symbol) => {
                self_factors.multiply_symbol(&symbol);
                (self_constant, self_factors)
            }
            Expr::Constant(constant) => (self_constant.multiply(constant), self_factors),
            Expr::Sum(sum) => {
                self_factors.insert(sum.into());
                (self_constant, self_factors)
            }
            Expr::Product(product) => {
                let mut lhs = Self {
                    constant: self_constant,
                    factors: self_factors,
                }
                .as_expr();

                let Self {
                    constant: rhs_constant,
                    factors: rhs_factors,
                } = product;

                for factor in std::iter::once(rhs_constant.as_expr())
                    .chain(rhs_factors.into_iter().map(Factor::as_expr))
                {
                    lhs = lhs.multiply(factor);
                }

                return lhs;
            }
            Expr::Power(power) => {
                self_factors.insert(power.into());
                (self_constant, self_factors)
            }
            Expr::Factorial(factorial) => {
                self_factors.insert(factorial.into());
                (self_constant, self_factors)
            }
        };

        Self::new(constant, factors)
    }

    pub fn power_int(self, exponent: BigInt) -> Expr {
        let Self { constant, factors } = self;

        let mut expr = constant.power_int(exponent.clone()).as_expr();

        for factor in factors.into_iter() {
            expr = expr.multiply(Power::new(
                factor.as_expr(),
                Constant::from_int(exponent.clone()).as_expr(),
            ));
        }

        expr
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Factor {
    Symbol(Symbol),
    Sum(Sum),
    Power(Power),
    Factorial(Factorial),
}
impl Factor {
    pub fn as_expr(self) -> Expr {
        match self {
            Self::Symbol(symbol) => Expr::Symbol(symbol),
            Self::Sum(sum) => Expr::Sum(sum),
            Self::Power(power) => Expr::Power(power),
            Self::Factorial(factorial) => Expr::Factorial(factorial),
        }
    }

    pub fn try_from_expr(expr: Expr) -> Option<Self> {
        match expr {
            Expr::Symbol(symbol) => Some(symbol.into()),
            Expr::Sum(sum) => Some(sum.into()),
            Expr::Power(power) => Some(power.into()),
            Expr::Factorial(factorial) => Some(factorial.into()),
            _ => None,
        }
    }
}
impl From<Symbol> for Factor {
    fn from(value: Symbol) -> Self {
        Factor::Symbol(value)
    }
}
impl From<Sum> for Factor {
    fn from(value: Sum) -> Self {
        Factor::Sum(value)
    }
}
impl From<Power> for Factor {
    fn from(value: Power) -> Self {
        Factor::Power(value)
    }
}
impl From<Factorial> for Factor {
    fn from(value: Factorial) -> Self {
        Factor::Factorial(value)
    }
}

#[cfg(test)]
mod tests {
    use crate::expr::{test_helpers::*, Expr};

    #[test]
    pub fn basic_associative_transformation() {
        test_src(
            "(w * x) * (y * z)",
            product([int(1), sym("w"), sym("x"), sym("y"), sym("z")]),
        )
    }

    #[test]
    pub fn basic_commutative_transformation() {
        test_src("x * y", product([int(1), sym("x"), sym("y")]));
        test_src("x * y", product([int(1), sym("y"), sym("x")]));
        test_src("y * x", product([int(1), sym("x"), sym("y")]));
        test_src("y * x", product([int(1), sym("y"), sym("x")]));
    }

    #[test]
    pub fn basic_power_transformation_1() {
        //test_src("x * x", powi(sym("x"), 2));
        //test_src("2 * x * x", product([int(2), powi(sym("x"), 2)]));
        //test_src("2 * x * x * x", product([int(2), powi(sym("x"), 3)]));
        test_src("x * x * x", powi(sym("x"), 3));
        /*
        test_src("x ^ 1 * x ^ 1", powi(sym("x"), 2));
        test_src("x ^ 1 * x ^ 2", powi(sym("x"), 3));
        test_src("x ^ 0 * x ^ 1", sym("x"));
        test_src("x ^ 0 * x ^ 2", powi(sym("x"), 2));
        test_src("x ^ 2 * x ^ 3", powi(sym("x"), 6));
        test_src("x ^ 1 * x ^ -1", int(0));
        test_src("x ^ 1 * x ^ -2", powi(sym("x"), -1));
        test_src("x ^ -1 * x ^ -2", powi(sym("x"), -3));
        */
    }
}
