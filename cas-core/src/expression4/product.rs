use vec1::vec1;

use num::BigInt;
use vec1::Vec1;

use super::{
    constant::Constant, factorial::Factorial, power::Power, sum::Sum, symbol::Symbol, Expr,
};

#[derive(Debug, PartialEq, Eq)]
pub struct Product {
    constant: Constant,
    factors: Vec1<Factor>,
}
impl Product {
    pub(crate) fn unenforced(factors: Vec<Expr>) -> Expr {
        let mut iter = factors.into_iter();

        let constant = iter.next().unwrap().expect_constant();
        let mut new_factors: Vec1<Factor> = vec1![iter.next().unwrap().expect_factor()];

        for factor in iter {
            new_factors.push(factor.expect_factor());
        }

        Expr::Product(Self {
            constant,
            factors: new_factors,
        })
    }

    pub fn new(constant: Constant, mut factors: Vec1<Factor>) -> Expr {
        if constant.is_zero() {
            Constant::zero().as_expr()
        } else if constant.is_one() && factors.len() == 1 {
            factors.swap_remove(0).unwrap().as_expr()
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
            Expr::Symbol(symbol) => {
                self_factors.push(symbol.into());
                (self_constant, self_factors)
            }
            Expr::Constant(constant) => (self_constant.multiply(constant), self_factors),
            Expr::Sum(sum) => {
                self_factors.push(sum.into());
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

                for addend in std::iter::once(rhs_constant.as_expr())
                    .chain(rhs_factors.into_iter().map(Factor::as_expr))
                {
                    lhs = lhs.add(addend);
                }

                return lhs;
            }
            Expr::Power(power) => {
                self_factors.push(power.into());
                (self_constant, self_factors)
            }
            Expr::Factorial(factorial) => {
                self_factors.push(factorial.into());
                (self_constant, self_factors)
            }
        };

        Self::new(constant, factors)
    }

    pub fn power_int(self, exponent: BigInt) -> Expr {
        let Self { constant, factors } = self;

        let mut expr = constant.power_int(exponent).as_expr();

        for factor in factors.into_iter() {
            expr = expr.multiply(factor.as_expr());
        }

        expr
    }
}

#[derive(Debug, PartialEq, Eq)]
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
