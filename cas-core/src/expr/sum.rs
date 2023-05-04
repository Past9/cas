use vec1::{vec1, Vec1};

use crate::operands;

use super::{
    constant::Constant, factorial::Factorial, power::Power, product::Product, symbol::Symbol, Expr,
    Operands,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Sum {
    constant: Constant,
    addends: Operands<Addend>,
}
impl Sum {
    pub(crate) fn unenforced(addends: Vec<Expr>) -> Expr {
        let mut iter = addends.into_iter();

        let constant = iter.next().unwrap().expect_constant();
        let mut new_addends: Operands<Addend> = operands![iter.next().unwrap().expect_addend()];

        for addend in iter {
            new_addends.insert(addend.expect_addend());
        }

        Expr::Sum(Self {
            constant,
            addends: new_addends,
        })
    }

    pub(crate) fn new(constant: Constant, addends: Operands<Addend>) -> Expr {
        if constant.is_zero() && addends.len() == 1 {
            return addends.take_first().as_expr();
        } else {
            Self { constant, addends }.as_expr()
        }
    }

    pub fn negate(self) -> Expr {
        Product::new(Constant::neg_one(), operands![self.into()])
    }

    pub fn as_expr(self) -> Expr {
        Expr::Sum(self)
    }

    pub fn add(self, rhs: Expr) -> Expr {
        let Self {
            constant: self_constant,
            addends: mut self_addends,
        } = self;

        let (constant, addends) = match rhs {
            Expr::Undefined => {
                return Expr::Undefined;
            }
            Expr::Symbol(symbol) => {
                self_addends.insert(symbol.into());
                (self_constant, self_addends)
            }
            Expr::Constant(constant) => (self_constant.add(constant), self_addends),
            Expr::Sum(sum) => {
                let mut lhs = Self {
                    constant: self_constant,
                    addends: self_addends,
                }
                .as_expr();

                let Self {
                    constant: rhs_constant,
                    addends: rhs_addends,
                } = sum;

                for addend in std::iter::once(rhs_constant.as_expr())
                    .chain(rhs_addends.into_iter().map(Addend::as_expr))
                {
                    lhs = lhs.add(addend);
                }

                return lhs;
            }
            Expr::Product(product) => {
                self_addends.insert(product.into());
                (self_constant, self_addends)
            }
            Expr::Power(power) => {
                self_addends.insert(power.into());
                (self_constant, self_addends)
            }
            Expr::Factorial(factorial) => {
                self_addends.insert(factorial.into());
                (self_constant, self_addends)
            }
        };

        Self::new(constant, addends)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Addend {
    Symbol(Symbol),
    Product(Product),
    Power(Power),
    Factorial(Factorial),
}
impl Addend {
    pub fn as_expr(self) -> Expr {
        match self {
            Self::Symbol(symbol) => Expr::Symbol(symbol),
            Self::Product(product) => Expr::Product(product),
            Self::Power(power) => Expr::Power(power),
            Self::Factorial(factorial) => Expr::Factorial(factorial),
        }
    }
}
impl From<Symbol> for Addend {
    fn from(value: Symbol) -> Self {
        Addend::Symbol(value)
    }
}
impl From<Product> for Addend {
    fn from(value: Product) -> Self {
        Addend::Product(value)
    }
}
impl From<Power> for Addend {
    fn from(value: Power) -> Self {
        Addend::Power(value)
    }
}
impl From<Factorial> for Addend {
    fn from(value: Factorial) -> Self {
        Addend::Factorial(value)
    }
}

#[cfg(test)]
mod tests {
    use crate::expr::{
        test_helpers::{int, sum, sym},
        Expr,
    };

    #[test]
    fn combines_sums() {
        assert_eq!(
            Expr::from_src("2 + x + 3 + y + z"),
            sum([int(5), sym("x"), sym("y"), sym("z")])
        );
    }
}
