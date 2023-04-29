use vec1::{vec1, Vec1};

use super::{
    constant::Constant, factorial::Factorial, power::Power, product::Product, symbol::Symbol, Expr,
};

#[derive(Debug, PartialEq, Eq)]
pub struct Sum {
    constant: Constant,
    addends: Vec1<Addend>,
}
impl Sum {
    pub(crate) fn unenforced(addends: Vec<Expr>) -> Expr {
        let mut iter = addends.into_iter();

        let constant = iter.next().unwrap().expect_constant();
        let mut new_addends: Vec1<Addend> = vec1![iter.next().unwrap().expect_addend()];

        for addend in iter {
            new_addends.push(addend.expect_addend());
        }

        Expr::Sum(Self {
            constant,
            addends: new_addends,
        })
    }

    pub fn new(constant: Constant, mut addends: Vec1<Addend>) -> Expr {
        if constant.is_zero() && addends.len() == 1 {
            return addends.swap_remove(0).unwrap().as_expr();
        } else {
            Self { constant, addends }.as_expr()
        }
    }

    pub fn negate(self) -> Expr {
        Product::new(Constant::neg_one(), vec1![self.into()])
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
            Expr::Symbol(symbol) => {
                self_addends.push(symbol.into());
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
                self_addends.push(product.into());
                (self_constant, self_addends)
            }
            Expr::Power(power) => {
                self_addends.push(power.into());
                (self_constant, self_addends)
            }
            Expr::Factorial(factorial) => {
                self_addends.push(factorial.into());
                (self_constant, self_addends)
            }
        };

        Self::new(constant, addends)
    }
}

#[derive(Debug, PartialEq, Eq)]
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
