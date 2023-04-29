use super::{
    constant::Constant, factorial::Factorial, product::Product, sum::Sum, symbol::Symbol, Expr,
};
use num::{BigInt, BigRational, FromPrimitive};
use vec1::vec1;

#[derive(Debug, PartialEq, Eq)]
enum PowerKind {
    IntegerPower(IntegerPower),
    NonIntegerPower(NonIntegerPower),
}
impl PowerKind {
    fn as_exprs(self) -> (Expr, Expr) {
        match self {
            PowerKind::IntegerPower(power) => power.as_exprs(),
            PowerKind::NonIntegerPower(power) => power.as_exprs(),
        }
    }
}
impl From<IntegerPower> for PowerKind {
    fn from(value: IntegerPower) -> Self {
        Self::IntegerPower(value)
    }
}
impl From<NonIntegerPower> for PowerKind {
    fn from(value: NonIntegerPower) -> Self {
        Self::NonIntegerPower(value)
    }
}

#[derive(Debug, PartialEq, Eq)]
struct IntegerPower {
    base: IntegerPowerBase,
    exponent: BigInt,
}
impl IntegerPower {
    pub fn as_expr(self) -> Expr {
        Power::from(PowerKind::from(self)).as_expr()
    }

    pub fn as_exprs(self) -> (Expr, Expr) {
        let Self { base, exponent } = self;
        (base.as_expr(), Constant::from_int(exponent).as_expr())
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum IntegerPowerBase {
    Symbol(Symbol),
    Sum(Box<Sum>),
    Factorial(Box<Factorial>),
}
impl IntegerPowerBase {
    pub fn as_expr(self) -> Expr {
        match self {
            IntegerPowerBase::Symbol(symbol) => Expr::Symbol(symbol),
            IntegerPowerBase::Sum(sum) => Expr::Sum(*sum),
            IntegerPowerBase::Factorial(factorial) => Expr::Factorial(*factorial),
        }
    }
}
impl From<Symbol> for IntegerPowerBase {
    fn from(value: Symbol) -> Self {
        Self::Symbol(value)
    }
}
impl From<Sum> for IntegerPowerBase {
    fn from(value: Sum) -> Self {
        Self::Sum(Box::new(value))
    }
}
impl From<Factorial> for IntegerPowerBase {
    fn from(value: Factorial) -> Self {
        Self::Factorial(Box::new(value))
    }
}

#[derive(Debug, PartialEq, Eq)]
struct NonIntegerPower {
    base: Box<Expr>,
    power: Box<Expr>,
}
impl NonIntegerPower {
    pub fn as_expr(self) -> Expr {
        Power::from(PowerKind::from(self)).as_expr()
    }

    pub fn as_exprs(self) -> (Expr, Expr) {
        (*self.base, *self.power)
    }
}

enum NonIntegerPowerExponent {
    Fraction(BigRational),
    Sum(Sum),
    Product(Product),
    Power(Power),
    Factorial(Factorial),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Power {
    kind: PowerKind,
}
impl Power {
    pub fn unenforced_int(base: Expr, exponent: i128) -> Expr {
        Expr::Power(Power {
            kind: PowerKind::IntegerPower(IntegerPower {
                base: base.expect_integer_power_base(),
                exponent: BigInt::from_i128(exponent).unwrap(),
            }),
        })
    }

    pub fn unenforced(base: Expr, exponent: Expr) -> Expr {
        Expr::Power(Power {
            kind: PowerKind::NonIntegerPower(NonIntegerPower {
                base: Box::new(base),
                power: Box::new(exponent),
            }),
        })
    }

    pub fn new(base: Expr, exponent: Expr) -> Expr {
        match &exponent {
            Expr::Constant(constant) => {
                if constant.is_int() {
                    let int = constant.clone().expect_int();
                    match base {
                        Expr::Symbol(symbol) => IntegerPower {
                            base: symbol.into(),
                            exponent: int,
                        }
                        .as_expr(),
                        Expr::Constant(constant) => constant.power_int(int).as_expr(),
                        Expr::Sum(sum) => IntegerPower {
                            base: sum.into(),
                            exponent: int,
                        }
                        .as_expr(),
                        Expr::Product(product) => product.power_int(int),
                        Expr::Power(power) => {
                            let (base, base_exponent) = power.as_exprs();
                            Self::new(base, base_exponent.multiply(exponent))
                        }
                        Expr::Factorial(factorial) => IntegerPower {
                            base: factorial.into(),
                            exponent: int,
                        }
                        .as_expr(),
                    }
                } else {
                    NonIntegerPower {
                        base: Box::new(base),
                        power: Box::new(exponent),
                    }
                    .as_expr()
                }
            }
            _ => NonIntegerPower {
                base: Box::new(base),
                power: Box::new(exponent),
            }
            .as_expr(),
        }
    }

    pub fn negate(self) -> Expr {
        Product::new(Constant::neg_one(), vec1![self.into()])
    }

    pub fn as_expr(self) -> Expr {
        Expr::Power(self)
    }

    pub fn as_exprs(self) -> (Expr, Expr) {
        self.kind.as_exprs()
    }
}
impl From<PowerKind> for Power {
    fn from(value: PowerKind) -> Self {
        Self { kind: value }
    }
}
