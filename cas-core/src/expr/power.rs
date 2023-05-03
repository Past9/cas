use super::{
    constant::Constant, factorial::Factorial, product::Product, sum::Sum, symbol::Symbol, Expr,
};
use num::{BigInt, BigRational, FromPrimitive};
use vec1::vec1;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
struct NonIntegerPower {
    base: Box<Expr>,
    exponent: Box<NonIntegerPowerExponent>,
}
impl NonIntegerPower {
    pub fn as_expr(self) -> Expr {
        Power::from(PowerKind::from(self)).as_expr()
    }

    pub fn as_exprs(self) -> (Expr, Expr) {
        (*self.base, self.exponent.as_expr())
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum NonIntegerPowerExponent {
    Symbol(Symbol),
    Fraction(BigRational),
    Sum(Sum),
    Product(Product),
    Power(Power),
    Factorial(Factorial),
}
impl NonIntegerPowerExponent {
    pub fn as_expr(self) -> Expr {
        match self {
            NonIntegerPowerExponent::Symbol(symbol) => symbol.as_expr(),
            NonIntegerPowerExponent::Fraction(fraction) => Constant::from_frac(fraction).as_expr(),
            NonIntegerPowerExponent::Sum(sum) => sum.as_expr(),
            NonIntegerPowerExponent::Product(product) => product.as_expr(),
            NonIntegerPowerExponent::Power(power) => power.as_expr(),
            NonIntegerPowerExponent::Factorial(factorial) => factorial.as_expr(),
        }
    }
}
impl From<Symbol> for NonIntegerPowerExponent {
    fn from(value: Symbol) -> Self {
        Self::Symbol(value)
    }
}
impl From<Constant> for NonIntegerPowerExponent {
    fn from(value: Constant) -> Self {
        Self::Fraction(value.expect_frac())
    }
}
impl From<Sum> for NonIntegerPowerExponent {
    fn from(value: Sum) -> Self {
        Self::Sum(value)
    }
}
impl From<Product> for NonIntegerPowerExponent {
    fn from(value: Product) -> Self {
        Self::Product(value)
    }
}
impl From<Power> for NonIntegerPowerExponent {
    fn from(value: Power) -> Self {
        Self::Power(value)
    }
}
impl From<Factorial> for NonIntegerPowerExponent {
    fn from(value: Factorial) -> Self {
        Self::Factorial(value)
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
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
                exponent: Box::new(exponent.expect_non_integer_power_exponent()),
            }),
        })
    }

    pub fn new(base: Expr, exponent: Expr) -> Expr {
        if base.is_undefined() || exponent.is_undefined() {
            return Expr::Undefined;
        }

        if base.is_zero_const() {
            if exponent.is_pos_const() {
                return Constant::zero().as_expr();
            } else {
                return Expr::Undefined;
            }
        }

        if base.is_one_const() {
            return Constant::one().as_expr();
        }

        if exponent.is_zero_const() {
            if !base.is_zero_const() {
                return Constant::one().as_expr();
            } else {
                return Expr::Undefined;
            }
        }

        if exponent.is_one_const() {
            return base;
        }

        match &exponent {
            Expr::Constant(constant) => {
                if constant.is_int() {
                    let int = constant.clone().expect_int();
                    match base {
                        Expr::Undefined => Expr::Undefined,
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
                        exponent: Box::new(exponent.expect_non_integer_power_exponent()),
                    }
                    .as_expr()
                }
            }
            _ => NonIntegerPower {
                base: Box::new(base),
                exponent: Box::new(exponent.expect_non_integer_power_exponent()),
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
impl From<NonIntegerPower> for Power {
    fn from(value: NonIntegerPower) -> Self {
        PowerKind::from(value).into()
    }
}
impl From<IntegerPower> for Power {
    fn from(value: IntegerPower) -> Self {
        PowerKind::from(value).into()
    }
}

#[cfg(test)]
mod tests {
    use crate::expr::{unenforced_helpers::*, Expr};

    #[test]
    fn basic_power_transformation_3_15() {
        assert_eq!(
            Expr::from_src("(x ^ y) ^ 2"),
            pow(sym("x"), product([int(2), sym("y")]))
        )
    }

    #[test]
    fn basic_power_transformation_3_16() {
        assert_eq!(
            Expr::from_src("(x * y) ^ 2"),
            product([int(1), powi(sym("x"), 2), powi(sym("y"), 2)])
        )
    }

    #[test]
    fn basic_identity_transformation_3_23() {
        assert_eq!(Expr::from_src("0 ^ 2"), int(0));
        assert_eq!(Expr::from_src("0 ^ (1/2)"), int(0));
        assert_eq!(Expr::from_src("0 ^ x"), undefined());
        assert_eq!(Expr::from_src("0 ^ -x"), undefined());
        assert_eq!(Expr::from_src("0 ^ -2"), undefined());
        assert_eq!(Expr::from_src("0 ^ -(1/2)"), undefined());
    }

    #[test]
    fn basic_identity_transformation_3_24() {
        assert_eq!(Expr::from_src("1 ^ 2"), int(1));
        assert_eq!(Expr::from_src("1 ^ (x * y)"), int(1));
        assert_eq!(Expr::from_src("1 ^ -2"), int(1));
    }

    #[test]
    fn basic_identity_transformation_3_25() {
        assert_eq!(Expr::from_src("1 ^ 0"), int(1));
        assert_eq!(Expr::from_src("2 ^ 0"), int(1));
        assert_eq!(Expr::from_src("x ^ 0"), int(1));
        assert_eq!(Expr::from_src("0 ^ 0"), undefined());
    }

    #[test]
    fn basic_identity_transformation_3_26() {
        assert_eq!(Expr::from_src("0 ^ 1"), int(0));
        assert_eq!(Expr::from_src("1 ^ 1"), int(1));
        assert_eq!(Expr::from_src("-1 ^ 1"), int(-1));
        assert_eq!(Expr::from_src("-2 ^ 1"), int(-2));
        assert_eq!(Expr::from_src("x ^ 1"), sym("x"));
        assert_eq!(
            Expr::from_src("(x * y) ^ 1"),
            product([int(1), sym("x"), sym("y")])
        );
    }

    #[test]
    fn basic_numerical_transformation_3() {
        assert_eq!(Expr::from_src("2 ^ 2"), int(4));
        assert_eq!(Expr::from_src("(1/2) ^ 2"), frac(1, 4));
        assert_eq!(Expr::from_src("-2 ^ 2"), int(4));
        assert_eq!(Expr::from_src("(-1/2) ^ 2"), frac(1, 4));
        assert_eq!(Expr::from_src("2 ^ -2"), frac(1, 4));
        assert_eq!(Expr::from_src("(1/2) ^ -2"), int(4));
        assert_eq!(Expr::from_src("-2 ^ -2"), frac(1, 4));
        assert_eq!(Expr::from_src("(-1/2) ^ -2"), int(4));

        assert_eq!(Expr::from_src("2 ^ 3"), int(8));
        assert_eq!(Expr::from_src("(1/2) ^ 3"), frac(1, 8));
        assert_eq!(Expr::from_src("-2 ^ 3"), int(-8));
        assert_eq!(Expr::from_src("(-1/2) ^ 3"), frac(-1, 8));
        assert_eq!(Expr::from_src("2 ^ -3"), frac(1, 8));
        assert_eq!(Expr::from_src("(1/2) ^ -3"), int(8));
        assert_eq!(Expr::from_src("-2 ^ -3"), frac(-1, 8));
        assert_eq!(Expr::from_src("(-1/2) ^ -3"), int(-8));
    }

    #[test]
    fn undefined_transformation() {
        assert_eq!(Expr::from_src("undefined ^ 2"), undefined());
        assert_eq!(Expr::from_src("undefined ^ -2"), undefined());
        assert_eq!(Expr::from_src("undefined ^ 1/2"), undefined());
        assert_eq!(Expr::from_src("undefined ^ -1/2"), undefined());
        assert_eq!(Expr::from_src("undefined ^ 0"), undefined());
        assert_eq!(Expr::from_src("undefined ^ x"), undefined());
        assert_eq!(Expr::from_src("undefined ^ (x * y)"), undefined());
        assert_eq!(Expr::from_src("undefined ^ (x + y)"), undefined());

        assert_eq!(Expr::from_src("2 ^ undefined"), undefined());
        assert_eq!(Expr::from_src("-2 ^ undefined"), undefined());
        assert_eq!(Expr::from_src("1/2 ^ undefined"), undefined());
        assert_eq!(Expr::from_src("-1/2 ^ undefined"), undefined());
        assert_eq!(Expr::from_src("0 ^ undefined"), undefined());
        assert_eq!(Expr::from_src("x ^ undefined"), undefined());
        assert_eq!(Expr::from_src("(x * y) ^ undefined"), undefined());
        assert_eq!(Expr::from_src("(x + y) ^ undefined"), undefined());
    }
}
