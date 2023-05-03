mod constant;
mod factorial;
mod power;
mod product;
mod sum;
mod symbol;

use crate::operands;
use std::collections::{btree_set::IntoIter, BTreeSet};

use self::{
    constant::Constant,
    factorial::Factorial,
    power::{IntegerPowerBase, NonIntegerPowerExponent, Power},
    product::{Factor, Product},
    sum::{Addend, Sum},
    symbol::Symbol,
};
use crate::parse::{ast::Ast, parse_src};
use vec1::vec1;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Expr {
    Undefined,
    Symbol(Symbol),
    Constant(Constant),
    Sum(Sum),
    Product(Product),
    Power(Power),
    Factorial(Factorial),
}
impl Expr {
    pub fn from_src(src: &str) -> Self {
        let result = parse_src(src);
        Self::from_ast(result.ast.unwrap())
    }

    pub fn from_ast(ast: Ast) -> Self {
        match ast {
            Ast::Undefined => Self::Undefined,
            Ast::Symbol(name) => Symbol::new(name).as_expr(),
            Ast::Constant(constant) => Constant::from_dec(constant).as_expr(),
            Ast::UnaryOp(unary) => match unary.op {
                crate::parse::ast::UnaryOp::Neg => Self::from_ast(*unary.operand).negate(),
                crate::parse::ast::UnaryOp::Fac => Factorial::new(Self::from_ast(*unary.operand)),
            },
            Ast::BinaryOp(binary) => match binary.op {
                crate::parse::ast::BinaryOp::Add => {
                    Self::from_ast(*binary.l).add(Self::from_ast(*binary.r))
                }
                crate::parse::ast::BinaryOp::Sub => {
                    Self::from_ast(*binary.l).add(Self::from_ast(*binary.r).negate())
                }
                crate::parse::ast::BinaryOp::Mul => {
                    Self::from_ast(*binary.l).multiply(Self::from_ast(*binary.r))
                }
                crate::parse::ast::BinaryOp::Div => {
                    Self::from_ast(*binary.l).divide(Self::from_ast(*binary.r))
                }
                crate::parse::ast::BinaryOp::Exp => {
                    Self::from_ast(*binary.l).power(Self::from_ast(*binary.r))
                }
            },
        }
    }

    fn add(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Expr::Constant(l), Expr::Constant(r)) => l.add(r).as_expr(),

            (Expr::Symbol(l), Expr::Symbol(r)) => {
                Sum::new(Constant::zero(), operands![l.into(), r.into()])
            }

            (Expr::Product(l), Expr::Product(r)) => {
                Sum::new(Constant::zero(), operands![l.into(), r.into()])
            }

            (Expr::Power(l), Expr::Power(r)) => {
                Sum::new(Constant::zero(), operands![l.into(), r.into()])
            }

            (Expr::Factorial(l), Expr::Factorial(r)) => {
                Sum::new(Constant::zero(), operands![l.into(), r.into()])
            }

            (Expr::Sum(l), Expr::Sum(r)) => l.add(r.as_expr()),

            (Expr::Symbol(symbol), Expr::Constant(constant))
            | (Expr::Constant(constant), Expr::Symbol(symbol)) => {
                Sum::new(constant, operands![symbol.into()])
            }

            (Expr::Symbol(symbol), Expr::Product(product))
            | (Expr::Product(product), Expr::Symbol(symbol)) => {
                Sum::new(Constant::zero(), operands![symbol.into(), product.into()])
            }

            (Expr::Symbol(symbol), Expr::Power(power))
            | (Expr::Power(power), Expr::Symbol(symbol)) => {
                Sum::new(Constant::zero(), operands![symbol.into(), power.into()])
            }

            (Expr::Symbol(symbol), Expr::Factorial(factorial))
            | (Expr::Factorial(factorial), Expr::Symbol(symbol)) => {
                Sum::new(Constant::zero(), operands![symbol.into(), factorial.into()])
            }

            (Expr::Constant(constant), Expr::Product(product))
            | (Expr::Product(product), Expr::Constant(constant)) => {
                Sum::new(constant, operands![product.into()])
            }

            (Expr::Constant(constant), Expr::Power(power))
            | (Expr::Power(power), Expr::Constant(constant)) => {
                Sum::new(constant, operands![power.into()])
            }

            (Expr::Constant(constant), Expr::Factorial(factorial))
            | (Expr::Factorial(factorial), Expr::Constant(constant)) => {
                Sum::new(constant, operands![factorial.into()])
            }

            (Expr::Product(product), Expr::Power(power))
            | (Expr::Power(power), Expr::Product(product)) => {
                Sum::new(Constant::zero(), operands![product.into(), power.into()])
            }

            (Expr::Product(product), Expr::Factorial(factorial))
            | (Expr::Factorial(factorial), Expr::Product(product)) => Sum::new(
                Constant::zero(),
                operands![product.into(), factorial.into()],
            ),

            (Expr::Power(power), Expr::Factorial(factorial))
            | (Expr::Factorial(factorial), Expr::Power(power)) => {
                Sum::new(Constant::zero(), operands![power.into(), factorial.into()])
            }

            (Expr::Sum(sum), Expr::Symbol(other)) | (Expr::Symbol(other), Expr::Sum(sum)) => {
                sum.add(other.as_expr())
            }

            (Expr::Sum(sum), Expr::Constant(other)) | (Expr::Constant(other), Expr::Sum(sum)) => {
                sum.add(other.as_expr())
            }

            (Expr::Sum(sum), Expr::Product(other)) | (Expr::Product(other), Expr::Sum(sum)) => {
                sum.add(other.as_expr())
            }

            (Expr::Sum(sum), Expr::Power(other)) | (Expr::Power(other), Expr::Sum(sum)) => {
                sum.add(other.as_expr())
            }

            (Expr::Sum(sum), Expr::Factorial(other)) | (Expr::Factorial(other), Expr::Sum(sum)) => {
                sum.add(other.as_expr())
            }

            (Expr::Undefined, _) | (_, Expr::Undefined) => Expr::Undefined,
        }
    }

    fn multiply(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Expr::Constant(l), Expr::Constant(r)) => l.multiply(r).as_expr(),

            (Expr::Symbol(l), Expr::Symbol(r)) => {
                Product::new(Constant::one(), vec1![l.into(), r.into()])
            }

            (Expr::Product(l), Expr::Product(r)) => l.multiply(r.as_expr()),

            (Expr::Power(l), Expr::Power(r)) => {
                Product::new(Constant::one(), vec1![l.into(), r.into()])
            }

            (Expr::Factorial(l), Expr::Factorial(r)) => {
                Product::new(Constant::one(), vec1![l.into(), r.into()])
            }

            (Expr::Sum(l), Expr::Sum(r)) => {
                Product::new(Constant::one(), vec1![l.into(), r.into()])
            }

            (Expr::Symbol(symbol), Expr::Constant(constant))
            | (Expr::Constant(constant), Expr::Symbol(symbol)) => {
                Product::new(constant, vec1![symbol.into()])
            }

            (Expr::Symbol(symbol), Expr::Power(power))
            | (Expr::Power(power), Expr::Symbol(symbol)) => {
                Product::new(Constant::one(), vec1![symbol.into(), power.into()])
            }

            (Expr::Symbol(symbol), Expr::Factorial(factorial))
            | (Expr::Factorial(factorial), Expr::Symbol(symbol)) => {
                Product::new(Constant::one(), vec1![symbol.into(), factorial.into()])
            }

            (Expr::Constant(constant), Expr::Power(power))
            | (Expr::Power(power), Expr::Constant(constant)) => {
                Product::new(constant, vec1![power.into()])
            }

            (Expr::Constant(constant), Expr::Factorial(factorial))
            | (Expr::Factorial(factorial), Expr::Constant(constant)) => {
                Product::new(constant, vec1![factorial.into()])
            }

            (Expr::Power(power), Expr::Factorial(factorial))
            | (Expr::Factorial(factorial), Expr::Power(power)) => {
                Product::new(Constant::one(), vec1![power.into(), factorial.into()])
            }

            (Expr::Sum(sum), Expr::Symbol(symbol)) | (Expr::Symbol(symbol), Expr::Sum(sum)) => {
                Product::new(Constant::one(), vec1![symbol.into(), sum.into()])
            }

            (Expr::Sum(sum), Expr::Constant(constant))
            | (Expr::Constant(constant), Expr::Sum(sum)) => {
                Product::new(constant, vec1![sum.into()])
            }

            (Expr::Sum(sum), Expr::Power(power)) | (Expr::Power(power), Expr::Sum(sum)) => {
                Product::new(Constant::one(), vec1![power.into(), sum.into()])
            }

            (Expr::Sum(sum), Expr::Factorial(factorial))
            | (Expr::Factorial(factorial), Expr::Sum(sum)) => {
                Product::new(Constant::one(), vec1![factorial.into(), sum.into()])
            }

            (Expr::Symbol(symbol), Expr::Product(product))
            | (Expr::Product(product), Expr::Symbol(symbol)) => product.multiply(symbol.as_expr()),

            (Expr::Product(product), Expr::Power(power))
            | (Expr::Power(power), Expr::Product(product)) => product.multiply(power.as_expr()),

            (Expr::Product(product), Expr::Factorial(factorial))
            | (Expr::Factorial(factorial), Expr::Product(product)) => {
                product.multiply(factorial.as_expr())
            }

            (Expr::Constant(constant), Expr::Product(product))
            | (Expr::Product(product), Expr::Constant(constant)) => {
                product.multiply(constant.as_expr())
            }

            (Expr::Sum(sum), Expr::Product(product)) | (Expr::Product(product), Expr::Sum(sum)) => {
                product.multiply(sum.as_expr())
            }

            (Expr::Undefined, _) | (_, Expr::Undefined) => Expr::Undefined,
        }
    }

    fn divide(self, rhs: Self) -> Self {
        self.multiply(Power::new(rhs, Constant::neg_one().as_expr()))
    }

    fn power(self, rhs: Self) -> Self {
        Power::new(self, rhs)
    }

    fn negate(self) -> Self {
        match self {
            Self::Undefined => Self::Undefined,
            Self::Symbol(symbol) => symbol.negate(),
            Self::Constant(constant) => constant.negate().as_expr(),
            Self::Sum(sum) => sum.negate(),
            Self::Product(product) => product.negate().as_expr(),
            Self::Power(power) => power.negate(),
            Self::Factorial(factorial) => factorial.negate(),
        }
    }

    fn is_undefined(&self) -> bool {
        match self {
            Expr::Undefined => true,
            _ => false,
        }
    }

    fn is_zero_const(&self) -> bool {
        match self {
            Expr::Constant(constant) => constant.is_zero(),
            _ => false,
        }
    }

    fn is_one_const(&self) -> bool {
        match self {
            Expr::Constant(constant) => constant.is_one(),
            _ => false,
        }
    }

    fn is_pos_const(&self) -> bool {
        match self {
            Expr::Constant(constant) => constant.is_pos(),
            _ => false,
        }
    }

    fn expect_constant(self) -> Constant {
        match self {
            Expr::Constant(constant) => constant,
            _ => panic!("Not a constant: {:?}", self),
        }
    }

    fn expect_factor(self) -> Factor {
        match self {
            Expr::Symbol(symbol) => symbol.into(),
            Expr::Sum(sum) => sum.into(),
            Expr::Power(power) => power.into(),
            Expr::Factorial(factorial) => factorial.into(),
            _ => panic!("Cannot make product factor: {:?}", self),
        }
    }

    fn expect_addend(self) -> Addend {
        match self {
            Expr::Symbol(symbol) => symbol.into(),
            Expr::Product(product) => product.into(),
            Expr::Power(power) => power.into(),
            Expr::Factorial(factorial) => factorial.into(),
            _ => panic!("Cannot make sum addend: {:?}", self),
        }
    }

    fn expect_integer_power_base(self) -> IntegerPowerBase {
        match self {
            Expr::Symbol(symbol) => symbol.into(),
            Expr::Sum(sum) => sum.into(),
            Expr::Factorial(factorial) => factorial.into(),
            _ => panic!("Cannot make integer power base: {:?}", self),
        }
    }

    fn expect_non_integer_power_exponent(self) -> NonIntegerPowerExponent {
        match self {
            Expr::Undefined => panic!("Undefined expression"),
            Expr::Symbol(symbol) => symbol.into(),
            Expr::Constant(constant) => {
                if constant.is_int() {
                    panic!("Integer constant")
                } else {
                    constant.into()
                }
            }
            Expr::Sum(sum) => sum.into(),
            Expr::Product(product) => product.into(),
            Expr::Power(power) => power.into(),
            Expr::Factorial(factorial) => factorial.into(),
        }
    }
}

pub(crate) mod unenforced_helpers {
    use super::{
        constant::Constant, factorial::Factorial, power::Power, product::Product, sum::Sum,
        symbol::Symbol, Expr,
    };

    #[allow(dead_code)]
    pub fn undefined() -> Expr {
        Expr::Undefined
    }

    #[allow(dead_code)]
    pub fn int(value: i128) -> Expr {
        Constant::unenforced_int(value)
    }

    #[allow(dead_code)]
    pub fn frac(num: i128, den: i128) -> Expr {
        Constant::unenforced_frac(num, den)
    }

    #[allow(dead_code)]
    pub fn sym(name: &str) -> Expr {
        Symbol::unenforced(name.into())
    }

    #[allow(dead_code)]
    pub fn factorial(expr: Expr) -> Expr {
        Factorial::unenforced(expr)
    }

    #[allow(dead_code)]
    pub fn product<const N: usize>(factors: [Expr; N]) -> Expr {
        Product::unenforced(Vec::from(factors))
    }

    #[allow(dead_code)]
    pub fn sum<const N: usize>(addends: [Expr; N]) -> Expr {
        Sum::unenforced(Vec::from(addends))
    }

    #[allow(dead_code)]
    pub fn pow(base: Expr, exponent: Expr) -> Expr {
        Power::unenforced(base, exponent)
    }

    #[allow(dead_code)]
    pub fn powi(base: Expr, exponent: i128) -> Expr {
        Power::unenforced_int(base, exponent)
    }
}

#[macro_export]
macro_rules! operands {
    () => (
        compile_error!("Vec1 needs at least 1 element")
    );
    ($first:expr $(, $item:expr)* , ) => (
        $crate::vec1!($first $(, $item)*)
    );
    ($first:expr $(, $item:expr)* ) => ({
        #[allow(unused_mut)]
        let mut tmp = $crate::expr::Operands::new($first);
        $(tmp.insert($item);)*
        tmp
    });
}

#[derive(Debug, PartialEq, Eq, Ord, PartialOrd)]
pub(crate) struct Operands<T: Ord> {
    set: BTreeSet<T>,
}
impl<T: Ord> Operands<T> {
    pub fn new(first: T) -> Self {
        Self {
            set: BTreeSet::from([first]),
        }
    }

    pub fn insert(&mut self, operand: T) {
        self.set.insert(operand);
    }

    pub fn len(&self) -> usize {
        self.set.len()
    }

    pub fn take_first(self) -> T {
        self.set.into_iter().next().unwrap()
    }

    pub fn into_iter(self) -> IntoIter<T> {
        self.set.into_iter()
    }
}

#[cfg(test)]
mod tests {
    use crate::expr::unenforced_helpers::*;

    use super::*;

    #[test]
    fn reads_integer() {
        assert_eq!(Expr::from_src("123"), int(123));
        assert_eq!(Expr::from_src("0"), int(0));
        assert_eq!(Expr::from_src("001"), int(1));
        assert_eq!(Expr::from_src("100"), int(100));
    }

    #[test]
    fn reads_negative_integer() {
        assert_eq!(Expr::from_src("-123"), int(-123));
        assert_eq!(Expr::from_src("-0"), int(0));
        assert_eq!(Expr::from_src("-001"), int(-1));
        assert_eq!(Expr::from_src("-100"), int(-100));
    }

    #[test]
    fn reads_decimal_fraction() {
        assert_eq!(Expr::from_src("1.2"), frac(6, 5));
        assert_eq!(Expr::from_src("0.12"), frac(3, 25));
        assert_eq!(Expr::from_src("12.0"), int(12));
    }

    #[test]
    fn reads_negative_decimal_fraction() {
        assert_eq!(Expr::from_src("-1.2"), frac(-6, 5));
        assert_eq!(Expr::from_src("-0.12"), frac(-3, 25));
        assert_eq!(Expr::from_src("-12.0"), int(-12));
    }
}
