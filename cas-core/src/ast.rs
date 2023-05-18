use std::ops::{Add, Div, Mul, Sub};

use auto_ops::{impl_op_ex, impl_op_ex_commutative};
use num::{bigint::ToBigInt, BigInt, BigRational, BigUint, FromPrimitive};

use self::helpers::*;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Ast {
    Fail,
    Und,
    Sym(String),
    Int(BigInt),
    Frc(BigRational),
    Neg(Box<Ast>),
    Fac(Box<Ast>),
    Sum(Vec<Ast>),
    Prd(Vec<Ast>),
    Dif(Box<Ast>, Box<Ast>),
    Quo(Box<Ast>, Box<Ast>),
    Pow(Box<Ast>, Box<Ast>),
    Fun(String, Vec<Ast>),
}
impl Ast {
    pub fn pow(self, exp: Self) -> Self {
        pow(self, exp)
    }

    pub fn root(self, root: Self) -> Self {
        self.pow(quo(int(1), root))
    }

    pub fn sqrt(self) -> Self {
        self.root(int(2))
    }
}

impl From<u8> for Ast {
    fn from(value: u8) -> Self {
        Ast::Int(BigInt::from_u8(value).unwrap())
    }
}
impl From<i8> for Ast {
    fn from(value: i8) -> Self {
        Ast::Int(BigInt::from_i8(value).unwrap())
    }
}
impl From<u16> for Ast {
    fn from(value: u16) -> Self {
        Ast::Int(BigInt::from_u16(value).unwrap())
    }
}
impl From<i16> for Ast {
    fn from(value: i16) -> Self {
        Ast::Int(BigInt::from_i16(value).unwrap())
    }
}
impl From<u32> for Ast {
    fn from(value: u32) -> Self {
        Ast::Int(BigInt::from_u32(value).unwrap())
    }
}
impl From<i32> for Ast {
    fn from(value: i32) -> Self {
        Ast::Int(BigInt::from_i32(value).unwrap())
    }
}
impl From<u64> for Ast {
    fn from(value: u64) -> Self {
        Ast::Int(BigInt::from_u64(value).unwrap())
    }
}
impl From<i64> for Ast {
    fn from(value: i64) -> Self {
        Ast::Int(BigInt::from_i64(value).unwrap())
    }
}
impl From<u128> for Ast {
    fn from(value: u128) -> Self {
        Ast::Int(BigInt::from_u128(value).unwrap())
    }
}
impl From<i128> for Ast {
    fn from(value: i128) -> Self {
        Ast::Int(BigInt::from_i128(value).unwrap())
    }
}
impl From<BigInt> for Ast {
    fn from(value: BigInt) -> Self {
        Ast::Int(value)
    }
}
impl From<BigUint> for Ast {
    fn from(value: BigUint) -> Self {
        Ast::Int(value.to_bigint().unwrap())
    }
}

impl Add for Ast {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        sum([self, rhs])
    }
}
impl Sub for Ast {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        dif(self, rhs)
    }
}
impl Mul for Ast {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        prd([self, rhs])
    }
}
impl Div for Ast {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        quo(self, rhs)
    }
}

impl_op_ex_commutative!(+ |a: Ast, b: u8| -> Ast { sum([b.into(), a]) });
impl_op_ex_commutative!(+ |a: Ast, b: i8| -> Ast { sum([b.into(), a]) });
impl_op_ex_commutative!(+ |a: Ast, b: u16| -> Ast { sum([b.into(), a]) });
impl_op_ex_commutative!(+ |a: Ast, b: i16| -> Ast { sum([b.into(), a]) });
impl_op_ex_commutative!(+ |a: Ast, b: u32| -> Ast { sum([b.into(), a]) });
impl_op_ex_commutative!(+ |a: Ast, b: i32| -> Ast { sum([b.into(), a]) });
impl_op_ex_commutative!(+ |a: Ast, b: u64| -> Ast { sum([b.into(), a]) });
impl_op_ex_commutative!(+ |a: Ast, b: i64| -> Ast { sum([b.into(), a]) });
impl_op_ex_commutative!(+ |a: Ast, b: u128| -> Ast { sum([b.into(), a]) });
impl_op_ex_commutative!(+ |a: Ast, b: i128| -> Ast { sum([b.into(), a]) });

impl_op_ex_commutative!(*|a: Ast, b: u8| -> Ast { prd([b.into(), a]) });
impl_op_ex_commutative!(*|a: Ast, b: i8| -> Ast { prd([b.into(), a]) });
impl_op_ex_commutative!(*|a: Ast, b: u16| -> Ast { prd([b.into(), a]) });
impl_op_ex_commutative!(*|a: Ast, b: i16| -> Ast { prd([b.into(), a]) });
impl_op_ex_commutative!(*|a: Ast, b: u32| -> Ast { prd([b.into(), a]) });
impl_op_ex_commutative!(*|a: Ast, b: i32| -> Ast { prd([b.into(), a]) });
impl_op_ex_commutative!(*|a: Ast, b: u64| -> Ast { prd([b.into(), a]) });
impl_op_ex_commutative!(*|a: Ast, b: i64| -> Ast { prd([b.into(), a]) });
impl_op_ex_commutative!(*|a: Ast, b: u128| -> Ast { prd([b.into(), a]) });
impl_op_ex_commutative!(*|a: Ast, b: i128| -> Ast { prd([b.into(), a]) });

impl_op_ex!(/|a: Ast, b: u8| -> Ast { quo(a, b.into()) });
impl_op_ex!(/|a: Ast, b: i8| -> Ast { quo(a, b.into()) });
impl_op_ex!(/|a: Ast, b: u16| -> Ast { quo(a, b.into()) });
impl_op_ex!(/|a: Ast, b: i16| -> Ast { quo(a, b.into()) });
impl_op_ex!(/|a: Ast, b: u32| -> Ast { quo(a, b.into()) });
impl_op_ex!(/|a: Ast, b: i32| -> Ast { quo(a, b.into()) });
impl_op_ex!(/|a: Ast, b: u64| -> Ast { quo(a, b.into()) });
impl_op_ex!(/|a: Ast, b: i64| -> Ast { quo(a, b.into()) });
impl_op_ex!(/|a: Ast, b: u128| -> Ast { quo(a, b.into()) });
impl_op_ex!(/|a: Ast, b: i128| -> Ast { quo(a, b.into()) });

impl_op_ex!(/|a: u8, b: Ast| -> Ast { quo(a.into(), b) });
impl_op_ex!(/|a: i8, b: Ast| -> Ast { quo(a.into(), b) });
impl_op_ex!(/|a: u16, b: Ast| -> Ast { quo(a.into(), b) });
impl_op_ex!(/|a: i16, b: Ast| -> Ast { quo(a.into(), b) });
impl_op_ex!(/|a: u32, b: Ast| -> Ast { quo(a.into(), b) });
impl_op_ex!(/|a: i32, b: Ast| -> Ast { quo(a.into(), b) });
impl_op_ex!(/|a: u64, b: Ast| -> Ast { quo(a.into(), b) });
impl_op_ex!(/|a: i64, b: Ast| -> Ast { quo(a.into(), b) });
impl_op_ex!(/|a: u128, b: Ast| -> Ast { quo(a.into(), b) });
impl_op_ex!(/|a: i128, b: Ast| -> Ast { quo(a.into(), b) });

impl_op_ex!(-|a: Ast, b: u8| -> Ast { dif(a, b.into()) });
impl_op_ex!(-|a: Ast, b: i8| -> Ast { dif(a, b.into()) });
impl_op_ex!(-|a: Ast, b: u16| -> Ast { dif(a, b.into()) });
impl_op_ex!(-|a: Ast, b: i16| -> Ast { dif(a, b.into()) });
impl_op_ex!(-|a: Ast, b: u32| -> Ast { dif(a, b.into()) });
impl_op_ex!(-|a: Ast, b: i32| -> Ast { dif(a, b.into()) });
impl_op_ex!(-|a: Ast, b: u64| -> Ast { dif(a, b.into()) });
impl_op_ex!(-|a: Ast, b: i64| -> Ast { dif(a, b.into()) });
impl_op_ex!(-|a: Ast, b: u128| -> Ast { dif(a, b.into()) });
impl_op_ex!(-|a: Ast, b: i128| -> Ast { dif(a, b.into()) });

impl_op_ex!(-|a: u8, b: Ast| -> Ast { dif(a.into(), b) });
impl_op_ex!(-|a: i8, b: Ast| -> Ast { dif(a.into(), b) });
impl_op_ex!(-|a: u16, b: Ast| -> Ast { dif(a.into(), b) });
impl_op_ex!(-|a: i16, b: Ast| -> Ast { dif(a.into(), b) });
impl_op_ex!(-|a: u32, b: Ast| -> Ast { dif(a.into(), b) });
impl_op_ex!(-|a: i32, b: Ast| -> Ast { dif(a.into(), b) });
impl_op_ex!(-|a: u64, b: Ast| -> Ast { dif(a.into(), b) });
impl_op_ex!(-|a: i64, b: Ast| -> Ast { dif(a.into(), b) });
impl_op_ex!(-|a: u128, b: Ast| -> Ast { dif(a.into(), b) });
impl_op_ex!(-|a: i128, b: Ast| -> Ast { dif(a.into(), b) });

#[macro_export]
macro_rules! expr {
    ($ast:expr) => {
        $ast as Ast
    };
}

pub mod helpers {
    use num::{BigInt, BigRational, FromPrimitive};

    use super::Ast;

    pub fn fac(operand: Ast) -> Ast {
        Ast::Fac(Box::new(operand))
    }

    pub fn neg(operand: Ast) -> Ast {
        Ast::Neg(Box::new(operand))
    }

    pub fn sum<const N: usize>(operands: [Ast; N]) -> Ast {
        Ast::Sum(operands.to_vec())
    }

    pub fn prd<const N: usize>(operands: [Ast; N]) -> Ast {
        Ast::Prd(operands.to_vec())
    }

    pub fn dif(l: Ast, r: Ast) -> Ast {
        Ast::Dif(Box::new(l), Box::new(r))
    }

    pub fn quo(l: Ast, r: Ast) -> Ast {
        Ast::Quo(Box::new(l), Box::new(r))
    }

    pub fn pow(l: Ast, r: Ast) -> Ast {
        Ast::Pow(Box::new(l), Box::new(r))
    }

    pub fn sym(name: &str) -> Ast {
        Ast::Sym(name.to_owned())
    }

    pub fn fun<const N: usize>(name: &str, args: [Ast; N]) -> Ast {
        Ast::Fun(name.to_owned(), args.to_vec())
    }

    pub fn int(int: i128) -> Ast {
        Ast::Int(BigInt::from_i128(int).unwrap())
    }

    pub fn frc(num: i128, den: i128) -> Ast {
        Ast::Frc(BigRational::new(
            BigInt::from_i128(num).unwrap(),
            BigInt::from_i128(den).unwrap(),
        ))
    }

    pub fn und() -> Ast {
        Ast::Und
    }
}
