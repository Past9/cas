use std::{borrow::Borrow, cmp::Ordering, str::FromStr};

use num::{BigInt, BigRational, FromPrimitive};
use rust_decimal::Decimal;

use crate::tokenize::tokens::Token;

use self::ast_helpers::{exp, int};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Ast {
    Und,
    Sym(String),
    Int(BigInt),
    Frc(BigRational),
    Neg(Box<Ast>),
    Fac(Box<Ast>),
    Add(Vec<Ast>),
    Mul(Vec<Ast>),
    Sub(Box<Ast>, Box<Ast>),
    Div(Box<Ast>, Box<Ast>),
    Exp(Box<Ast>, Box<Ast>),
}
impl Ast {
    pub fn from_dec(dec: Decimal) -> Self {
        Self::from_frac(BigRational::new(
            dec.mantissa().into(),
            10i128.pow(dec.scale()).into(),
        ))
    }

    pub fn from_frac(frac: BigRational) -> Self {
        if frac.is_integer() {
            Self::from_int(frac.to_integer())
        } else {
            Self::Frc(frac)
        }
    }

    pub fn from_int(int: BigInt) -> Self {
        Self::Int(int)
    }
}
impl PartialOrd for Ast {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            // O-1
            (Ast::Int(s), Ast::Int(o)) => s.partial_cmp(o),
            (Ast::Frc(s), Ast::Frc(o)) => s.partial_cmp(o),
            (Ast::Int(s), Ast::Frc(o)) => (s * o.denom()).partial_cmp(o.numer()),
            (Ast::Frc(s), Ast::Int(o)) => s.numer().partial_cmp(&(o * s.denom())),

            // O-2
            (Ast::Sym(s), Ast::Sym(o)) => s.partial_cmp(o),

            // O-3
            (Ast::Add(s), Ast::Add(o)) => compare_operands(s, o),
            (Ast::Mul(s), Ast::Mul(o)) => compare_operands(s, o),

            // O-4
            (Ast::Exp(s_base, s_exp), Ast::Exp(o_base, o_exp)) => {
                if s_base != o_base {
                    // O-4-1
                    s_base.partial_cmp(o_base)
                } else {
                    // O-4-2
                    s_exp.partial_cmp(o_exp)
                }
            }

            // O-5
            (Ast::Fac(s), Ast::Fac(o)) => s.partial_cmp(o),

            // O-7
            (Ast::Int(_), _) => Some(Ordering::Less),
            (Ast::Frc(_), _) => Some(Ordering::Less),
            (_, Ast::Int(_)) => Some(Ordering::Greater),
            (_, Ast::Frc(_)) => Some(Ordering::Greater),

            // O-8
            (Ast::Mul(s), o @ Ast::Exp(..))
            | (Ast::Mul(s), o @ Ast::Add(..))
            | (Ast::Mul(s), o @ Ast::Fac(..))
            | (Ast::Mul(s), o @ Ast::Sym(..)) => compare_operands(s, &[o]),

            (s @ Ast::Exp(..), o @ Ast::Mul(..))
            | (s @ Ast::Add(..), o @ Ast::Mul(..))
            | (s @ Ast::Fac(..), o @ Ast::Mul(..))
            | (s @ Ast::Sym(..), o @ Ast::Mul(..)) => o.partial_cmp(s).map(Ordering::reverse),

            // O-9
            (Ast::Exp(s_base, s_exp), o_base @ Ast::Add(..))
            | (Ast::Exp(s_base, s_exp), o_base @ Ast::Fac(..))
            | (Ast::Exp(s_base, s_exp), o_base @ Ast::Sym(..)) => {
                // Treat other expression as exponent with power of one,
                // then user O-4 rules
                if &**s_base != o_base {
                    // O-4-1
                    (&**s_base).partial_cmp(o_base)
                } else {
                    // O-4-2
                    (&**s_exp).partial_cmp(&int(1))
                }
            }

            (s @ Ast::Add(..), o @ Ast::Exp(..))
            | (s @ Ast::Fac(..), o @ Ast::Exp(..))
            | (s @ Ast::Sym(..), o @ Ast::Exp(..)) => o.partial_cmp(s).map(Ordering::reverse),

            // O-10
            (Ast::Add(s), o @ Ast::Fac(..)) | (Ast::Add(s), o @ Ast::Sym(..)) => {
                compare_operands(s, &[o])
            }

            (s @ Ast::Fac(..), o @ Ast::Add(..)) | (s @ Ast::Sym(..), o @ Ast::Add(..)) => {
                o.partial_cmp(s).map(Ordering::reverse)
            }

            // O-11
            (Ast::Fac(s), o @ Ast::Sym(..)) => {
                if &**s == o {
                    Some(Ordering::Greater)
                } else {
                    // Revert to O-5. Rather than creating two factorials
                    // to compare, we just re-implement the logic here, which
                    // just compares the operands.
                    (&**s).partial_cmp(o)
                }
            }

            (s @ Ast::Sym(..), o @ Ast::Fac(..)) => o.partial_cmp(s).map(Ordering::reverse),

            (Ast::Und, _) | (_, Ast::Und) => panic!("Cannot sort undefined"),
            (Ast::Neg(..), _) | (_, Ast::Neg(..)) => panic!("Cannot sort negation"),
            (Ast::Sub(..), _) | (_, Ast::Sub(..)) => panic!("Cannot sort subtraction"),
            (Ast::Div(..), _) | (_, Ast::Div(..)) => panic!("Cannot sort division"),
        }
    }
}
impl Ord for Ast {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other)
            .expect("Ast::partial_cmp returned None")
    }
}

fn compare_operands<T: Borrow<Ast>, U: Borrow<Ast>>(l: &[T], r: &[U]) -> Option<Ordering> {
    let mut m = l.len() as isize;
    let mut n = r.len() as isize;

    // First iteration is O-1
    // Subsequent ones are O-2
    while m >= 0 && n >= 0 {
        if l[m as usize].borrow() == r[n as usize].borrow() {
            m -= 1;
            n -= 1;
            continue;
        } else {
            return l[m as usize].borrow().partial_cmp(&r[n as usize].borrow());
        }
    }

    // O-3 (longest operands wins)
    if l.len() == r.len() {
        Some(Ordering::Equal)
    } else {
        Some(l.len().cmp(&r.len()))
    }
}

pub mod ast_helpers {
    use num::{BigInt, BigRational, FromPrimitive};

    use super::Ast;

    pub fn fac(operand: Ast) -> Ast {
        Ast::Fac(Box::new(operand))
    }

    pub fn neg(operand: Ast) -> Ast {
        Ast::Neg(Box::new(operand))
    }

    pub fn add(l: Ast, r: Ast) -> Ast {
        Ast::Add(vec![l, r])
    }

    pub fn mul(l: Ast, r: Ast) -> Ast {
        Ast::Add(vec![l, r])
    }

    pub fn sub(l: Ast, r: Ast) -> Ast {
        Ast::Sub(Box::new(l), Box::new(r))
    }

    pub fn div(l: Ast, r: Ast) -> Ast {
        Ast::Div(Box::new(l), Box::new(r))
    }

    pub fn exp(l: Ast, r: Ast) -> Ast {
        Ast::Exp(Box::new(l), Box::new(r))
    }

    pub fn sym(name: &str) -> Ast {
        Ast::Sym(name.to_owned())
    }

    pub fn int(int: i128) -> Ast {
        Ast::Int(BigInt::from_i128(int).unwrap())
    }

    pub fn frac(num: i128, den: i128) -> Ast {
        Ast::Frc(BigRational::new(
            BigInt::from_i128(num).unwrap(),
            BigInt::from_i128(den).unwrap(),
        ))
    }

    pub fn und() -> Ast {
        Ast::Und
    }
}
