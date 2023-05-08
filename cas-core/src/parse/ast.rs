use self::ast_helpers::int;
use num::{BigInt, BigRational, One, Signed, Zero};
use rust_decimal::Decimal;
use std::{borrow::Borrow, cmp::Ordering};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Ast {
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

    pub fn simplify(self) -> Self {
        match self {
            ast @ (Ast::Und | Ast::Sym(_) | Ast::Int(_)) => ast,
            Ast::Frc(frc) => Self::simplify_fraction(frc),
            Ast::Neg(operand) => Self::simplify_negation(*operand),
            Ast::Fac(operand) => Self::simplify_factorial(*operand),
            Ast::Sum(operands) => Self::simplify_sum(operands),
            Ast::Prd(operands) => Self::simplify_product(operands),
            Ast::Dif(l, r) => Self::simplify_difference(*l, *r),
            Ast::Quo(l, r) => Self::simplify_quotient(*l, *r),
            Ast::Pow(base, exp) => Self::simplify_power(*base, *exp),
        }
    }

    pub fn is_undefined(&self) -> bool {
        match self {
            Ast::Und => true,
            _ => false,
        }
    }

    pub fn is_pos_int(&self) -> bool {
        match self {
            Ast::Int(int) => int.is_positive(),
            _ => false,
        }
    }

    pub fn is_pos_frc(&self) -> bool {
        match self {
            Ast::Frc(frc) => frc.is_positive(),
            _ => false,
        }
    }

    pub fn is_pos_const(&self) -> bool {
        self.is_pos_int() || self.is_pos_frc()
    }

    pub fn is_int_zero(&self) -> bool {
        match self {
            Ast::Int(int) => int.is_zero(),
            _ => false,
        }
    }

    pub fn is_int_one(&self) -> bool {
        match self {
            Ast::Int(int) => int.is_one(),
            _ => false,
        }
    }

    pub fn is_int(&self) -> bool {
        match self {
            Ast::Int(_) => true,
            _ => false,
        }
    }

    pub fn is_product(&self) -> bool {
        match self {
            Ast::Prd(_) => true,
            _ => false,
        }
    }

    pub fn is_sum(&self) -> bool {
        match self {
            Ast::Sum(_) => true,
            _ => false,
        }
    }

    pub fn is_const(&self) -> bool {
        match self {
            Ast::Int(_) | Ast::Frc(_) => true,
            _ => false,
        }
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
            (Ast::Sum(s), Ast::Sum(o)) => compare_operands(s, o),
            (Ast::Prd(s), Ast::Prd(o)) => compare_operands(s, o),

            // O-4
            (Ast::Pow(s_base, s_exp), Ast::Pow(o_base, o_exp)) => {
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
            (Ast::Prd(s), o @ Ast::Pow(..))
            | (Ast::Prd(s), o @ Ast::Sum(..))
            | (Ast::Prd(s), o @ Ast::Fac(..))
            | (Ast::Prd(s), o @ Ast::Sym(..)) => compare_operands(s, &[o]),

            (s @ Ast::Pow(..), o @ Ast::Prd(..))
            | (s @ Ast::Sum(..), o @ Ast::Prd(..))
            | (s @ Ast::Fac(..), o @ Ast::Prd(..))
            | (s @ Ast::Sym(..), o @ Ast::Prd(..)) => o.partial_cmp(s).map(Ordering::reverse),

            // O-9
            (Ast::Pow(s_base, s_exp), o_base @ Ast::Sum(..))
            | (Ast::Pow(s_base, s_exp), o_base @ Ast::Fac(..))
            | (Ast::Pow(s_base, s_exp), o_base @ Ast::Sym(..)) => {
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

            (s @ Ast::Sum(..), o @ Ast::Pow(..))
            | (s @ Ast::Fac(..), o @ Ast::Pow(..))
            | (s @ Ast::Sym(..), o @ Ast::Pow(..)) => o.partial_cmp(s).map(Ordering::reverse),

            // O-10
            (Ast::Sum(s), o @ Ast::Fac(..)) | (Ast::Sum(s), o @ Ast::Sym(..)) => {
                compare_operands(s, &[o])
            }

            (s @ Ast::Fac(..), o @ Ast::Sum(..)) | (s @ Ast::Sym(..), o @ Ast::Sum(..)) => {
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
            (Ast::Dif(..), _) | (_, Ast::Dif(..)) => panic!("Cannot sort subtraction"),
            (Ast::Quo(..), _) | (_, Ast::Quo(..)) => panic!("Cannot sort division"),
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

    pub fn sum(l: Ast, r: Ast) -> Ast {
        Ast::Sum(vec![l, r])
    }

    pub fn prd(l: Ast, r: Ast) -> Ast {
        Ast::Sum(vec![l, r])
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
