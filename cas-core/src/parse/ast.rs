use num::{BigInt, BigRational, One, Signed, Zero};
use rust_decimal::Decimal;

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
    Fun(String, Vec<Ast>),
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

pub mod ast_helpers {
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

#[cfg(test)]
pub(crate) mod test_helpers {
    use crate::parse::parse_src;

    use super::Ast;

    fn ast_from_src(src: &str) -> Ast {
        let result = parse_src(src);
        result.ast.unwrap()
    }

    pub fn test_src(src: &str, expected: Ast) {
        assert_eq!(ast_from_src(src), expected)
    }

    pub fn test_simplified_src(src: &str, expected: Ast) {
        assert_eq!(ast_from_src(src).simplify(), expected)
    }
}
