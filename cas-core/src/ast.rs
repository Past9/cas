use num::{BigInt, BigRational};

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
