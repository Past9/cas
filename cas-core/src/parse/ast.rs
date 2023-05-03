use std::str::FromStr;

use rust_decimal::Decimal;

use crate::tokenize::tokens::Token;

#[derive(Debug, PartialEq, Clone)]
pub enum UnaryOp {
    Neg,
    Fac,
}
impl UnaryOp {
    pub fn from_token(token: Token) -> Self {
        match token {
            Token::Minus => Self::Neg,
            Token::Bang => Self::Fac,
            other => panic!("'{:?}' is not a unary operator", other),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Exp,
}
impl BinaryOp {
    pub fn from_token(token: Token) -> Self {
        match token {
            Token::Plus => Self::Add,
            Token::Minus => Self::Sub,
            Token::Asterisk => Self::Mul,
            Token::FwdSlash => Self::Div,
            Token::Caret => Self::Exp,
            other => panic!("'{:?}' is not a binary operator", other),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Ast {
    Undefined,
    Symbol(String),
    Constant(Decimal),
    UnaryOp(AstUnaryOp),
    BinaryOp(AstBinaryOp),
}
impl Ast {
    pub fn symbol(name: String) -> Self {
        Self::Symbol(name)
    }

    pub fn constant(value: Decimal) -> Self {
        Self::Constant(value)
    }

    pub fn unary_op(op: UnaryOp, operand: Self) -> Self {
        Self::UnaryOp(AstUnaryOp {
            op,
            operand: Box::new(operand),
        })
    }

    pub fn binary_op(op: BinaryOp, l: Self, r: Self) -> Self {
        Self::BinaryOp(AstBinaryOp {
            op,
            l: Box::new(l),
            r: Box::new(r),
        })
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct AstUnaryOp {
    pub op: UnaryOp,
    pub operand: Box<Ast>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct AstBinaryOp {
    pub op: BinaryOp,
    pub l: Box<Ast>,
    pub r: Box<Ast>,
}

pub fn fac(operand: Ast) -> Ast {
    Ast::unary_op(UnaryOp::Fac, operand)
}

pub fn neg(operand: Ast) -> Ast {
    Ast::unary_op(UnaryOp::Neg, operand)
}

pub fn add(l: Ast, r: Ast) -> Ast {
    Ast::binary_op(BinaryOp::Add, l, r)
}

pub fn sub(l: Ast, r: Ast) -> Ast {
    Ast::binary_op(BinaryOp::Sub, l, r)
}

pub fn mul(l: Ast, r: Ast) -> Ast {
    Ast::binary_op(BinaryOp::Mul, l, r)
}

pub fn div(l: Ast, r: Ast) -> Ast {
    Ast::binary_op(BinaryOp::Div, l, r)
}

pub fn exp(l: Ast, r: Ast) -> Ast {
    Ast::binary_op(BinaryOp::Exp, l, r)
}

pub fn sym(name: &str) -> Ast {
    Ast::Symbol(name.to_owned())
}

pub fn con(decimal: &str) -> Ast {
    Ast::Constant(
        Decimal::from_str(decimal).expect(&format!("Could not parse '{decimal}' as decimal")),
    )
}

pub fn und() -> Ast {
    Ast::Undefined
}
