use std::{collections::BTreeSet, iter::Product};

use num::{BigInt, BigRational, ToPrimitive};

use crate::parse::{ast::Ast, parse_src};

#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum Expr {
    Const(BigRational),
    Sum(BigRational, BTreeSet<SumOperand>),
    Product(BigRational, BTreeSet<ProductOperand>),
    Power(Box<Self>, Box<Self>),
}
impl Expr {
    pub fn from_src(src: &str) -> Self {
        let result = parse_src(src);
        Self::from_ast(result.ast.unwrap())
    }

    pub fn from_ast(ast: Ast) -> Self {
        match ast {
            Ast::Symbol(_) => unimplemented!(),
            Ast::Constant(decimal) => Self::Const(BigRational::new(
                decimal.mantissa().into(),
                10i128.pow(decimal.scale()).into(),
            )),
            Ast::UnaryOp(unary) => match unary.op {
                crate::parse::ast::UnaryOp::Neg => todo!(),
                crate::parse::ast::UnaryOp::Fac => unimplemented!(),
            },
            Ast::BinaryOp(binary) => match binary.op {
                crate::parse::ast::BinaryOp::Add => {
                    match (Self::from_ast(*binary.l), Self::from_ast(*binary.r)) {
                        (Expr::Const(l), Expr::Const(r)) => Self::Const(l / r),

                        (Expr::Sum(l_c, l_addends), Expr::Sum(r_c, r_addends)) => {
                            Self::Sum(l_c + r_c, todo!())
                        }

                        (Expr::Product(l_c, l_factors), Expr::Product(r_c, r_factors)) => todo!(),

                        (Expr::Power(l_base, l_pow), Expr::Power(r_base, r_pow)) => todo!(),

                        (Expr::Sum(sum_c, addends), Expr::Const(c))
                        | (Expr::Const(c), Expr::Sum(sum_c, addends)) => {
                            Self::Sum(c + sum_c, addends)
                        }

                        (Expr::Product(product_c, factors), Expr::Const(c))
                        | (Expr::Const(c), Expr::Product(product_c, factors)) => {
                            Self::Sum(c, BTreeSet::from([SumOperand::Product(product_c, factors)]))
                        }

                        (Expr::Const(c), Expr::Power(base, pow))
                        | (Expr::Power(base, pow), Expr::Const(c)) => todo!(),

                        (Expr::Sum(sum_c, addends), Expr::Product(product_c, factors))
                        | (Expr::Product(product_c, factors), Expr::Sum(sum_c, addends)) => todo!(),

                        (Expr::Sum(c, addends), Expr::Power(base, pow))
                        | (Expr::Power(base, pow), Expr::Sum(c, addends)) => todo!(),

                        (Expr::Product(c, factors), Expr::Power(base, pow))
                        | (Expr::Power(base, pow), Expr::Product(c, factors)) => todo!(),
                    }
                }
                crate::parse::ast::BinaryOp::Sub => todo!(),
                crate::parse::ast::BinaryOp::Mul => todo!(),
                crate::parse::ast::BinaryOp::Div => todo!(),
                crate::parse::ast::BinaryOp::Exp => todo!(),
            },
        }
    }
}
impl From<SumOperand> for Expr {
    fn from(value: SumOperand) -> Self {
        match value {
            SumOperand::Product(c, factors) => Self::Product(c, factors),
        }
    }
}
impl From<ProductOperand> for Expr {
    fn from(value: ProductOperand) -> Self {
        match value {
            ProductOperand::Sum(c, addends) => Self::Sum(c, addends),
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum SumOperand {
    Product(BigRational, BTreeSet<ProductOperand>),
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum ProductOperand {
    Sum(BigRational, BTreeSet<SumOperand>),
}
