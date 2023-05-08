use num::{bigint::ToBigInt, BigUint, Signed, Zero};

use crate::parse::ast::{
    ast_helpers::{fac, int},
    Ast,
};

impl Ast {
    pub(crate) fn simplify_factorial(operand: Self) -> Self {
        match operand {
            und @ Ast::Und => und,
            ref int_op @ Ast::Int(ref int_val) => {
                if int_val.is_zero() {
                    return int(0);
                } else if int_val.is_positive() {
                    Ast::Int(
                        int_factorial(int_val.to_biguint().unwrap())
                            .to_bigint()
                            .unwrap(),
                    )
                } else {
                    fac(int_op.to_owned())
                }
            }
            Ast::Sym(_)
            | Ast::Frc(_)
            | Ast::Neg(_)
            | Ast::Fac(_)
            | Ast::Sum(_)
            | Ast::Prd(_)
            | Ast::Dif(_, _)
            | Ast::Quo(_, _)
            | Ast::Pow(_, _) => fac(operand),
        }
    }
}

fn int_factorial(uint: BigUint) -> BigUint {
    if uint == 1u32.into() {
        return 1u32.into();
    } else {
        return &uint * int_factorial(&uint - BigUint::from(1u32));
    }
}
