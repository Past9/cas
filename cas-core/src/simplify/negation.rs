use std::ops::Neg;

use crate::ast::{helpers::*, Ast};

impl Ast {
    pub(crate) fn simplify_negation(operand: Self) -> Self {
        match operand {
            fail @ Self::Fail => fail,
            und @ Self::Und => und,
            Self::Int(int) => Self::from_int(int.neg()),
            Self::Frc(frc) => Self::from_frac(frc.neg()),
            Self::Prd(mut operands) => {
                operands.push(int(-1));
                Self::Prd(operands)
            }
            operand @ (Self::Sym(_)
            | Self::Fac(_)
            | Self::Sum(_)
            | Self::Pow(_, _)
            | Self::Fun(_, _)) => prd([int(-1), operand]),
            Self::Neg(_) | Self::Dif(_, _) | Self::Quo(_, _) => {
                panic!("Cannot simplify negation of {:#?}", operand)
            }
        }
    }
}
