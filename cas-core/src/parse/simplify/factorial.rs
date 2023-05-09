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
                    return int(1);
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

#[cfg(test)]
mod tests {
    use crate::parse::ast::{ast_helpers::*, test_helpers::test_simplified_src};

    #[test]
    fn simplify_pos_int_fac() {
        test_simplified_src("0!", int(1));
        test_simplified_src("1!", int(1));
        test_simplified_src("2!", int(2));
        test_simplified_src("3!", int(6));
        test_simplified_src("4!", int(24));
        test_simplified_src("5!", int(120));
        test_simplified_src("6!", int(720));
        test_simplified_src("7!", int(5040));
        test_simplified_src("8!", int(40320));
        test_simplified_src("9!", int(362880));
        test_simplified_src("10!", int(3628800));

        test_simplified_src("3!!", int(720));
        test_simplified_src("(2 + 3)!", int(120));
    }

    #[test]
    fn does_not_simplify_neg_int_fac() {
        test_simplified_src("(-1)!", fac(int(-1)));
        test_simplified_src("(-2)!", fac(int(-2)));
        test_simplified_src("(-3)!", fac(int(-3)));
        test_simplified_src("(-4)!", fac(int(-4)));
    }

    #[test]
    fn does_not_simplify_fraction_fac() {
        test_simplified_src("0.5!", fac(frc(1, 2)));
        test_simplified_src("(-0.5)!", fac(frc(-1, 2)));
        test_simplified_src("(1/2)!", fac(frc(1, 2)));
        test_simplified_src("(-1/2)!", fac(frc(-1, 2)));
    }

    #[test]
    fn does_not_simplify_symbol_fac() {
        test_simplified_src("x!", fac(sym("x")));
        test_simplified_src("(x + y)!", fac(sum([sym("x"), sym("y")])));
        test_simplified_src("(5 + x)!", fac(sum([int(5), sym("x")])));
        test_simplified_src("(5 * x)!", fac(prd([int(5), sym("x")])));
    }
}
