use num::BigUint;
use vec1::vec1;

use super::{constant::Constant, product::Product, Expr};

#[derive(Debug, PartialEq, Eq)]
pub struct Factorial {
    operand: Box<Expr>,
}
impl Factorial {
    pub(crate) fn unenforced(expr: Expr) -> Expr {
        Expr::Factorial(Factorial {
            operand: Box::new(expr),
        })
    }

    pub fn new(operand: Expr) -> Expr {
        match operand {
            Expr::Constant(constant) => {
                if constant.is_pos_int() {
                    let factorial = int_factorial(constant.expect_pos_int());
                    Constant::from_int(factorial.into()).as_expr()
                } else if constant.is_zero() {
                    Constant::from_int(0.into()).as_expr()
                } else {
                    Self {
                        operand: Box::new(constant.as_expr()),
                    }
                    .as_expr()
                }
            }
            operand => Self {
                operand: Box::new(operand),
            }
            .as_expr(),
        }
    }

    pub fn as_expr(self) -> Expr {
        Expr::Factorial(self)
    }

    pub fn negate(self) -> Expr {
        Product::new(Constant::neg_one(), vec1![self.into()])
    }
}

fn int_factorial(uint: BigUint) -> BigUint {
    if uint == 1u32.into() {
        return 1u32.into();
    } else {
        return &uint * int_factorial(&uint - BigUint::from(1u32));
    }
}
