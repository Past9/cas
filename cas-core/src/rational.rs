use crate::ast::{
    helpers::{int, pow, prd},
    Ast,
};

#[derive(PartialEq, Debug)]
pub struct NumDen {
    pub num: Ast,
    pub den: Ast,
}
impl NumDen {
    pub fn new(num: Ast, den: Ast) -> Self {
        Self { num, den }
    }
}

impl Ast {
    pub fn num_den(self) -> Option<NumDen> {
        match self {
            Ast::Und => None,

            // ND-1
            Ast::Frc(frc) => Some(NumDen::new(
                Ast::Int(frc.numer().clone()),
                Ast::Int(frc.denom().clone()),
            )),

            // ND-2
            Ast::Pow(base, exp) => {
                if exp.is_neg_const() {
                    Some(NumDen::new(
                        int(1),
                        pow(Ast::Pow(base, exp), int(-1)).simplify(),
                    ))
                } else {
                    Some(NumDen::new(Ast::Pow(base, exp), int(1)))
                }
            }

            // ND-3
            Ast::Prd(operands) => {
                let mut iter = operands.into_iter();
                let first = iter.next().unwrap();
                let rest = Ast::Prd(iter.collect()).simplify();

                let (first_num, first_den) = {
                    if let Some(NumDen { num, den }) = first.num_den() {
                        (num, den)
                    } else {
                        return None;
                    }
                };

                let (rest_num, rest_den) = {
                    if let Some(NumDen { num, den }) = rest.num_den() {
                        (num, den)
                    } else {
                        return None;
                    }
                };

                Some(NumDen::new(
                    prd([first_num, rest_num]).simplify(),
                    prd([first_den, rest_den]).simplify(),
                ))
            }

            // ND-4
            _ => Some(NumDen::new(self, int(1))),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{helpers::expect_ast, rational::NumDen};

    #[test]
    fn gets_num_and_den() {
        assert_eq!(
            expect_ast("(2/3) * ((x * (x + 1)) / (x + 2)) * y^n")
                .simplify()
                .num_den(),
            Some(NumDen::new(
                expect_ast("2 * x * (x + 1) * y ^ n").simplify(),
                expect_ast("3 * (x + 2)").simplify(),
            ))
        );
    }
}
