use num::{traits::Pow, ToPrimitive};

use crate::ast::Ast;

impl Ast {
    pub fn eval(self) -> f64 {
        match self {
            Ast::Fail => panic!("Tried to eval Ast::Fail"),
            Ast::Und => panic!("Tried to eval Ast::Und"),
            Ast::Sym(name) => panic!("Tried toe val symbol `{}`", name),
            Ast::Int(int) => int.to_f64().unwrap(),
            Ast::Frc(frc) => frc.to_f64().unwrap(),
            Ast::Neg(operand) => -operand.eval(),
            Ast::Fac(operand) => panic!("Tried to eval factorial of {:?}", operand),
            Ast::Sum(operands) => operands.into_iter().map(Self::eval).sum(),
            Ast::Prd(operands) => operands.into_iter().map(Self::eval).product(),
            Ast::Dif(l, r) => l.eval() - r.eval(),
            Ast::Quo(l, r) => l.eval() / r.eval(),
            Ast::Pow(base, exp) => base.eval().pow(exp.eval()),
            Ast::Fun(name, _) => panic!("Tried to eval function `{}`", name),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::helpers::expect_ast;

    #[test]
    fn evals_arithmetic() {
        assert_eq!(expect_ast("2 * 3.5").simplify().eval(), 7f64);
        assert_eq!(expect_ast("2.5 ^ 2").simplify().eval(), 6.25);
        assert_eq!(expect_ast("2 ^ (1/2) / 2 ^ (1/2)").simplify().eval(), 1f64);
        assert_eq!(
            expect_ast("(4 ^ (1/2)) / (16 ^ (1/2))").simplify().eval(),
            0.5f64
        );
        assert_eq!(expect_ast("2^(1/2)").simplify().eval(), 2f64.sqrt());
        assert_eq!(
            expect_ast("2 * 2^(1/2)").simplify().eval(),
            2f64 * 2f64.sqrt()
        );
    }
}
