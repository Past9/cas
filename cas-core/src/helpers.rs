use num::{BigInt, BigRational, One, Signed, Zero};
use rust_decimal::Decimal;

use crate::ast::Ast;

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

    pub fn has(&self, ast: &Ast) -> bool {
        if self == ast {
            true
        } else {
            match self {
                Ast::Neg(operand) => operand.has(ast),
                Ast::Fac(operand) => operand.has(ast),
                Ast::Sum(operands) => operands.iter().any(|op| op.has(ast)),
                Ast::Prd(operands) => operands.iter().any(|op| op.has(ast)),
                Ast::Dif(l, r) => l.has(ast) || r.has(ast),
                Ast::Quo(l, r) => l.has(ast) || r.has(ast),
                Ast::Pow(base, exp) => base.has(ast) || exp.has(ast),
                Ast::Fun(_, args) => args.iter().any(|op| op.has(ast)),

                Ast::Und | Ast::Sym(_) | Ast::Int(_) | Ast::Frc(_) => false,
            }
        }
    }

    pub fn is_free_of(&self, ast: &Ast) -> bool {
        !self.has(ast)
    }
}

#[cfg(test)]
fn expect_ast(src: &str) -> Ast {
    let result = crate::parse::parse_src(src);
    result.ast.unwrap()
}

#[cfg(test)]
pub fn test_src(src: &str, expected: Ast) {
    assert_eq!(expect_ast(src), expected)
}

#[cfg(test)]
pub fn test_simplified_src(src: &str, expected: Ast) {
    assert_eq!(expect_ast(src).simplify(), expected)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::helpers::*;

    #[test]
    fn ast_has() {
        let ast = expect_ast("x + 2");
        assert!(ast.has(&sum([sym("x"), int(2)])));
        assert!(ast.has(&sym("x")));
        assert!(ast.has(&int(2)));

        assert!(!ast.has(&sum([int(2), sym("x")])));
        assert!(!ast.has(&sym("y")));
        assert!(!ast.has(&int(3)));
    }

    #[test]
    fn ast_is_free_of() {
        let ast = expect_ast("x + 2");
        assert!(!ast.is_free_of(&sum([sym("x"), int(2)])));
        assert!(!ast.is_free_of(&sym("x")));
        assert!(!ast.is_free_of(&int(2)));

        assert!(ast.is_free_of(&sum([int(2), sym("x")])));
        assert!(ast.is_free_of(&sym("y")));
        assert!(ast.is_free_of(&int(3)));
    }
}
