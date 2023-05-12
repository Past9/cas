use std::{borrow::Borrow, cmp::Ordering};

use crate::ast::{helpers::int, Ast};

pub(super) mod difference;
pub(super) mod factorial;
pub(super) mod fraction;
pub(super) mod function;
pub(super) mod negation;
pub(super) mod power;
pub(super) mod product;
pub(super) mod quotient;
pub(super) mod sum;

impl Ast {
    pub fn simplify(self) -> Self {
        match self {
            ast @ (Ast::Und | Ast::Sym(_) | Ast::Int(_)) => ast,
            Ast::Frc(frc) => Self::simplify_fraction(frc),
            Ast::Neg(operand) => Self::simplify_negation((*operand).simplify()),
            Ast::Fac(operand) => Self::simplify_factorial((*operand).simplify()),
            Ast::Sum(operands) => {
                Self::simplify_sum(operands.into_iter().map(|op| op.simplify()).collect())
            }
            Ast::Prd(operands) => {
                Self::simplify_product(operands.into_iter().map(|op| op.simplify()).collect())
            }
            Ast::Dif(l, r) => Self::simplify_difference((*l).simplify(), (*r).simplify()),
            Ast::Quo(l, r) => Self::simplify_quotient((*l).simplify(), (*r).simplify()),
            Ast::Pow(base, exp) => Self::simplify_power((*base).simplify(), (*exp).simplify()),
            Ast::Fun(name, args) => {
                Self::simplify_function(name, args.into_iter().map(|op| op.simplify()).collect())
            }
        }
    }
}
impl PartialOrd for Ast {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            // O-1
            (Ast::Int(s), Ast::Int(o)) => s.partial_cmp(o),
            (Ast::Frc(s), Ast::Frc(o)) => s.partial_cmp(o),
            (Ast::Int(s), Ast::Frc(o)) => (s * o.denom()).partial_cmp(o.numer()),
            (Ast::Frc(s), Ast::Int(o)) => s.numer().partial_cmp(&(o * s.denom())),

            // O-2
            (Ast::Sym(s), Ast::Sym(o)) => s.partial_cmp(o),

            // O-3
            (Ast::Sum(s), Ast::Sum(o)) => compare_operands(s, o, MostSignificantOperand::Right),
            (Ast::Prd(s), Ast::Prd(o)) => compare_operands(s, o, MostSignificantOperand::Right),

            // O-4
            (Ast::Pow(s_base, s_exp), Ast::Pow(o_base, o_exp)) => {
                if s_base != o_base {
                    // O-4-1
                    s_base.partial_cmp(o_base)
                } else {
                    // O-4-2
                    s_exp.partial_cmp(o_exp)
                }
            }

            // O-5
            (Ast::Fac(s), Ast::Fac(o)) => s.partial_cmp(o),

            // O-6
            (Ast::Fun(s_name, s_args), Ast::Fun(o_name, o_args)) => {
                if s_name == o_name {
                    compare_operands(s_args, o_args, MostSignificantOperand::Left)
                } else {
                    s_name.partial_cmp(o_name)
                }
            }

            // O-7
            (Ast::Int(_), _) => Some(Ordering::Less),
            (Ast::Frc(_), _) => Some(Ordering::Less),
            (_, Ast::Int(_)) => Some(Ordering::Greater),
            (_, Ast::Frc(_)) => Some(Ordering::Greater),

            // O-8
            (Ast::Prd(s), o @ Ast::Pow(..))
            | (Ast::Prd(s), o @ Ast::Sum(..))
            | (Ast::Prd(s), o @ Ast::Fac(..))
            | (Ast::Prd(s), o @ Ast::Fun(..))
            | (Ast::Prd(s), o @ Ast::Sym(..)) => {
                compare_operands(s, &[o], MostSignificantOperand::Right)
            }

            (s @ Ast::Pow(..), o @ Ast::Prd(..))
            | (s @ Ast::Sum(..), o @ Ast::Prd(..))
            | (s @ Ast::Fac(..), o @ Ast::Prd(..))
            | (s @ Ast::Fun(..), o @ Ast::Prd(..))
            | (s @ Ast::Sym(..), o @ Ast::Prd(..)) => o.partial_cmp(s).map(Ordering::reverse),

            // O-9
            (Ast::Pow(s_base, s_exp), o_base @ Ast::Sum(..))
            | (Ast::Pow(s_base, s_exp), o_base @ Ast::Fac(..))
            | (Ast::Pow(s_base, s_exp), o_base @ Ast::Fun(..))
            | (Ast::Pow(s_base, s_exp), o_base @ Ast::Sym(..)) => {
                // Treat other expression as exponent with power of one,
                // then user O-4 rules
                if &**s_base != o_base {
                    // O-4-1
                    (&**s_base).partial_cmp(o_base)
                } else {
                    // O-4-2
                    (&**s_exp).partial_cmp(&int(1))
                }
            }

            (s @ Ast::Sum(..), o @ Ast::Pow(..))
            | (s @ Ast::Fac(..), o @ Ast::Pow(..))
            | (s @ Ast::Fun(..), o @ Ast::Pow(..))
            | (s @ Ast::Sym(..), o @ Ast::Pow(..)) => o.partial_cmp(s).map(Ordering::reverse),

            // O-10
            (Ast::Sum(s), o @ Ast::Fac(..))
            | (Ast::Sum(s), o @ Ast::Fun(..))
            | (Ast::Sum(s), o @ Ast::Sym(..)) => {
                compare_operands(s, &[o], MostSignificantOperand::Right)
            }

            (s @ Ast::Fac(..), o @ Ast::Sum(..))
            | (s @ Ast::Fun(..), o @ Ast::Sum(..))
            | (s @ Ast::Sym(..), o @ Ast::Sum(..)) => o.partial_cmp(s).map(Ordering::reverse),

            // O-11
            (Ast::Fac(s), o @ Ast::Fun(..)) | (Ast::Fac(s), o @ Ast::Sym(..)) => {
                if &**s == o {
                    Some(Ordering::Greater)
                } else {
                    // Revert to O-5. Rather than creating two factorials
                    // to compare, we just re-implement the logic here, which
                    // just compares the operands.
                    (&**s).partial_cmp(o)
                }
            }

            (s @ Ast::Fun(..), o @ Ast::Fac(..)) | (s @ Ast::Sym(..), o @ Ast::Fac(..)) => {
                o.partial_cmp(s).map(Ordering::reverse)
            }

            // O-12
            (Ast::Fun(s_name, ..), Ast::Sym(o_name)) => {
                if s_name == o_name {
                    Some(Ordering::Greater)
                } else {
                    s_name.partial_cmp(o_name)
                }
            }

            (s @ Ast::Sym(..), o @ Ast::Fun(..)) => o.partial_cmp(s).map(Ordering::reverse),

            (Ast::Und, _) | (_, Ast::Und) => panic!("Cannot sort undefined"),
            (Ast::Neg(..), _) | (_, Ast::Neg(..)) => panic!("Cannot sort negation"),
            (Ast::Dif(..), _) | (_, Ast::Dif(..)) => panic!("Cannot sort subtraction"),
            (Ast::Quo(..), _) | (_, Ast::Quo(..)) => panic!("Cannot sort division"),
        }
    }
}
impl Ord for Ast {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other)
            .expect("Ast::partial_cmp returned None")
    }
}

enum MostSignificantOperand {
    Right,
    Left,
}

fn compare_operands<T: Borrow<Ast>, U: Borrow<Ast>>(
    l: &[T],
    r: &[U],
    mso: MostSignificantOperand,
) -> Option<Ordering> {
    let mut m = l.len() as isize - 1;
    let mut n = r.len() as isize - 1;

    // First iteration is O-1
    // Subsequent ones are O-2
    while m >= 0 && n >= 0 {
        let (l_index, r_index) = match mso {
            MostSignificantOperand::Right => (m, n),
            MostSignificantOperand::Left => (l.len() as isize - 1 - m, r.len() as isize - 1 - n),
        };

        if l[l_index as usize].borrow() == r[r_index as usize].borrow() {
            m -= 1;
            n -= 1;
            continue;
        } else {
            return l[m as usize].borrow().partial_cmp(&r[n as usize].borrow());
        }
    }

    // O-3 (longest operands wins)
    if l.len() == r.len() {
        Some(Ordering::Equal)
    } else {
        Some(l.len().cmp(&r.len()))
    }
}
