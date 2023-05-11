use std::borrow::Cow;

use num::BigRational;

use crate::parse::ast::{ast_helpers::int, Ast};

impl Ast {
    pub(crate) fn simplify_sum(operands: Vec<Ast>) -> Self {
        if operands.len() == 0 {
            return int(0);
        }

        // SSUM-1
        if operands.iter().any(Ast::is_undefined) {
            return Ast::Und;
        }

        // No SSUM-2 because there is no analogue of SPRD-2

        // SSUM-3
        if operands.len() == 1 {
            return operands.into_iter().next().unwrap();
        }

        // SSUM-4
        let operands = Self::simplify_sum_rec(operands);

        // SSUM-4-3
        if operands.len() == 0 {
            return int(0);
        }

        // SSUM-4-1
        if operands.len() == 1 {
            return operands.into_iter().next().unwrap();
        }

        // SSUM-4-2
        if operands.len() >= 2 {
            return Self::Sum(operands);
        }

        unreachable!();
    }

    fn simplify_sum_rec(operands: Vec<Ast>) -> Vec<Ast> {
        if operands.len() < 2 {
            panic!("At least 2 operands required");
        }

        // SSUMREC-1
        if operands.len() == 2 && !operands[0].is_sum() && !operands[1].is_sum() {
            // SSUMREC-1-1
            let mut operands = {
                let (operands, both_consts) = match (&operands[0], &operands[1]) {
                    (Ast::Int(l), Ast::Int(r)) => (vec![Self::Int(l + r)], true),
                    (Ast::Frc(l), Ast::Frc(r)) => (vec![Self::from_frac(l + r)], true),

                    (Ast::Int(int), Ast::Frc(frc)) | (Ast::Frc(frc), Ast::Int(int)) => (
                        vec![Self::from_frac(
                            BigRational::from_integer(int.clone()) + frc,
                        )],
                        true,
                    ),

                    _ => (operands, false),
                };

                if both_consts {
                    if operands.len() == 1 && operands[0].is_int_zero() {
                        return vec![];
                    } else {
                        return operands;
                    }
                }

                operands
            };

            // SSUMREC-1-2
            {
                if operands[0].is_int_zero() {
                    return vec![operands.swap_remove(1)];
                }

                if operands[1].is_int_zero() {
                    return vec![operands.into_iter().next().unwrap()];
                }
            };

            // SSUMREC-1-3
            {
                let (l_factor, l_constant) = operands[0].as_multiple();
                let (r_factor, r_constant) = operands[1].as_multiple();

                if l_factor == r_factor {
                    let multiple = Self::simplify_product(vec![
                        Self::simplify_sum(vec![l_constant.into_owned(), r_constant.into_owned()]),
                        l_factor.into_owned(),
                    ]);

                    if multiple.is_int_zero() {
                        return vec![];
                    } else {
                        return vec![multiple];
                    }
                }
            }

            // SSUMREC-1-4
            {
                if operands[1] < operands[0] {
                    operands.reverse();
                    return operands;
                }
            }

            // SSUMREC-1-5
            {
                return operands;
            }
        }

        // SSUMREC-2
        if operands.len() == 2 && (operands[0].is_sum() || operands[1].is_sum()) {
            let mut iter = operands.into_iter();

            let l = iter.next().unwrap();
            let r = iter.next().unwrap();

            return match (l, r) {
                // SSUMREC-2-1
                (Ast::Sum(l), Ast::Sum(r)) => Self::merge_sums(l, r),
                // SSUMREC-2-2
                (Ast::Sum(l), r) => Self::merge_sums(l, vec![r]),
                // SSUMREC-2-3
                (l, Ast::Sum(r)) => Self::merge_sums(vec![l], r),
                _ => unreachable!(),
            };
        }

        // SSUMREC-3
        let mut iter = operands.into_iter();
        let first = iter.next().unwrap();
        let remaining = Self::simplify_sum_rec(iter.collect());

        match first {
            // SSUMREC-3-1
            Ast::Sum(operands) => Self::merge_sums(operands, remaining),
            // SSUMREC-3-2
            operand => Self::merge_sums(vec![operand], remaining),
        }
    }

    fn merge_sums(p: Vec<Ast>, q: Vec<Ast>) -> Vec<Ast> {
        // MSUM-1
        if q.len() == 0 {
            return p;
        }

        // MSUM-2
        if p.len() == 0 {
            return q;
        }

        // MSUM-3
        {
            let mut p_iter = p.clone().into_iter();
            let p1 = p_iter.next().unwrap();
            let remaining_p = p_iter.collect::<Vec<_>>();

            let mut q_iter = q.clone().into_iter();
            let q1 = q_iter.next().unwrap();
            let remaining_q = q_iter.collect::<Vec<_>>();

            let mut h = Self::simplify_sum_rec(vec![p1.clone(), q1.clone()]);

            // MSUM-3-1
            if h.len() == 0 {
                return Self::merge_sums(remaining_p, remaining_q);
            }

            // MSUM-3-2
            if h.len() == 1 {
                let mut merged = Self::merge_sums(remaining_p, remaining_q);
                h.append(&mut merged);
                return h;
            }

            if h.len() == 2 {
                // MSUM-3-3
                if h[0] == p1 && h[1] == q1 {
                    return std::iter::once(p1)
                        .chain(Self::merge_sums(remaining_p, q).into_iter())
                        .collect();
                }

                // MSUM-3-4
                if h[0] == q1 && h[1] == p1 {
                    return std::iter::once(q1)
                        .chain(Self::merge_sums(p, remaining_q))
                        .into_iter()
                        .collect();
                }
            }
        }

        unreachable!()
    }

    /// Returns a representation of `self` as a multiple of some constant.
    /// If `self` is a multiple of two operands and one is a constant, returns `(non_const_factor, const_factor)`.
    /// If `self` is a multiple of more than two operands and one is a constant, returns `(Ast::Prd(non_const_factors), const_factor)`.
    /// Otherwise, returns `(self, 1)`.
    fn as_multiple(&self) -> (Cow<Ast>, Cow<Ast>) {
        match self {
            operand @ (Ast::Und
            | Ast::Sym(_)
            | Ast::Int(_)
            | Ast::Frc(_)
            | Ast::Neg(_)
            | Ast::Fac(_)
            | Ast::Sum(_)
            | Ast::Dif(_, _)
            | Ast::Quo(_, _)
            | Ast::Fun(_, _)
            | Ast::Pow(_, _)) => (Cow::Borrowed(operand), Cow::Owned(int(1))),
            prd @ Ast::Prd(factors) => {
                if factors.len() == 2 && factors[0].is_const() {
                    return (Cow::Borrowed(&factors[1]), Cow::Borrowed(&factors[0]));
                }

                if factors.len() > 2 && factors[0].is_const() {
                    return (
                        Cow::Owned(Ast::Prd(factors.iter().skip(1).cloned().collect()).simplify()),
                        Cow::Borrowed(&factors[0]),
                    );
                }

                (Cow::Borrowed(prd), Cow::Owned(int(1)))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::parse::ast::{ast_helpers::*, test_helpers::test_simplified_src};

    #[test]
    fn simplify_const_sum() {
        test_simplified_src("1 + 2", int(3));
        test_simplified_src("0.5 + 2", frc(5, 2));
        test_simplified_src("0.5 + -2", frc(-3, 2));
        test_simplified_src("-0.5 + 2", frc(3, 2));
        test_simplified_src("1 + -1", int(0));
        test_simplified_src("0.5 + -0.5", int(0));
        test_simplified_src("1/2 + -1/2", int(0));
    }

    #[test]
    fn simplify_symbol_sum() {
        test_simplified_src("0.5 + x + 2", sum([frc(5, 2), sym("x")]));
        test_simplified_src("0.5 + -x + 2", sum([frc(5, 2), prd([int(-1), sym("x")])]));
        test_simplified_src("1 / x + 2 / x", prd([int(3), pow(sym("x"), int(-1))]));
        test_simplified_src(
            "1 / (2 * x) + 2 / x",
            prd([frc(5, 2), pow(sym("x"), int(-1))]),
        );
    }

    #[test]
    fn adds_multiples() {
        test_simplified_src("(2 * x) + (3 * x)", prd([int(5), sym("x")]));
        test_simplified_src("(-2 * x) + (3 * x)", sym("x"));
        test_simplified_src("(2 * x) + (2 * -x)", int(0));
        test_simplified_src("(2 * x) + (3 * -x)", prd([int(-1), sym("x")]));
    }

    #[test]
    fn add_sub_ltr() {
        // Ensures addition and subtration are parsed left-to-right at the same precedence
        // instead of prioritizing one over the other, which can give incorrect/unexpected results.
        test_simplified_src("2 + 3 - 4 + 5", int(6));
        test_simplified_src("2 - 3 + 4 - 5", int(-2));
    }
}
