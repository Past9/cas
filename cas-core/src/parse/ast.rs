use crate::parse::ast::ast_helpers::{pow, sum};

use self::ast_helpers::{int, prd};
use num::{BigInt, BigRational, FromPrimitive, One, Zero};
use rust_decimal::Decimal;
use std::{
    borrow::{Borrow, Cow},
    cmp::Ordering,
    ops::Neg,
};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Ast {
    Und,
    Sym(String),
    Int(BigInt),
    Frc(BigRational),
    Neg(Box<Ast>),
    Fac(Box<Ast>),
    Sum(Vec<Ast>),
    Prd(Vec<Ast>),
    Dif(Box<Ast>, Box<Ast>),
    Quo(Box<Ast>, Box<Ast>),
    Pow(Box<Ast>, Box<Ast>),
}
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

    pub fn simplify(self) -> Self {
        match self {
            ast @ (Ast::Und | Ast::Sym(_) | Ast::Int(_)) => ast,
            Ast::Frc(frc) => Self::simplify_fraction(frc),
            Ast::Neg(operand) => Self::simplify_negation(*operand),
            Ast::Fac(operand) => Self::simplify_factorial(*operand),
            Ast::Sum(operands) => Self::simplify_sum(operands),
            Ast::Prd(operands) => Self::simplify_product(operands),
            Ast::Dif(l, r) => Self::simplify_difference(*l, *r),
            Ast::Quo(l, r) => Self::simplify_quotient(*l, *r),
            Ast::Pow(base, exp) => Self::simplify_power(*base, *exp),
        }
    }

    fn simplify_fraction(frc: BigRational) -> Self {
        Self::from_frac(frc)
    }

    fn simplify_negation(operand: Ast) -> Self {
        match operand {
            und @ Ast::Und => und,
            Ast::Int(int) => Self::from_int(int.neg()),
            Ast::Frc(frc) => Self::from_frac(frc.neg()),
            Ast::Prd(mut operands) => {
                operands.push(int(-1));
                Ast::Prd(operands)
            }
            operand @ (Ast::Sym(_) | Ast::Fac(_) | Ast::Sum(_) | Ast::Pow(_, _)) => {
                prd(int(-1), operand)
            }
            Ast::Neg(_) | Ast::Dif(_, _) | Ast::Quo(_, _) => {
                panic!("Cannot simplify negation of {:#?}", operand)
            }
        }
    }

    fn simplify_factorial(operand: Ast) -> Self {
        todo!()
    }

    fn simplify_sum(operands: Vec<Ast>) -> Self {
        todo!()
    }

    fn simplify_product_2(operands: Vec<Ast>) -> Self {
        if operands.len() == 0 {
            return int(1);
        }

        // Simplify all operands
        let operands = operands
            .into_iter()
            .map(Ast::simplify)
            .collect::<Vec<Ast>>();

        // SPRD-1
        if operands.iter().any(Ast::is_undefined) {
            return Ast::Und;
        }

        // SPRD-2
        if operands.iter().any(Ast::is_int_zero) {
            return int(0);
        }

        // SPRD-3
        if operands.len() == 1 {
            return operands.into_iter().next().unwrap();
        }

        // SPRD-4
        let operands = Self::simplify_product_rec(operands);

        // SPRD-4-3
        if operands.len() == 0 {
            return int(1);
        }

        // SPRD-4-1
        if operands.len() == 1 {
            return operands.into_iter().next().unwrap();
        }

        // SPRD-4-2
        if operands.len() >= 2 {
            return Self::Prd(operands);
        }

        panic!("Impossible branch");
    }

    fn simplify_product_rec(mut operands: Vec<Ast>) -> Vec<Ast> {
        if operands.len() < 2 {
            panic!("At least 2 operands required");
        }

        // SPRDREC-1
        if operands.len() == 2 && !operands[0].is_product() && !operands[1].is_product() {
            // SPRDREC-1-1
            let mut operands = {
                let (operands, both_consts) = match (&operands[0], &operands[1]) {
                    (Ast::Int(l), Ast::Int(r)) => (vec![Self::Int(l * r)], true),
                    (Ast::Frc(l), Ast::Frc(r)) => (vec![Self::from_frac(l * r)], true),

                    (Ast::Int(int), Ast::Frc(frc)) | (Ast::Frc(frc), Ast::Int(int)) => (
                        vec![Self::from_frac(
                            BigRational::from_integer(int.clone()) * frc,
                        )],
                        true,
                    ),

                    _ => (operands, false),
                };

                if both_consts {
                    if operands.len() == 1 && operands[0].is_int_one() {
                        return vec![];
                    } else {
                        return operands;
                    }
                }

                operands
            };

            // SPRDREC-1-2
            {
                if operands[0].is_int_one() {
                    return vec![operands.swap_remove(1)];
                }

                if operands[1].is_int_one() {
                    return vec![operands.into_iter().next().unwrap()];
                }
            };

            // SPRDREC-1-3
            {
                let (base_l, exp_l) = operands[0].as_power_operands();
                let (base_r, exp_r) = operands[1].as_power_operands();

                if base_l == base_r {
                    let exp = Self::simplify_sum(vec![exp_l.into_owned(), exp_r.into_owned()]);
                    let pow = Self::simplify_power(base_l.into_owned(), exp);

                    if pow.is_int_one() {
                        return vec![];
                    } else {
                        return vec![pow];
                    }
                }
            };

            // SPRDREC-1-4
            {
                if operands[1] < operands[0] {
                    operands.reverse();
                    return operands;
                }
            };

            // SPRDREC-1-5
            {
                return operands;
            };
        }

        // SPRDREC-2
        if operands.len() == 2 && (operands[0].is_product() || !operands[1].is_product()) {
            let mut iter = operands.into_iter();

            let l = iter.next().unwrap();
            let r = iter.next().unwrap();

            return match (l, r) {
                // SPRDREC-2-1
                (Ast::Prd(l), Ast::Prd(r)) => Self::merge_products(l, r),
                // SPRDREC-2-2
                (Ast::Prd(l), r) => Self::merge_products(l, vec![r]),
                // SPRDREC-2-3
                (l, Ast::Prd(r)) => Self::merge_products(vec![l], r),
                _ => panic!("At least one operand should be a product"),
            };
        }

        // SPRDREC-3
        let mut iter = operands.into_iter();
        let first = iter.next().unwrap();
        let remaining = Self::simplify_product_rec(iter.collect());

        match first {
            // SPRDREC-3-1
            Ast::Prd(operands) => Self::merge_products(operands, remaining),
            // SPRDREC-3-2
            operand => Self::merge_products(vec![operand], remaining),
        }
    }

    fn merge_products(p: Vec<Ast>, q: Vec<Ast>) -> Vec<Ast> {
        if p.len() == 0 && q.len() == 0 {
            return vec![int(1)];
        }

        // MPRD-1
        if q.len() == 0 {
            return p;
        }

        // MPRD-2
        if p.len() == 0 {
            return q;
        }

        // MPRD-3
        {
            let mut p_iter = p.clone().into_iter();
            let p1 = p_iter.next().unwrap();
            let remaining_p = p_iter.collect::<Vec<_>>();

            let mut q_iter = q.clone().into_iter();
            let q1 = q_iter.next().unwrap();
            let remaining_q = q_iter.collect::<Vec<_>>();

            let mut h = Self::simplify_product_rec(vec![p1.clone(), q1.clone()]);

            // MPRD-3-1
            if h.len() == 0 {
                return Self::merge_products(remaining_p, remaining_q);
            }

            // MPRD-3-2
            if h.len() == 1 {
                let mut merged = Self::merge_products(remaining_p, remaining_q);
                h.append(&mut merged);
                return h;
            }

            if h.len() == 2 {
                // MPRD-3-3
                if h[0] == p1 && h[1] == q1 {
                    return std::iter::once(p1)
                        .chain(Self::merge_products(remaining_p, q).into_iter())
                        .collect();
                }

                // MPRD-3-4
                if h[0] == q1 && h[1] == p1 {
                    return std::iter::once(q1)
                        .chain(Self::merge_products(p, remaining_q))
                        .into_iter()
                        .collect();
                }
            }
        }

        panic!("Impossible branch");
    }

    fn as_power_operands(&self) -> (Cow<Ast>, Cow<Ast>) {
        match self {
            operand @ (Ast::Und
            | Ast::Sym(_)
            | Ast::Int(_)
            | Ast::Frc(_)
            | Ast::Neg(_)
            | Ast::Fac(_)
            | Ast::Sum(_)
            | Ast::Prd(_)
            | Ast::Dif(_, _)
            | Ast::Quo(_, _)) => (Cow::Borrowed(operand), Cow::Owned(int(1))),
            Ast::Pow(base, exp) => (Cow::Borrowed(base), Cow::Borrowed(exp)),
        }
    }

    fn simplify_product(operands: Vec<Ast>) -> Self {
        let mut operands = operands
            .into_iter()
            // Simplify each operand first
            .map(|op| op.simplify())
            // Apply the Basic Associative Transformation
            // (flatten operands that are products)
            .flat_map(|op| match op {
                operand @ (Ast::Und
                | Ast::Sym(_)
                | Ast::Int(_)
                | Ast::Frc(_)
                | Ast::Fac(_)
                | Ast::Sum(_)
                | Ast::Pow(_, _)) => vec![operand].into_iter(),
                Ast::Prd(operands) => operands.into_iter(),

                operand @ (Ast::Neg(_) | Ast::Dif(_, _) | Ast::Quo(_, _)) => {
                    panic!("Cannot simplify product operand {:?}", operand)
                }
            })
            .collect::<Vec<Ast>>();

        // Apply the Basic Commutative Transformation
        // (reorder the operands to a standard form)
        operands.sort();

        // Apply the Basic Power Transformation
        // (combine like operands or powers with like bases into
        // single operands by summing their exponents)
        let operands = {
            let mut new_operands = Vec::new();
            let mut ops_iter = operands.into_iter();
            let (mut cur_base, mut total_exp) = match ops_iter.next().unwrap() {
                operand @ (Ast::Und
                | Ast::Sym(_)
                | Ast::Int(_)
                | Ast::Frc(_)
                | Ast::Neg(_)
                | Ast::Fac(_)
                | Ast::Sum(_)
                | Ast::Prd(_)
                | Ast::Dif(_, _)
                | Ast::Quo(_, _)) => (operand, int(1)),
                Ast::Pow(base, exp) => (*base, *exp),
            };

            for operand in ops_iter {
                let (base, exp) = match operand {
                    operand @ (Ast::Und
                    | Ast::Sym(_)
                    | Ast::Int(_)
                    | Ast::Frc(_)
                    | Ast::Neg(_)
                    | Ast::Fac(_)
                    | Ast::Sum(_)
                    | Ast::Prd(_)
                    | Ast::Dif(_, _)
                    | Ast::Quo(_, _)) => (operand, int(1)),
                    Ast::Pow(base, exp) => (*base, *exp),
                };

                if base == cur_base {
                    total_exp = sum(total_exp, exp);
                } else {
                    new_operands.push(pow(cur_base, total_exp));
                    cur_base = base;
                    total_exp = exp;
                }
            }

            new_operands.push(pow(cur_base, total_exp));

            new_operands = new_operands.into_iter().map(|op| op.simplify()).collect();

            new_operands.sort();

            new_operands
        };

        // Apply the Basic Numerical Transformation
        // (multiply all constant factors into a single constant)
        let mut operands = {
            let mut const_total = BigRational::from_i32(1).unwrap();
            let mut new_operands = Vec::new();
            for operand in operands.into_iter() {
                match operand {
                    Ast::Int(int) => {
                        const_total *= BigRational::from_integer(int);
                    }
                    Ast::Frc(frc) => {
                        const_total *= frc;
                    }
                    operand => new_operands.push(operand),
                }
            }

            new_operands.insert(0, Ast::from_frac(const_total));

            new_operands
        };

        // Basic Undefined Transformation
        // (if any operand is undefined, the entire product
        // is undefined)
        if operands.iter().any(|op| op.is_undefined()) {
            return Ast::Und;
        }

        if operands.len() == 0 {
            // Shouldn't happen, but a product with no factors
            // (not even a 1) is equal to zero
            return int(0);
        }

        // Basic Identity Transformation 3.21
        // (if a product contains the factor 0, the
        // whole thing equals 0)
        if operands.first().unwrap().is_int_zero() {
            return int(0);
        }

        // Basic Identity Tranformation 3.22
        // (if a product contains the factor 1, we can
        // remove that factor)
        if operands.first().unwrap().is_int_one() {
            operands.remove(0);
        }

        // Basic Unary Transformation
        // (if product has only one factor, just
        // return that factor)
        if operands.len() == 1 {
            return operands.into_iter().next().unwrap();
        }

        Ast::Prd(operands)
    }

    fn simplify_difference(l: Ast, r: Ast) -> Self {
        todo!()
    }

    fn simplify_quotient(l: Ast, r: Ast) -> Self {
        todo!()
    }

    fn simplify_power(base: Ast, exponent: Ast) -> Self {
        todo!()
    }

    pub fn is_undefined(&self) -> bool {
        match self {
            Ast::Und => true,
            _ => false,
        }
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

    pub fn is_product(&self) -> bool {
        match self {
            Ast::Prd(_) => true,
            _ => false,
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
            (Ast::Sum(s), Ast::Sum(o)) => compare_operands(s, o),
            (Ast::Prd(s), Ast::Prd(o)) => compare_operands(s, o),

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

            // O-7
            (Ast::Int(_), _) => Some(Ordering::Less),
            (Ast::Frc(_), _) => Some(Ordering::Less),
            (_, Ast::Int(_)) => Some(Ordering::Greater),
            (_, Ast::Frc(_)) => Some(Ordering::Greater),

            // O-8
            (Ast::Prd(s), o @ Ast::Pow(..))
            | (Ast::Prd(s), o @ Ast::Sum(..))
            | (Ast::Prd(s), o @ Ast::Fac(..))
            | (Ast::Prd(s), o @ Ast::Sym(..)) => compare_operands(s, &[o]),

            (s @ Ast::Pow(..), o @ Ast::Prd(..))
            | (s @ Ast::Sum(..), o @ Ast::Prd(..))
            | (s @ Ast::Fac(..), o @ Ast::Prd(..))
            | (s @ Ast::Sym(..), o @ Ast::Prd(..)) => o.partial_cmp(s).map(Ordering::reverse),

            // O-9
            (Ast::Pow(s_base, s_exp), o_base @ Ast::Sum(..))
            | (Ast::Pow(s_base, s_exp), o_base @ Ast::Fac(..))
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
            | (s @ Ast::Sym(..), o @ Ast::Pow(..)) => o.partial_cmp(s).map(Ordering::reverse),

            // O-10
            (Ast::Sum(s), o @ Ast::Fac(..)) | (Ast::Sum(s), o @ Ast::Sym(..)) => {
                compare_operands(s, &[o])
            }

            (s @ Ast::Fac(..), o @ Ast::Sum(..)) | (s @ Ast::Sym(..), o @ Ast::Sum(..)) => {
                o.partial_cmp(s).map(Ordering::reverse)
            }

            // O-11
            (Ast::Fac(s), o @ Ast::Sym(..)) => {
                if &**s == o {
                    Some(Ordering::Greater)
                } else {
                    // Revert to O-5. Rather than creating two factorials
                    // to compare, we just re-implement the logic here, which
                    // just compares the operands.
                    (&**s).partial_cmp(o)
                }
            }

            (s @ Ast::Sym(..), o @ Ast::Fac(..)) => o.partial_cmp(s).map(Ordering::reverse),

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

fn compare_operands<T: Borrow<Ast>, U: Borrow<Ast>>(l: &[T], r: &[U]) -> Option<Ordering> {
    let mut m = l.len() as isize;
    let mut n = r.len() as isize;

    // First iteration is O-1
    // Subsequent ones are O-2
    while m >= 0 && n >= 0 {
        if l[m as usize].borrow() == r[n as usize].borrow() {
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

pub mod ast_helpers {
    use num::{BigInt, BigRational, FromPrimitive};

    use super::Ast;

    pub fn fac(operand: Ast) -> Ast {
        Ast::Fac(Box::new(operand))
    }

    pub fn neg(operand: Ast) -> Ast {
        Ast::Neg(Box::new(operand))
    }

    pub fn sum(l: Ast, r: Ast) -> Ast {
        Ast::Sum(vec![l, r])
    }

    pub fn prd(l: Ast, r: Ast) -> Ast {
        Ast::Sum(vec![l, r])
    }

    pub fn dif(l: Ast, r: Ast) -> Ast {
        Ast::Dif(Box::new(l), Box::new(r))
    }

    pub fn quo(l: Ast, r: Ast) -> Ast {
        Ast::Quo(Box::new(l), Box::new(r))
    }

    pub fn pow(l: Ast, r: Ast) -> Ast {
        Ast::Pow(Box::new(l), Box::new(r))
    }

    pub fn sym(name: &str) -> Ast {
        Ast::Sym(name.to_owned())
    }

    pub fn int(int: i128) -> Ast {
        Ast::Int(BigInt::from_i128(int).unwrap())
    }

    pub fn frc(num: i128, den: i128) -> Ast {
        Ast::Frc(BigRational::new(
            BigInt::from_i128(num).unwrap(),
            BigInt::from_i128(den).unwrap(),
        ))
    }

    pub fn und() -> Ast {
        Ast::Und
    }
}
