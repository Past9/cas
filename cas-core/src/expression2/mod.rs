use std::{
    collections::{BTreeSet, HashSet},
    iter::Product,
    ops::{Add, Mul, Neg},
};

use rust_decimal::prelude::ToPrimitive;

use crate::parse::ast::{con, Ast};

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Expr {
    Symbol(String),
    Integer(i128),
    Fraction(i128, i128),
    Product(ProductOperands),
    Sum(SumOperands),
}
impl Expr {
    pub fn from_ast(ast: Ast) -> Self {
        match ast {
            Ast::Symbol(name) => Self::Symbol(name),
            Ast::Constant(decimal) => {
                let rounded = decimal.round();
                if decimal == rounded {
                    // Decimal is an integer
                    Self::Integer(rounded.to_i128().unwrap())
                } else {
                    // Decimal is a fraction where the numerator is a power of 10
                    Self::simplify_fraction(decimal.mantissa(), 10i128.pow(decimal.scale()))
                }
            }
            Ast::UnaryOp(unary) => match unary.op {
                crate::parse::ast::UnaryOp::Neg => -Self::from_ast(*unary.operand),
                crate::parse::ast::UnaryOp::Fac => todo!(),
            },
            Ast::BinaryOp(binary) => match binary.op {
                crate::parse::ast::BinaryOp::Add => todo!(),
                crate::parse::ast::BinaryOp::Sub => todo!(),
                crate::parse::ast::BinaryOp::Mul => {
                    Self::from_ast(*binary.l) * Self::from_ast(*binary.r)
                }
                crate::parse::ast::BinaryOp::Div => todo!(),
                crate::parse::ast::BinaryOp::Exp => todo!(),
            },
        }
    }

    pub fn const_multiple_of(&self, expr: &Expr) -> Expr {
        match self {
            Expr::Product(operands) => {
                if operands.expr_operands.len() == 1 && operands.expr_operands.get(expr).is_some() {
                    match &operands.const_operand {
                        Some(const_operand) => (**const_operand).clone(),
                        None => Expr::Integer(1),
                    }
                } else {
                    Expr::Integer(0)
                }
            }
            other if other == expr => Expr::Integer(1),
            other => Expr::Integer(0),
        }
    }

    pub fn const_multiple_of_symbol(&self, name: &str) -> Expr {
        match self {
            Expr::Product(operands) => {
                if operands
                    .expr_operands
                    .get(&Expr::Symbol(name.into()))
                    .is_some()
                {
                    match &operands.const_operand {
                        Some(op) => (**op).clone(),
                        None => Expr::Integer(1),
                    }
                } else {
                    Expr::Integer(0)
                }
            }
            Expr::Symbol(sym_name) if sym_name == name => Expr::Integer(1),
            _ => Expr::Integer(0),
        }
    }

    pub fn is_const(&self) -> bool {
        match self {
            Expr::Integer(_) | Expr::Fraction(_, _) => true,
            _ => false,
        }
    }

    fn sum<const N: usize>(const_operand: Option<Expr>, expr_operands: [Expr; N]) -> Self {
        Self::Sum(SumOperands::new(const_operand, expr_operands))
    }

    fn product<const N: usize>(const_operand: Option<Expr>, expr_operands: [Expr; N]) -> Self {
        Self::Product(ProductOperands::new(const_operand, expr_operands))
    }

    fn simplify_fraction(numerator: i128, denominator: i128) -> Self {
        if denominator == 0 {
            panic!("Denominator cannot be zero");
        }

        if numerator == 0 {
            return Self::Integer(0);
        }

        // Make sure that only the numerator is ever negative
        let (num, den) = match (numerator.is_negative(), denominator.is_negative()) {
            (true, true) => (-numerator, -denominator),
            (true, false) => (numerator, denominator),
            (false, true) => (-numerator, -denominator),
            (false, false) => (numerator, denominator),
        };

        // Get the Greatest Common Divisor and simplify the fraction
        let gcd = gcd(num as u128, den as u128) as i128;

        let (num_div, num_rem) = (num / gcd, num % gcd);
        let (den_div, den_rem) = (den / gcd, den % gcd);

        let (simplified_num, simplified_den) = if num_rem == 0 && den_rem == 0 {
            (num_div, den_div)
        } else {
            (num, den)
        };

        if simplified_den == 1 {
            // If the denominator is 1, the fraction simplifies to an integer
            Self::Integer(simplified_num)
        } else {
            // Otherwise it's a fraction
            Self::simplify_fraction(simplified_num, simplified_den)
        }
    }
}
impl Neg for Expr {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            Expr::Symbol(symbol) => Expr::product(Some(Expr::Integer(-1)), [Expr::Symbol(symbol)]),
            Expr::Integer(integer) => Expr::Integer(-integer),
            Expr::Fraction(num, den) => Expr::Fraction(-num, den),
            Expr::Product(operands) => Expr::Product(operands) * Expr::Integer(-1),
            Expr::Sum(operands) => Expr::Sum(operands) * Expr::Integer(-1),
        }
    }
}
impl Add for Expr {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Expr::Symbol(l_name), Expr::Symbol(r_name)) => {
                if l_name == r_name {
                    Expr::product(Some(Expr::Integer(2)), [Expr::Symbol(l_name)])
                } else {
                    Expr::sum(None, [Expr::Symbol(l_name), Expr::Symbol(r_name)])
                }
            }

            (Expr::Integer(l_integer), Expr::Integer(r_integer)) => {
                Expr::Integer(l_integer + r_integer)
            }

            (Expr::Fraction(l_num, l_den), Expr::Fraction(r_num, r_den)) => {
                Expr::simplify_fraction(l_num * r_den + r_num * l_den, l_den * r_den)
            }

            (Expr::Product(l_operands), Expr::Product(r_operands)) => {
                if l_operands.expr_operands == r_operands.expr_operands {
                    // If all the non-const operands are the same, the result is the sum of
                    // the const operands times the non-const operands.
                    let const_operand = match (l_operands.const_operand, r_operands.const_operand) {
                        (None, None) => Expr::Integer(2),
                        (None, Some(r)) => Expr::Integer(1) + *r,
                        (Some(l), None) => *l + Expr::Integer(1),
                        (Some(l), Some(r)) => *l + *r,
                    };

                    // If the summed const operand is 1, don't include it
                    let const_operand = if const_operand == Expr::Integer(1) {
                        None
                    } else {
                        Some(Box::new(const_operand))
                    };

                    Expr::Product(ProductOperands {
                        const_operand,
                        expr_operands: l_operands.expr_operands,
                    })
                } else {
                    Expr::sum(None, [Expr::Product(l_operands), Expr::Product(r_operands)])
                }
            }

            (Expr::Sum(l_operands), Expr::Sum(r_operands)) => {
                // Add const operands.
                // Find all like non-const operands and convert them into
                // "2 * operand" products.
                todo!()
            }

            (Expr::Symbol(name), Expr::Integer(integer))
            | (Expr::Integer(integer), Expr::Symbol(name)) => {
                if integer == 0 {
                    Expr::Symbol(name)
                } else {
                    Expr::sum(Some(Expr::Integer(integer)), [Expr::Symbol(name)])
                }
            }

            (Expr::Symbol(name), Expr::Fraction(num, den))
            | (Expr::Fraction(num, den), Expr::Symbol(name)) => {
                Expr::sum(Some(Expr::Fraction(num, den)), [Expr::Symbol(name)])
            }

            (Expr::Symbol(name), Expr::Product(operands))
            | (Expr::Product(operands), Expr::Symbol(name)) => {
                // If the product operands are an optional const and the symbol,
                // increment the const. Otherwise return symbol + product.
                todo!()
            }

            (Expr::Integer(integer), Expr::Fraction(num, den))
            | (Expr::Fraction(num, den), Expr::Integer(integer)) => {
                if integer == 0 {
                    Expr::Fraction(num, den)
                } else {
                    Expr::simplify_fraction(num + integer * den, den)
                }
            }

            (Expr::Integer(integer), Expr::Product(operands))
            | (Expr::Product(operands), Expr::Integer(integer)) => {
                if integer == 0 {
                    Expr::Product(operands)
                } else {
                    //
                    todo!()
                }
            }

            (Expr::Fraction(num, den), Expr::Product(operands))
            | (Expr::Product(operands), Expr::Fraction(num, den)) => {
                todo!()
            }

            (Expr::Symbol(name), Expr::Sum(operands))
            | (Expr::Sum(operands), Expr::Symbol(name)) => todo!(),

            (Expr::Integer(integer), Expr::Sum(operands))
            | (Expr::Sum(operands), Expr::Integer(integer)) => {
                if integer == 0 {
                    Expr::Sum(operands)
                } else {
                    let integer = Expr::Integer(integer);
                    let const_operand = match operands.const_operand {
                        Some(const_operand) => *const_operand + integer,
                        None => integer,
                    };

                    let const_operand = if const_operand != Expr::Integer(1) {
                        Some(Box::new(const_operand))
                    } else {
                        None
                    };

                    Expr::Sum(SumOperands {
                        const_operand,
                        expr_operands: operands.expr_operands,
                    })
                }
            }

            (Expr::Fraction(num, den), Expr::Sum(operands))
            | (Expr::Sum(operands), Expr::Fraction(num, den)) => {
                let fraction = Expr::Fraction(num, den);
                let const_operand = match operands.const_operand {
                    Some(const_operand) => *const_operand + fraction,
                    None => fraction,
                };

                let const_operand = if const_operand != Expr::Integer(1) {
                    Some(Box::new(const_operand))
                } else {
                    None
                };

                Expr::Sum(SumOperands {
                    const_operand,
                    expr_operands: operands.expr_operands,
                })
            }

            (Expr::Product(product_operands), Expr::Sum(sum_operands))
            | (Expr::Sum(sum_operands), Expr::Product(product_operands)) => {
                todo!()
            }
        }
    }
}
impl Mul for Expr {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Expr::Symbol(l_name), Expr::Symbol(r_name)) => {
                if l_name == r_name {
                    // Symbol ^ 2
                    todo!()
                } else {
                    Expr::product(None, [Expr::Symbol(l_name), Expr::Symbol(r_name)])
                }
            }

            (Expr::Integer(l_integer), Expr::Integer(r_integer)) => {
                Expr::Integer(l_integer * r_integer)
            }

            (Expr::Fraction(l_num, l_den), Expr::Fraction(r_num, r_den)) => {
                Expr::simplify_fraction(l_num * r_num, l_den * r_den)
            }

            (Expr::Product(l_operands), Expr::Product(r_operands)) => {
                let mut product = Expr::Product(l_operands);

                if let Some(const_operand) = r_operands.const_operand {
                    product = product * *const_operand;
                }

                for operand in r_operands.expr_operands.into_iter() {
                    product = product * operand;
                }

                product
            }

            (Expr::Sum(_), Expr::Sum(_)) => todo!(),

            (Expr::Symbol(name), Expr::Integer(integer))
            | (Expr::Integer(integer), Expr::Symbol(name)) => {
                if integer == 0 {
                    Expr::Integer(0)
                } else if integer == 1 {
                    Expr::Symbol(name)
                } else {
                    Expr::product(Some(Expr::Integer(integer)), [Expr::Symbol(name)])
                }
            }

            (Expr::Symbol(name), Expr::Fraction(numerator, denominator))
            | (Expr::Fraction(numerator, denominator), Expr::Symbol(name)) => Expr::product(
                Some(Expr::Fraction(numerator, denominator)),
                [Expr::Symbol(name)],
            ),

            (Expr::Symbol(name), Expr::Product(operands))
            | (Expr::Product(operands), Expr::Symbol(name)) => {
                for operand in operands.expr_operands.iter() {
                    if let Expr::Symbol(ref operand_name) = operand {
                        if *operand_name == name {
                            // return product with Symbol -> Symbol ^ 2
                            todo!()
                        }
                    }
                }

                let mut operands = operands;
                operands.expr_operands.insert(Expr::Symbol(name));
                Expr::Product(operands)
            }

            (Expr::Integer(integer), Expr::Fraction(num, den))
            | (Expr::Fraction(num, den), Expr::Integer(integer)) => {
                Expr::simplify_fraction(num * integer, den)
            }

            (Expr::Integer(integer), Expr::Product(operands))
            | (Expr::Product(operands), Expr::Integer(integer)) => {
                if integer == 0 {
                    return Expr::Integer(0);
                }

                if integer == 1 {
                    return Expr::Product(operands);
                }

                let const_operand = match operands.const_operand {
                    Some(expr) => *expr * Expr::Integer(integer),
                    None => Expr::Integer(integer),
                };

                let const_operand = if const_operand == Expr::Integer(1) {
                    None
                } else {
                    Some(const_operand)
                };

                if const_operand.is_none() && operands.expr_operands.len() == 1 {
                    operands.expr_operands.into_iter().find(|_| true).unwrap()
                } else {
                    Expr::Product(ProductOperands {
                        const_operand: const_operand.map(Box::new),
                        expr_operands: operands.expr_operands,
                    })
                }
            }

            (Expr::Fraction(num, den), Expr::Product(operands))
            | (Expr::Product(operands), Expr::Fraction(num, den)) => {
                let const_operand = match operands.const_operand {
                    Some(expr) => *expr * Expr::Fraction(num, den),
                    None => Expr::Fraction(num, den),
                };

                let const_operand = if const_operand == Expr::Integer(1) {
                    None
                } else {
                    Some(const_operand)
                };

                if const_operand.is_none() && operands.expr_operands.len() == 1 {
                    operands.expr_operands.into_iter().find(|_| true).unwrap()
                } else {
                    Expr::Product(ProductOperands {
                        const_operand: const_operand.map(Box::new),
                        expr_operands: operands.expr_operands,
                    })
                }
            }

            (Expr::Symbol(name), Expr::Sum(operands))
            | (Expr::Sum(operands), Expr::Symbol(name)) => {
                Expr::product(None, [Expr::Symbol(name), Expr::Sum(operands)])
            }

            (Expr::Integer(integer), Expr::Sum(operands))
            | (Expr::Sum(operands), Expr::Integer(integer)) => {
                Expr::product(Some(Expr::Integer(integer)), [Expr::Sum(operands)])
            }

            (Expr::Fraction(num, den), Expr::Sum(operands))
            | (Expr::Sum(operands), Expr::Fraction(num, den)) => {
                Expr::product(Some(Expr::Fraction(num, den)), [Expr::Sum(operands)])
            }

            (Expr::Product(product_operands), Expr::Sum(sum_operands))
            | (Expr::Sum(sum_operands), Expr::Product(product_operands)) => {
                let mut expr_operands = product_operands.expr_operands;
                expr_operands.insert(Expr::Sum(sum_operands));
                Expr::Product(ProductOperands {
                    const_operand: product_operands.const_operand,
                    expr_operands: expr_operands,
                })
            }
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct ProductOperands {
    const_operand: Option<Box<Expr>>,
    expr_operands: BTreeSet<Expr>,
}
impl ProductOperands {
    fn new<const N: usize>(const_operand: Option<Expr>, expr_operands: [Expr; N]) -> Self {
        ProductOperands {
            const_operand: const_operand.map(Box::new),
            expr_operands: BTreeSet::from(expr_operands),
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct SumOperands {
    const_operand: Option<Box<Expr>>,
    expr_operands: BTreeSet<Expr>,
}
impl SumOperands {
    fn new<const N: usize>(const_operand: Option<Expr>, expr_operands: [Expr; N]) -> Self {
        SumOperands {
            const_operand: const_operand.map(Box::new),
            expr_operands: BTreeSet::from(expr_operands),
        }
    }

    /*
    fn find_const_multiple_of(&mut self, expr: &Expr) -> Option<&Expr> {
        self.expr_operands.iter().find(|op| {
            if let Expr::Product(operands) = op {
                if operands.len() == 2 {
                    if &operands[1] == expr {
                        if operands[0].is_const() {
                            true
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                } else {
                    false
                }
            } else {
                false
            }
        })
    }
    */

    /*
    fn add(&mut self, expr: Expr) {
        match expr {
            Expr::Symbol(name) => {
                let symbol = Expr::Symbol(name);
                if self.expr_operands.contains(&symbol) {
                    self.expr_operands.remove(&symbol);
                    self.expr_operands
                        .insert(Expr::Product(vec![Expr::Integer(2), symbol]));
                } else if let Some(const_multiple) = self.find_const_multiple_of(&symbol) {
                    self.expr_operands.remove(const_multiple);
                    self.expr_operands
                        .insert(const_multiple * Expr::Integer(()))
                }
            }
            Expr::Integer(_) => todo!(),
            Expr::Fraction(_, _) => todo!(),
            Expr::Product(_) => todo!(),
            Expr::Sum(_) => todo!(),
        };
    }
    */
}

/*
fn sum_operands(operands: Vec<Expr>) -> SumOperands {
    let mut const_operand = None;
    let mut expr_operands = BTreeSet::new();

    for (i, operand) in operands.into_iter().enumerate() {
        if i == 0 {
            if let Expr::Integer(integer) = operand {
                const_operand = Some(Box::new(Expr::Integer(integer)));
                continue;
            } else if let Expr::Fraction(num, den) = operand {
                const_operand = Some(Box::new(Expr::Fraction(num, den)));
                continue;
            }
        }

        expr_operands.insert(operand);
    }

    SumOperands {
        const_operand,
        expr_operands,
    }
}
impl Add<Expr> for SumOperands {
    type Output = Expr;

    fn add(self, rhs: Expr) -> Self::Output {
        match rhs {
            Expr::Symbol(name) => todo!(),
            Expr::Integer(integer) => todo!(),
            Expr::Fraction(num, den) => todo!(),
            Expr::Product(operands) => todo!(),
            Expr::Sum(operands) => todo!(),
        }
    }
}
*/

pub(crate) fn gcd(a: u128, b: u128) -> u128 {
    let mut a = a;
    let mut b = b;
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }

    a
}
