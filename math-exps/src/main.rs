use std::cmp::Ordering;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Expr {
    Const(i32),
    Var(String),
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Pow(Box<Expr>, Box<Expr>),
}

impl Expr {
    pub fn canonicalize(&self) -> Self {
        match self {
            Expr::Add(e1, e2) => {
                let e1 = e1.canonicalize();
                let e2 = e2.canonicalize();
                if e1 == e2 {
                    Expr::Mul(Box::new(Expr::Const(2)), Box::new(e1))
                } else {
                    let mut terms = canonicalize_sum(&e1, &e2);
                    terms.sort();
                    merge_terms(terms)
                }
            }
            Expr::Mul(e1, e2) => {
                let e1 = e1.canonicalize();
                let e2 = e2.canonicalize();
                if e1 == e2 {
                    Expr::Pow(Box::new(e1), Box::new(Expr::Const(2)))
                } else {
                    Expr::Mul(Box::new(e1), Box::new(e2))
                }
            }
            Expr::Pow(e1, e2) => {
                let e1 = e1.canonicalize();
                let e2 = e2.canonicalize();
                Expr::Pow(Box::new(e1), Box::new(e2))
            }
            _ => self.clone(),
        }
    }
}

fn canonicalize_sum(e1: &Expr, e2: &Expr) -> Vec<Expr> {
    let mut terms = Vec::new();
    match e1 {
        Expr::Add(e1_a, e1_b) => {
            terms.extend(canonicalize_sum(e1_a, e1_b));
        }
        _ => terms.push(e1.clone()),
    }

    match e2 {
        Expr::Add(e2_a, e2_b) => {
            terms.extend(canonicalize_sum(e2_a, e2_b));
        }
        _ => terms.push(e2.clone()),
    }

    terms
}

fn merge_terms(terms: Vec<Expr>) -> Expr {
    let mut term_map = HashMap::new();
    for term in terms {
        let count = term_map.entry(term.clone()).or_insert(0);
        *count += 1;
    }

    let mut term_vec: Vec<(Expr, i32)> = term_map.into_iter().collect();
    term_vec.sort_by(|(e1, _), (e2, _)| e1.partial_cmp(e2).unwrap_or(Ordering::Equal));

    let mut merged_terms = Vec::new();
    for (expr, count) in term_vec {
        if count > 1 {
            merged_terms.push(Expr::Mul(Box::new(Expr::Const(count)), Box::new(expr)));
        } else {
            merged_terms.push(expr);
        }
    }

    if merged_terms.len() == 1 {
        merged_terms.pop().unwrap()
    } else {
        merged_terms
            .into_iter()
            .rev()
            .fold(None, |acc, x| match acc {
                Some(expr) => Some(Expr::Add(Box::new(x), Box::new(expr))),
                None => Some(x),
            })
            .unwrap()
    }
}

fn main() {
    // Example usage:
    let expr1 = Expr::Add(
        Box::new(Expr::Var("x".to_string())),
        Box::new(Expr::Var("y".to_string())),
    );
    let expr2 = Expr::Add(
        Box::new(Expr::Var("y".to_string())),
        Box::new(Expr::Var("x".to_string())),
    );
    let expr3 = Expr::Mul(
        Box::new(Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Var("y".to_string())),
        )),
        Box::new(Expr::Const(2)),
    );

    let canonical_expr1 = expr1.canonicalize();
    let canonical_expr2 = expr2.canonicalize();
    let canonical_expr3 = expr3.canonicalize();

    println!("Expression 1: {:?}", canonical_expr1);
    println!("Expression 2: {:?}", canonical_expr2);
    println!("Expression 3: {:?}", canonical_expr3);

    let x1 = Expr::Mul(Box::new(canonical_expr1), Box::new(canonical_expr2)).canonicalize();
    let x2 = Expr::Mul(Box::new(x1.clone()), Box::new(x1)).canonicalize();

    println!("{:#?}", x2);

    /*
    assert_eq!(canonical_expr1, canonical_expr2);
    assert_eq!(
        Expr::Mul(Box::new(canonical_expr1), Box::new(canonical_expr2)).canonicalize(),
        canonical_expr3
    );
    */
}
