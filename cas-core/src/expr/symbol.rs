use super::{constant::Constant, product::Product, Expr};
use vec1::vec1;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Symbol {
    name: String,
}
impl Symbol {
    pub(crate) fn unenforced(name: &str) -> Expr {
        Expr::Symbol(Self { name: name.into() })
    }

    pub fn new(name: String) -> Self {
        Self { name }
    }

    pub fn as_expr(self) -> Expr {
        Expr::Symbol(self)
    }

    pub fn negate(self) -> Expr {
        Product::new(Constant::neg_one(), vec1![self.into()])
    }
}
