#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Token {
    Const(String),
    Ident(String),
    Comma,
    OpenParen,
    CloseParen,
    Plus,
    Minus,
    Asterisk,
    FwdSlash,
    Caret,
    Bang,
    Undefined,
}
