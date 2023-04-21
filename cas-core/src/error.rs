use std::{collections::HashSet, hash::Hash};

#[derive(Debug, Clone, PartialEq)]
pub enum SyntaxErrorReason<I> {
    Unexpected,
    Unclosed { span: crate::Span, delimiter: I },
    Custom(String),
}

#[derive(Debug, Clone, PartialEq)]
pub struct SyntaxError<I: Hash + Eq> {
    span: crate::Span,
    reason: SyntaxErrorReason<I>,
    expected: HashSet<Option<I>>,
    found: Option<I>,
    label: Option<String>,
}
impl<I: Hash + Eq> SyntaxError<I> {
    pub fn custom<M: ToString>(span: crate::Span, msg: M) -> Self {
        Self {
            span,
            reason: SyntaxErrorReason::Custom(msg.to_string()),
            expected: HashSet::default(),
            found: None,
            label: None,
        }
    }

    pub fn span(&self) -> crate::Span {
        self.span.clone()
    }

    pub fn expected(&self) -> impl ExactSizeIterator<Item = &Option<I>> + '_ {
        self.expected.iter()
    }

    pub fn found(&self) -> Option<&I> {
        self.found.as_ref()
    }

    pub fn reason(&self) -> &SyntaxErrorReason<I> {
        &self.reason
    }

    pub fn label(&self) -> Option<String> {
        self.label.clone()
    }
}
impl<I: Hash + Eq + Clone> chumsky::Error<I> for SyntaxError<I> {
    type Span = crate::Span;
    type Label = String;

    fn expected_input_found<Iter: IntoIterator<Item = Option<I>>>(
        span: Self::Span,
        expected: Iter,
        found: Option<I>,
    ) -> Self {
        Self {
            span,
            reason: SyntaxErrorReason::Unexpected,
            expected: expected.into_iter().collect(),
            found,
            label: None,
        }
    }

    fn with_label(mut self, label: Self::Label) -> Self {
        self.label.get_or_insert(label);
        self
    }

    fn merge(mut self, other: Self) -> Self {
        self.reason = match (&self.reason, &other.reason) {
            (SyntaxErrorReason::Unclosed { .. }, _) => self.reason,
            (_, SyntaxErrorReason::Unclosed { .. }) => other.reason,
            _ => self.reason,
        };
        for expected in other.expected {
            self.expected.insert(expected);
        }
        self
    }
}
