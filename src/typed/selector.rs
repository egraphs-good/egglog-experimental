use super::{
    CallableRef, EgglogValue, Relation, SortRef, TypedError,
    builtins::Unit,
    expr::{Expr, Identity, NodeKind, ValueInput, variable},
};
use std::sync::Arc;

mod sealed {
    pub trait Selector<A> {}
    pub trait Arguments {}
}

/// Macro and callback adaptation, not a separate value family.
#[doc(hidden)]
pub trait CallRoot {
    type Output: EgglogValue;
    fn call_expression(&self) -> &Expr;
}
impl<I: ValueInput> CallRoot for I {
    type Output = I::Owned;
    fn call_expression(&self) -> &Expr {
        self.borrow().expression()
    }
}
impl CallRoot for Relation {
    type Output = Unit;
    fn call_expression(&self) -> &Expr {
        self.expression()
    }
}

impl CallRoot for &Relation {
    type Output = Unit;
    fn call_expression(&self) -> &Expr {
        self.expression()
    }
}

#[doc(hidden)]
pub struct Selection {
    pub(crate) callable: CallableRef,
    pub(crate) inputs: Vec<SortRef>,
    pub(crate) output: SortRef,
}
impl Selection {
    fn from_probe(root: &Expr, variables: &[Expr]) -> Result<Self, TypedError> {
        let NodeKind::Call(callable, children) = &root.node().kind else {
            return Err(TypedError::Invalid(
                "selector must return one direct call".into(),
            ));
        };
        if children != variables {
            return Err(TypedError::Invalid(
                "selector must use every fresh argument exactly once in declaration order".into(),
            ));
        }
        let inputs: Vec<_> = variables.iter().map(|x| x.node().sort.clone()).collect();
        let output = root.node().sort.clone();
        if let Some(source) = callable.source {
            let def = (source.resolve)();
            if def.inputs != inputs || def.output != output || def.callable != *callable {
                return Err(TypedError::Invalid(
                    "selector declaration signature does not match its call".into(),
                ));
            }
        }
        Ok(Self {
            callable: callable.clone(),
            inputs,
            output,
        })
    }
    pub(crate) fn validate(
        &self,
        callable: &CallableRef,
        inputs: &[SortRef],
        output: &SortRef,
    ) -> Result<bool, TypedError> {
        if self.callable.name != callable.name {
            return Ok(false);
        }
        if self.callable.kind != callable.kind {
            return Err(TypedError::Invalid(
                "same-named callable has an incompatible kind".into(),
            ));
        }
        if self.inputs != inputs || self.output != *output {
            return Err(TypedError::Invalid(
                "same-named callable has an incompatible signature".into(),
            ));
        }
        if let (Some(a), Some(b)) = (self.callable.source, callable.source)
            && (a.resolve)() != (b.resolve)()
        {
            return Err(TypedError::Invalid(
                "same-named callable has incompatible declaration options".into(),
            ));
        }
        if self.callable.source.is_some() != callable.source.is_some() {
            return Err(TypedError::Invalid("exact declaration options are unavailable for this native-only callable; use the heterogeneous frozen views".into()));
        }
        Ok(true)
    }
}

#[doc(hidden)]
pub trait SelectCall<A>: sealed::Selector<A> {
    type Root: CallRoot;
    fn select(self) -> Result<Selection, TypedError>;
}
#[doc(hidden)]
pub trait SelectedArgs: sealed::Arguments + Sized {
    fn decode(expressions: &[Expr]) -> Result<Self, TypedError>;
}

/// Inspect the exact root selected by a callback over fresh borrowed variables.
/// Invalid selectors return an error; a different root returns `None`.
/// The callback must pass every input exactly once, in order, to one root call.
/// Authored calls need no EGraph. Frozen classes must first select a constructor
/// node; its returned fields retain their original snapshot provenance.
pub fn get_args<N, F, A>(node: &N, selector: F) -> Result<Option<A>, TypedError>
where
    N: CallRoot,
    F: SelectCall<A, Root = N>,
    A: SelectedArgs,
{
    let selection = selector.select()?;
    let expression = node.call_expression();
    match &expression.node().kind {
        NodeKind::Call(callable, children) => {
            let inputs: Vec<_> = children.iter().map(|x| x.node().sort.clone()).collect();
            if !selection.validate(callable, &inputs, &expression.node().sort)? {
                return Ok(None);
            }
            A::decode(children).map(Some)
        }
        NodeKind::Frozen(reference) => reference
            .project(&selection)?
            .map(|args| A::decode(&args))
            .transpose(),
        _ => Ok(None),
    }
}

macro_rules! selector_adapter {
    ($($a:ident:$marker:ident:$index:tt),*) => {
        impl<F, $($a: EgglogValue,)* R: CallRoot> sealed::Selector<($($a,)*)> for F
        where F: for<'scope> FnOnce($(&'scope $a),*) -> R {}
        impl<F, $($a: EgglogValue,)* R: CallRoot> SelectCall<($($a,)*)> for F
        where F: for<'scope> FnOnce($(&'scope $a),*) -> R {
            type Root = R;
            fn select(self) -> Result<Selection, TypedError> {
                let scope = Identity(Arc::new(())); let _ = &scope;
                let variables = ($(variable::<$a>(scope.clone(), $index),)*); let _ = &variables;
                let root = self($(&variables.$index),*);
                if root.call_expression().node().sort != <R::Output as EgglogValue>::sort_ref() {
                    return Err(TypedError::Invalid("selector result does not have its Rust wrapper's exact sort".into()));
                }
                Selection::from_probe(root.call_expression(), &[$(variables.$index.expression().clone()),*])
            }
        }
        impl<$($a: EgglogValue),*> sealed::Arguments for ($($a,)*) {}
        impl<$($a: EgglogValue),*> SelectedArgs for ($($a,)*) {
            fn decode(expressions: &[Expr]) -> Result<Self, TypedError> {
                let expected = [$($a::sort_ref()),*];
                if expressions.len() != expected.len() || expressions.iter().zip(&expected).any(|(x,s)| &x.node().sort != s) {
                    return Err(TypedError::Decode("selected argument signature mismatch".into()));
                }
                Ok(($($a::from_expression(expressions[$index].clone()),)*))
            }
        }
    };
}
selector_adapter!();
for_arities!(selector_adapter);
