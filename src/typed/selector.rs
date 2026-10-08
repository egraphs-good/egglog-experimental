use super::{
    EgglogValue, TypedError,
    expr::{Expr, fresh_scope, variable},
    rule::ensure_sort,
};

#[doc(hidden)]
pub trait Selector<N, A> {
    fn select(self, node: &N) -> Result<Option<A>, TypedError>;
}

/// Inspect an exact constructor using a callback over its argument sorts.
/// Children retain their original owners. A different constructor returns None;
/// same-name incompatible declarations or reordered selectors are errors.
pub fn get_args<N: EgglogValue, A>(
    node: &N,
    selector: impl Selector<N, A>,
) -> Result<Option<A>, TypedError> {
    let record = &node.expression().0;
    let value = &record.owner.as_ref().unwrap().program.nodes[record.index as usize];
    if super::SortRef(record.resolve(super::storage::Arena::Sort, value.sort_id)?) != N::sort_ref()
    {
        return Err(TypedError::Invalid(
            "selector root has another sort than its Rust wrapper".into(),
        ));
    }
    selector.select(node)
}

macro_rules! selectors {
    ($($t:ident:$i:tt),*) => {
        impl<N: EgglogValue, F, $($t: EgglogValue,)*> Selector<N, ($($t,)*)> for F
        where F: FnOnce($(&$t),*) -> N {
            fn select(self, node: &N) -> Result<Option<($($t,)*)>, TypedError> {
                let scope = fresh_scope(); let _ = scope;
                let variables = ($(variable::<$t>(scope, $i),)*); let _ = &variables;
                let pattern = self($(&variables.$i),*);
                let expressions: Vec<Expr> = vec![$(variables.$i.expression().clone()),*];
                let Some(args) = node.expression().select(pattern.expression(), &expressions)? else { return Ok(None); };
                let _ = &args;
                Ok(Some(($(ensure_sort::<$t>(args[$i].clone())?,)*)))
            }
        }
    };
}
selectors!();
selectors!(A:0);
selectors!(A:0,B:1);
selectors!(A:0,B:1,C:2);
selectors!(A:0,B:1,C:2,D:3);
