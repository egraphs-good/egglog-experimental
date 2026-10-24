use super::{
    EgglogValue, TypedError,
    expr::{Expr, fresh_scope, variable},
    rule::ensure_sort,
};

#[doc(hidden)]
pub trait Selector<N, A> {
    fn select(self, node: &N) -> Result<Option<A>, TypedError>;
}

/// Inspect exact constructor or function call syntax using fresh arguments.
/// This does not evaluate a function row or decode extracted finite data.
/// Children retain their original owners. A different callable returns None;
/// same-name incompatible declarations or reordered selectors are errors.
/// Selector callbacks and generated named argument records support up to 64
/// inputs. Plain callable declarations do not impose an argument-count limit.
pub fn get_args<N: EgglogValue, A>(
    node: &N,
    selector: impl Selector<N, A>,
) -> Result<Option<A>, TypedError> {
    let record = &node.expression().0;
    let value = &record.owner.as_ref().unwrap().program().unwrap().nodes[record.index as usize];
    if super::SortRef(record.resolve(super::storage::Arena::Sort, value.sort_id)?) != N::sort_ref()
    {
        return Err(TypedError::Invalid(
            "selector root has another sort than its Rust wrapper".into(),
        ));
    }
    selector.select(node)
}

macro_rules! selectors {
    (@[$($done:ident:$j:tt,)*];) => {};
    (@[$($done:ident:$j:tt,)*]; $next:ident:$i:tt $(,$tail:ident:$k:tt)*) => {
        selectors!($($done:$j,)* $next:$i);
        selectors!(@[$($done:$j,)* $next:$i,]; $($tail:$k),*);
    };
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
selectors!(@[]; A0:0,A1:1,A2:2,A3:3,A4:4,A5:5,A6:6,A7:7,A8:8,A9:9,
    A10:10,A11:11,A12:12,A13:13,A14:14,A15:15,A16:16,A17:17,A18:18,A19:19,
    A20:20,A21:21,A22:22,A23:23,A24:24,A25:25,A26:26,A27:27,A28:28,A29:29,
    A30:30,A31:31,A32:32,A33:33,A34:34,A35:35,A36:36,A37:37,A38:38,A39:39,
    A40:40,A41:41,A42:42,A43:43,A44:44,A45:45,A46:46,A47:47,A48:48,A49:49,
    A50:50,A51:51,A52:52,A53:53,A54:54,A55:55,A56:56,A57:57,A58:58,A59:59,
    A60:60,A61:61,A62:62,A63:63);
