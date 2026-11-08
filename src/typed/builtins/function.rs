use crate::typed::{
    EgglogValue, SortRef, TypedError,
    expr::{Expr, ValueInput, fresh_scope, variable},
};
use std::{fmt::Debug, hash::Hash, marker::PhantomData};

/// The parameter tuple of a structural function value.
#[doc(hidden)]
pub trait FunctionArgs: Clone + Debug + Eq + Hash + Send + Sync + 'static {
    fn sorts() -> std::vec::Vec<SortRef>;
    fn expressions(&self) -> std::vec::Vec<Expr>;
    fn variables(scope: u64) -> Self;
}

/// A typed symbolic function, represented by the shared structural Func sort.
/// Computed callbacks author Lambda code with explicit evaluated captures.
/// `new` defers its complete symbolic body; `with_captures` retains supplied
/// values at function-value construction. Eq bodies are currently rejected.
/// Parameter and capture tuples support up to twelve values.
///
/// ```compile_fail,E0277
/// use egglog_experimental::typed::builtins::{Function, I64, F64};
/// let f = Function::<(I64,), I64>::new(|x| x.clone()).unwrap();
/// f.call(F64::from(1.0));
/// ```
/// ```compile_fail,E0308
/// use egglog_experimental::typed::builtins::{Function, I64, F64};
/// let _ = Function::<(I64,), I64>::new(|_| F64::from(1.0));
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Function<A: FunctionArgs, R: EgglogValue>(Expr, PhantomData<fn(A) -> R>);

impl<A: FunctionArgs, R: EgglogValue> ValueInput for Function<A, R> {
    type Owned = Self;
}
impl<A: FunctionArgs, R: EgglogValue> From<&Function<A, R>> for Function<A, R> {
    fn from(value: &Function<A, R>) -> Self {
        value.clone()
    }
}
impl<A: FunctionArgs, R: EgglogValue> EgglogValue for Function<A, R> {
    fn sort_ref() -> SortRef {
        SortRef::function(A::sorts(), R::sort_ref()).expect("typed function sort")
    }
    fn expression(&self) -> &Expr {
        &self.0
    }
    fn from_expression(value: Expr) -> Self {
        Self(value, PhantomData)
    }
}

macro_rules! function_parameters {
    (@[$($done:ident:$j:tt,)*];) => {};
    (@[$($done:ident:$j:tt,)*]; $next:ident:$i:tt $(,$tail:ident:$k:tt)*) => {
        function_parameters!($($done:$j,)* $next:$i);
        function_parameters!(@[$($done:$j,)* $next:$i,]; $($tail:$k),*);
    };
    ($($t:ident:$i:tt),*) => {
        impl<$($t: EgglogValue,)*> FunctionArgs for ($($t,)*) {
            fn sorts() -> std::vec::Vec<SortRef> { vec![$($t::sort_ref()),*] }
            fn expressions(&self) -> std::vec::Vec<Expr> { vec![$(self.$i.expression().clone()),*] }
            #[allow(clippy::unused_unit, reason = "The zero-parameter tuple is unit.")]
            fn variables(scope: u64) -> Self { let _ = scope; ($(variable::<$t>(scope, $i, None),)*) }
        }
        impl<R: EgglogValue, $($t: EgglogValue,)*> Function<($($t,)*), R> {
            /// Author a callback without evaluating its body or captured values.
            pub fn new(callback: impl FnOnce($(&$t),*) -> R) -> Result<Self, TypedError> {
                let scope = fresh_scope(); let _ = scope;
                let parameters = ($(variable::<$t>(scope, $i, None),)*); let _ = &parameters;
                let body = callback($(&parameters.$i),*);
                Ok(Self::from_expression(Expr::function(body.expression().clone(), vec![$(parameters.$i.expression().clone()),*], vec![], Self::sort_ref())?))
            }

            /// Evaluate the supplied captures when the function value is
            /// constructed. The callback receives typed capture placeholders;
            /// its remaining syntax is deferred until each application.
            pub fn with_captures<C: FunctionArgs>(captures: C, callback: impl FnOnce(C, $(&$t),*) -> R) -> Result<Self, TypedError> {
                let scope = fresh_scope(); let _ = scope;
                let parameters = ($(variable::<$t>(scope, $i, None),)*); let _ = &parameters;
                let captured_parameters = C::variables(fresh_scope());
                let mut formals = captured_parameters.expressions();
                formals.extend([$(parameters.$i.expression().clone()),*]);
                let body = callback(captured_parameters, $(&parameters.$i),*);
                Ok(Self::from_expression(Expr::function(body.expression().clone(), formals, captures.expressions(), Self::sort_ref())?))
            }
        }
    };
}
function_parameters!();
function_parameters!(@[]; A0:0,A1:1,A2:2,A3:3,A4:4,A5:5,A6:6,A7:7,
    A8:8,A9:9,A10:10,A11:11);

macro_rules! function_application {
    ($method:ident) => {
        function_application!(@one $method;);
        function_application!(@many $method; []; A0:0,A1:1,A2:2,A3:3,A4:4,A5:5,A6:6,A7:7,
            A8:8,A9:9,A10:10,A11:11);
    };
    (@many $method:ident; [$($done:ident:$j:tt,)*];) => {};
    (@many $method:ident; [$($done:ident:$j:tt,)*]; $next:ident:$i:tt $(,$tail:ident:$k:tt)*) => {
        function_application!(@one $method; $($done:$j,)* $next:$i);
        function_application!(@many $method; [$($done:$j,)* $next:$i,]; $($tail:$k),*);
    };
    (@one $method:ident; $($t:ident:$i:tt),*) => {
        impl<R: crate::typed::EgglogValue, $($t: crate::typed::EgglogValue,)*> self::Function<($($t,)*), R> {
            /// Apply this symbolic function to its typed arguments.
            #[allow(non_snake_case, clippy::too_many_arguments, reason = "The declaration determines parameter names and arity.")]
            pub fn $method(&self, $($t: impl Into<$t>),*) -> R {
                R::from_expression(crate::typed::expr::Expr::apply(
                    <Self as crate::typed::EgglogValue>::expression(self).clone(),
                    vec![$(<$t as crate::typed::EgglogValue>::expression(&$t.into()).clone()),*],
                ).expect("typed function application"))
            }
        }
    };
}
function_application!(call);
