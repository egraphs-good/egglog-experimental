use super::expr::Expr;
use std::{
    any::TypeId,
    hash::{Hash, Hasher},
    sync::Arc,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[doc(hidden)]
pub enum SortKind {
    Builtin,
    Equality,
    Container {
        family: &'static str,
        arguments: Vec<SortRef>,
    },
}

#[derive(Clone)]
/// Stable nominal sort identity, including applied builtin type arguments.
pub struct SortRef {
    pub(crate) name: Arc<str>,
    pub(crate) kind: SortKind,
}
impl SortRef {
    /// Returns the exact nominal name used by native declarations.
    pub fn name(&self) -> &str {
        &self.name
    }
    #[doc(hidden)]
    pub fn equality(name: impl Into<Arc<str>>) -> Self {
        Self {
            name: name.into(),
            kind: SortKind::Equality,
        }
    }
    pub(crate) fn builtin(name: &'static str) -> Self {
        Self {
            name: name.into(),
            kind: SortKind::Builtin,
        }
    }
    pub(crate) fn container(family: &'static str, arguments: Vec<Self>) -> Self {
        let name = format!(
            "{family}<{}>",
            arguments
                .iter()
                .map(Self::name)
                .collect::<Vec<_>>()
                .join(",")
        );
        Self {
            name: name.into(),
            kind: SortKind::Container { family, arguments },
        }
    }
    /// Whether this is a user-declared equality sort rather than a builtin or container.
    pub fn is_equality(&self) -> bool {
        matches!(self.kind, SortKind::Equality)
    }
    /// The structural family and ordered applied sorts of a container, even
    /// when its nominal name is an alias. Families are `Vec`, `Set`, `MultiSet`,
    /// `Map` (key, value), and `Pair` (first, second); scalars/classes return None.
    pub fn container_shape(&self) -> Option<(&'static str, &[SortRef])> {
        match &self.kind {
            SortKind::Container { family, arguments } => Some((family, arguments)),
            _ => None,
        }
    }
}
impl PartialEq for SortRef {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.kind == other.kind
    }
}
impl Eq for SortRef {}
impl Hash for SortRef {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.name.hash(h);
        self.kind.hash(h);
    }
}
impl std::fmt::Debug for SortRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("SortRef").field(&self.name).finish()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[doc(hidden)]
pub enum CallKind {
    Constructor,
    Relation,
    Function,
    Primitive { total: bool },
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub struct DefinitionSource {
    pub token: TypeId,
    pub resolve: fn() -> &'static CallableDef,
}

#[derive(Clone)]
/// Stable nominal callable identity, independent of source locations.
#[doc(hidden)]
pub struct CallableRef {
    pub(crate) name: Arc<str>,
    pub(crate) kind: CallKind,
    pub(crate) source: Option<DefinitionSource>,
    pub(crate) syntax: Option<CallSyntax>,
}
#[derive(Clone, Debug)]
#[doc(hidden)]
pub enum CallSyntax {
    Function(&'static str),
    Method(&'static str),
    Binary(&'static str),
    Unary(&'static str),
}
impl CallableRef {
    /// Returns the exact nominal name used by native declarations.
    pub fn name(&self) -> &str {
        &self.name
    }
    #[doc(hidden)]
    pub fn declared(
        name: &'static str,
        kind: CallKind,
        source: DefinitionSource,
        syntax: Option<CallSyntax>,
    ) -> Self {
        Self {
            name: name.into(),
            kind,
            source: Some(source),
            syntax,
        }
    }
    pub(crate) fn primitive(name: &'static str, total: bool) -> Self {
        Self {
            name: name.into(),
            kind: CallKind::Primitive { total },
            source: None,
            syntax: None,
        }
    }
}
impl PartialEq for CallableRef {
    fn eq(&self, rhs: &Self) -> bool {
        self.name == rhs.name
            && std::mem::discriminant(&self.kind) == std::mem::discriminant(&rhs.kind)
    }
}
impl Eq for CallableRef {}
impl Hash for CallableRef {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.name.hash(h);
        std::mem::discriminant(&self.kind).hash(h);
    }
}
impl std::fmt::Debug for CallableRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("CallableRef").field(&self.name).finish()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[doc(hidden)]
pub struct CallableDef {
    pub callable: CallableRef,
    pub inputs: Vec<SortRef>,
    pub output: SortRef,
    pub merge: Option<Expr>,
    pub cost: Option<u64>,
    pub unextractable: bool,
}
