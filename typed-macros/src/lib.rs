//! The baseline's ordinary declaration parser, emitting generated-record views.
//! The initial subset deliberately rejects unsupported forms rather than
//! constructing a legacy semantic model or silently dropping their options.
use proc_macro::TokenStream;
use proc_macro2::TokenStream as Tokens;
use quote::{ToTokens, quote};
use syn::{
    Attribute, Fields, FnArg, Ident, ImplItem, ItemStruct, Meta, Pat, ReturnType, Signature, Token,
    Type, Visibility,
    ext::IdentExt,
    parse::{Parse, ParseStream, Parser},
    parse_macro_input,
    punctuated::Punctuated,
};

struct Stub {
    attrs: Vec<Attribute>,
    vis: Visibility,
    sig: Signature,
}
impl Parse for Stub {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let stub = Self {
            attrs: input.call(Attribute::parse_outer)?,
            vis: input.parse()?,
            sig: input.parse()?,
        };
        input.parse::<Token![;]>()?;
        Ok(stub)
    }
}

fn options(input: Tokens) -> syn::Result<Vec<Meta>> {
    let opts = Punctuated::<Meta, Token![,]>::parse_terminated.parse2(input)?;
    let mut seen = std::collections::HashSet::new();
    for opt in &opts {
        if !seen.insert(opt.path().to_token_stream().to_string()) {
            return Err(syn::Error::new_spanned(opt, "duplicate declaration option"));
        }
    }
    Ok(opts.into_iter().collect())
}

#[proc_macro_attribute]
pub fn sort(args: TokenStream, item: TokenStream) -> TokenStream {
    let item = parse_macro_input!(item as ItemStruct);
    let result = (|| {
        if !matches!(item.fields, Fields::Unit)
            || !item.generics.params.is_empty()
            || item.generics.where_clause.is_some()
        {
            return Err(syn::Error::new_spanned(
                &item,
                "sorts must be monomorphic unit structs",
            ));
        }
        let ident = &item.ident;
        let mut name = quote!(concat!(module_path!(), "::", stringify!(#ident)));
        for option in options(args.into())? {
            match option {
                Meta::NameValue(n) if n.path.is_ident("name") => {
                    let value = n.value;
                    name = quote!(#value);
                }
                other => {
                    return Err(syn::Error::new_spanned(
                        other,
                        "only name is supported on a sort",
                    ));
                }
            }
        }
        let ItemStruct {
            attrs, vis, ident, ..
        } = item;
        Ok(quote! {
            #(#attrs)* #[derive(Clone, PartialEq, Eq, Hash, Debug)]
            #vis struct #ident(::egglog_experimental::typed::__private::Expr);
            impl ::egglog_experimental::typed::__private::ValueInput for #ident { type Owned = Self; }
            impl From<&#ident> for #ident { fn from(value: &#ident) -> Self { value.clone() } }
            impl ::egglog_experimental::typed::EgglogValue for #ident {
                fn sort_ref() -> ::egglog_experimental::typed::SortRef {
                    static SORT: ::std::sync::OnceLock<::egglog_experimental::typed::SortRef> = ::std::sync::OnceLock::new();
                    SORT.get_or_init(|| ::egglog_experimental::typed::SortRef::equality(#name)).clone()
                }
                fn expression(&self) -> &::egglog_experimental::typed::__private::Expr { &self.0 }
                fn from_expression(expr: ::egglog_experimental::typed::__private::Expr) -> Self { Self(expr) }
            }
            impl ::egglog_experimental::typed::EqualitySort for #ident {}
        })
    })();
    result.unwrap_or_else(syn::Error::into_compile_error).into()
}

enum Member {
    Declaration(Box<Stub>),
    Other(Box<ImplItem>),
}
struct Declarations {
    attrs: Vec<Attribute>,
    owner: Type,
    trait_path: Option<syn::Path>,
    members: Vec<Member>,
}
impl Parse for Declarations {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        input.parse::<Token![impl]>()?;
        if input.peek(Token![<]) {
            return Err(input.error("declaration impls must be monomorphic"));
        }
        let first = input.parse::<Type>()?;
        let (owner, trait_path) = if input.peek(Token![for]) {
            let Type::Path(path) = first else {
                return Err(syn::Error::new_spanned(first, "expected a trait path"));
            };
            if path.qself.is_some() {
                return Err(syn::Error::new_spanned(path, "expected a trait path"));
            }
            input.parse::<Token![for]>()?;
            (input.parse()?, Some(path.path))
        } else {
            (first, None)
        };
        let body;
        syn::braced!(body in input);
        let mut members = vec![];
        while !body.is_empty() {
            let fork = body.fork();
            let _: Vec<Attribute> = fork.call(Attribute::parse_outer)?;
            let _: Visibility = fork.parse()?;
            if fork.parse::<Signature>().is_ok() && fork.peek(Token![;]) {
                members.push(Member::Declaration(Box::new(body.parse()?)));
            } else {
                members.push(Member::Other(Box::new(body.parse()?)));
            }
        }
        Ok(Self {
            attrs,
            owner,
            trait_path,
            members,
        })
    }
}

fn fresh_ident(base: &str, occupied: &mut std::collections::HashSet<String>) -> Ident {
    let mut spelling = base.to_owned();
    let mut suffix = 0;
    while !occupied.insert(spelling.clone()) {
        suffix += 1;
        spelling = format!("{base}_{suffix}");
    }
    Ident::new(&spelling, proc_macro2::Span::mixed_site())
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum CallableKind {
    Constructor,
    Function,
    Relation,
}

fn declaration_attrs(
    attrs: Vec<Attribute>,
) -> syn::Result<(Vec<Attribute>, Vec<Meta>, CallableKind)> {
    let mut opts = vec![];
    let mut retained = vec![];
    let mut seen = false;
    let mut kind = CallableKind::Constructor;
    for attr in attrs {
        if attr.path().is_ident("constructor")
            || attr.path().is_ident("function")
            || attr.path().is_ident("relation")
        {
            if seen {
                return Err(syn::Error::new_spanned(
                    attr,
                    "duplicate callable attribute",
                ));
            }
            seen = true;
            kind = if attr.path().is_ident("function") {
                CallableKind::Function
            } else if attr.path().is_ident("relation") {
                CallableKind::Relation
            } else {
                CallableKind::Constructor
            };
            opts = match &attr.meta {
                Meta::Path(_) => vec![],
                Meta::List(list) => options(list.tokens.clone())?,
                _ => return Err(syn::Error::new_spanned(attr, "invalid callable attribute")),
            };
        } else {
            retained.push(attr);
        }
    }
    Ok((retained, opts, kind))
}

fn resolve_type(ty: &Type, owner: Option<&Type>) -> syn::Result<Type> {
    if matches!(ty, Type::Path(path) if path.qself.is_none() && path.path.is_ident("Self")) {
        return owner
            .cloned()
            .ok_or_else(|| syn::Error::new_spanned(ty, "Self needs an inherent impl"));
    }
    if matches!(ty, Type::Reference(_)) {
        return Err(syn::Error::new_spanned(
            ty,
            "declare owned symbolic argument/output sorts; calls accept borrows",
        ));
    }
    Ok(ty.clone())
}

fn conversion_source_type(ty: &Type, owner: Option<&Type>) -> syn::Result<Type> {
    if let Type::Reference(reference) = ty {
        let mut reference = reference.clone();
        reference.elem = Box::new(conversion_source_type(&reference.elem, owner)?);
        Ok(Type::Reference(reference))
    } else {
        resolve_type(ty, owner)
    }
}

fn callable(
    mut stub: Stub,
    opts: Vec<Meta>,
    owner: Option<&Type>,
    kind: CallableKind,
    shared_definition: Option<(&Ident, &Ident)>,
) -> syn::Result<(Tokens, Tokens)> {
    let function = kind == CallableKind::Function;
    if !stub.sig.generics.params.is_empty()
        || stub.sig.generics.where_clause.is_some()
        || stub.sig.asyncness.is_some()
        || stub.sig.constness.is_some()
        || stub.sig.unsafety.is_some()
        || stub.sig.abi.is_some()
        || stub.sig.variadic.is_some()
    {
        return Err(syn::Error::new_spanned(
            &stub.sig,
            "callables require monomorphic safe ordinary signatures",
        ));
    }
    let name = stub.sig.ident.clone();
    let mut nominal = if let Some(owner) = owner {
        quote!(concat!(
            module_path!(),
            "::",
            stringify!(#owner),
            "::",
            stringify!(#name)
        ))
    } else {
        quote!(concat!(module_path!(), "::", stringify!(#name)))
    };
    let mut from: Option<Vec<Type>> = None;
    let mut try_from = false;
    let mut args_record = None;
    let mut no_merge = false;
    let mut merge = None;
    for opt in opts {
        match opt {
            Meta::NameValue(n) if n.path.is_ident("name") => {
                let value = n.value;
                nominal = quote!(#value);
            }
            Meta::NameValue(n) if n.path.is_ident("args") => {
                let syn::Expr::Path(p) = n.value else {
                    return Err(syn::Error::new_spanned(n, "args needs a record name"));
                };
                args_record = Some(p.path.get_ident().cloned().ok_or_else(|| {
                    syn::Error::new_spanned(p, "args needs an unqualified record name")
                })?);
            }
            Meta::Path(p) if p.is_ident("no_merge") && function => no_merge = true,
            Meta::NameValue(n) if n.path.is_ident("merge") && function => {
                let syn::Expr::Closure(closure) = n.value else {
                    return Err(syn::Error::new_spanned(
                        n,
                        "merge needs a two-argument closure",
                    ));
                };
                if closure.inputs.len() != 2 || closure.asyncness.is_some() {
                    return Err(syn::Error::new_spanned(
                        closure,
                        "merge needs an ordinary two-argument closure",
                    ));
                }
                merge = Some(closure);
            }
            Meta::Path(p) if p.is_ident("from") && kind == CallableKind::Constructor => {
                from = Some(Vec::new())
            }
            Meta::List(list) if list.path.is_ident("from") && kind == CallableKind::Constructor => {
                from = Some(
                    list.parse_args_with(Punctuated::<Type, Token![,]>::parse_terminated)?
                        .into_iter()
                        .collect(),
                );
            }
            Meta::Path(p) if p.is_ident("try_from") && kind == CallableKind::Constructor => {
                try_from = true
            }
            other => {
                return Err(syn::Error::new_spanned(
                    other,
                    "unsupported callable option (from/try_from are constructor-only)",
                ));
            }
        }
    }
    if function && no_merge == merge.is_some() {
        return Err(syn::Error::new_spanned(
            &stub.sig,
            "functions require exactly one of no_merge or merge",
        ));
    }
    let mut names = vec![];
    let mut types = vec![];
    for input in &mut stub.sig.inputs {
        if let FnArg::Receiver(receiver) = input {
            let Some(owner) = owner else {
                return Err(syn::Error::new_spanned(
                    receiver,
                    "receivers require an inherent declaration",
                ));
            };
            if shared_definition.is_some() {
                if receiver.reference.is_some()
                    || receiver.mutability.is_some()
                    || receiver.colon_token.is_some()
                {
                    return Err(syn::Error::new_spanned(
                        receiver,
                        "binary operator declarations require by-value self",
                    ));
                }
            } else if receiver.reference.is_none()
                || receiver.mutability.is_some()
                || receiver.colon_token.is_some()
            {
                return Err(syn::Error::new_spanned(
                    receiver,
                    match kind {
                        CallableKind::Constructor => {
                            "constructor declarations support only &self receivers"
                        }
                        CallableKind::Function => {
                            "function declarations support only &self receivers"
                        }
                        CallableKind::Relation => {
                            "relation declarations support only &self receivers"
                        }
                    },
                ));
            }
            if args_record.is_some() {
                return Err(syn::Error::new_spanned(
                    receiver,
                    "named argument records require explicit owned arguments",
                ));
            }
            if from.is_some() || try_from {
                return Err(syn::Error::new_spanned(
                    receiver,
                    "receiver declarations do not support from/try_from",
                ));
            }
            names.push(Ident::new("self", receiver.self_token.span));
            types.push(owner.clone());
            continue;
        }
        let FnArg::Typed(arg) = input else {
            unreachable!()
        };
        let Pat::Ident(pat) = arg.pat.as_ref() else {
            return Err(syn::Error::new_spanned(
                &arg.pat,
                "callable arguments must be plain identifiers",
            ));
        };
        if pat.by_ref.is_some() || pat.subpat.is_some() {
            return Err(syn::Error::new_spanned(
                pat,
                "callable arguments must be plain identifiers",
            ));
        }
        let ty = resolve_type(&arg.ty, owner)?;
        names.push(pat.ident.clone());
        types.push(ty.clone());
        arg.ty = Box::new(syn::parse_quote!(impl Into<#ty>));
    }
    let output = if kind == CallableKind::Relation {
        match &stub.sig.output {
            ReturnType::Default => (),
            ReturnType::Type(_, ty) if matches!(ty.as_ref(), Type::Tuple(tuple) if tuple.elems.is_empty()) =>
                {}
            other => {
                return Err(syn::Error::new_spanned(
                    other,
                    "relations require an omitted or () output",
                ));
            }
        }
        syn::parse_quote!(::egglog_experimental::typed::builtins::Unit)
    } else {
        let ReturnType::Type(_, output) = &stub.sig.output else {
            return Err(syn::Error::new_spanned(
                &stub.sig,
                "a callable output sort is required",
            ));
        };
        resolve_type(output, owner)?
    };
    stub.sig.output = syn::parse_quote!(-> #output);
    let target = if let Some(owner) = owner {
        quote!(<#owner>::#name)
    } else {
        quote!(#name)
    };
    let hidden: Vec<_> = (0..names.len())
        .map(|i| {
            Ident::new(
                &format!("__egglog_argument_{i}"),
                proc_macro2::Span::mixed_site(),
            )
        })
        .collect();
    // Mixed-site locals cannot capture authored identifiers. Item names (the
    // static) also get a spelling disjoint from the authored value bindings.
    let mut occupied: std::collections::HashSet<_> = names
        .iter()
        .map(|name| name.unraw().to_string())
        .chain(std::iter::once(name.unraw().to_string()))
        .collect();
    let definition_static = shared_definition
        .map(|(cache, _)| cache.clone())
        .unwrap_or_else(|| fresh_ident("__EGGLOG_DEFINITION", &mut occupied));
    let definition = fresh_ident("__egglog_definition", &mut occupied);
    let value = fresh_ident("__egglog_value", &mut occupied);
    let field = fresh_ident("__egglog_field", &mut occupied);
    let scope = fresh_ident("__egglog_scope", &mut occupied);
    let old = fresh_ident("__egglog_old", &mut occupied);
    let new = fresh_ident("__egglog_new", &mut occupied);
    let has_merge = merge.is_some();
    let merge_argument = if function {
        if let Some(merge) = merge {
            quote! {
                Some(|#old, #new| {
                    let #value: #output = (#merge)(
                        <#output as ::egglog_experimental::typed::EgglogValue>::from_expression(#old),
                        <#output as ::egglog_experimental::typed::EgglogValue>::from_expression(#new),
                    );
                    ::egglog_experimental::typed::EgglogValue::expression(&#value).clone()
                }),
            }
        } else {
            quote! {
                None::<fn(
                    ::egglog_experimental::typed::__private::Expr,
                    ::egglog_experimental::typed::__private::Expr,
                ) -> ::egglog_experimental::typed::__private::Expr>,
            }
        }
    } else {
        Tokens::new()
    };
    let mut extra = Tokens::new();
    let cfg: Vec<_> = stub
        .attrs
        .iter()
        .filter(|a| a.path().is_ident("cfg"))
        .collect();
    if from.is_some() || try_from {
        if types.len() != 1
            || types[0].to_token_stream().to_string() == output.to_token_stream().to_string()
        {
            return Err(syn::Error::new_spanned(
                &stub.sig,
                "from/try_from require a unary constructor with a different input sort",
            ));
        }
        let input = &types[0];
        if let Some(additional) = from {
            let mut sources = vec![input.clone(), syn::parse_quote!(&#input)];
            sources.extend(additional);
            let mut seen = std::collections::HashSet::new();
            for source in sources {
                let source = conversion_source_type(&source, owner)?;
                let spelling = source.to_token_stream().to_string();
                if !seen.insert(spelling.clone()) {
                    return Err(syn::Error::new_spanned(
                        source,
                        "duplicate from source type",
                    ));
                }
                if spelling == output.to_token_stream().to_string()
                    || spelling == quote!(&#output).to_string()
                {
                    return Err(syn::Error::new_spanned(
                        source,
                        "from cannot replace an identity or borrowed sort conversion",
                    ));
                }
                extra.extend(quote! {
                    #(#cfg)* impl From<#source> for #output {
                        fn from(#value: #source) -> Self { #target(#value) }
                    }
                });
            }
        }
        if try_from {
            extra.extend(quote! {
                #(#cfg)* impl TryFrom<&#output> for #input {
                    type Error = ::egglog_experimental::typed::TypedError;
                    fn try_from(#value: &#output) -> Result<Self, Self::Error> {
                        let Some((#field,)) = ::egglog_experimental::typed::get_args(#value, |#field: &#input| #target(#field))? else {
                            return Err(::egglog_experimental::typed::TypedError::Decode(concat!("expected constructor ", stringify!(#target)).into()));
                        };
                        Ok(#field)
                    }
                }
                #(#cfg)* impl TryFrom<#output> for #input {
                    type Error = ::egglog_experimental::typed::TypedError;
                    fn try_from(#value: #output) -> Result<Self, Self::Error> { <Self as TryFrom<&#output>>::try_from(&#value) }
                }
            });
        }
    }
    if let Some(record) = args_record {
        let vis = &stub.vis;
        let indices = 0..types.len();
        extra.extend(quote! {
            #(#cfg)* #[derive(Clone, Debug)] #vis struct #record { #(pub #names: #types,)* }
            #(#cfg)* impl #record {
                pub fn fresh() -> Self {
                    let #scope = ::egglog_experimental::typed::__private::fresh_scope(); let _ = #scope;
                    Self { #(#names: ::egglog_experimental::typed::__private::variable::<#types>(#scope, #indices),)* }
                }
                pub fn get_args(#value: &#output) -> Result<Option<Self>, ::egglog_experimental::typed::TypedError> {
                    let Some((#(#hidden,)*)) = ::egglog_experimental::typed::get_args(#value, |#(#hidden: &#types),*| #target(#(#hidden),*))? else { return Ok(None); };
                    Ok(Some(Self { #(#names: #hidden,)* }))
                }
            }
            #(#cfg)* impl From<#record> for #output { fn from(#value: #record) -> Self { #target(#(#value.#names),*) } }
        });
    }
    let Stub { attrs, vis, sig } = stub;
    let factory = Ident::new(
        match kind {
            CallableKind::Constructor => "constructor",
            CallableKind::Function => "function",
            CallableKind::Relation => "relation",
        },
        proc_macro2::Span::call_site(),
    );
    let result_argument = if kind == CallableKind::Relation {
        Tokens::new()
    } else {
        quote!(<#output as ::egglog_experimental::typed::EgglogValue>::sort_ref(),)
    };
    let construction = quote! {
        ::egglog_experimental::typed::__private::Callable::#factory(
            #nominal, vec![#(<#types as ::egglog_experimental::typed::EgglogValue>::sort_ref()),*],
            #result_argument
            #merge_argument
        )
    };
    let initialization = if has_merge {
        let owner = fresh_ident("__egglog_merge_owner", &mut occupied);
        let reset = fresh_ident("__EgglogMergeInitialization", &mut occupied);
        let guard = fresh_ident("__egglog_merge_guard", &mut occupied);
        quote! {
            static #definition_static: (
                ::std::sync::OnceLock<::egglog_experimental::typed::__private::Callable>,
                ::std::sync::Mutex<::std::option::Option<::std::thread::ThreadId>>,
            ) = (::std::sync::OnceLock::new(), ::std::sync::Mutex::new(::std::option::Option::None));
            if #definition_static.0.get().is_none() && {
                let #owner = #definition_static.1.lock().unwrap();
                #owner.as_ref() == ::std::option::Option::Some(&::std::thread::current().id())
            } {
                ::std::panic!("recursive function merge initialization");
            }
            let #definition = #definition_static.0.get_or_init(|| {
                *#definition_static.1.lock().unwrap() = ::std::option::Option::Some(::std::thread::current().id());
                let #guard = {
                    struct #reset(&'static ::std::sync::Mutex<::std::option::Option<::std::thread::ThreadId>>);
                    impl ::std::ops::Drop for #reset {
                        fn drop(&mut self) {
                            *self.0.lock().unwrap() = ::std::option::Option::None;
                        }
                    }
                    #reset(&#definition_static.1)
                };
                #construction
            });
        }
    } else if let Some((_, initializer)) = shared_definition {
        extra.extend(quote! {
            fn #initializer() -> ::egglog_experimental::typed::__private::Callable {
                #construction
            }
        });
        quote! {
            let #definition = #definition_static.get_or_init(#initializer);
        }
    } else {
        quote! {
            static #definition_static: ::std::sync::OnceLock<::egglog_experimental::typed::__private::Callable> = ::std::sync::OnceLock::new();
            let #definition = #definition_static.get_or_init(|| #construction);
        }
    };
    let method = quote! {
        #(#attrs)* #[allow(non_snake_case)] #vis #sig {
            #initialization
            let (#(#hidden,)*): (#(#types,)*) = (#(::std::convert::Into::into(#names),)*);
            <#output as ::egglog_experimental::typed::EgglogValue>::from_expression(
                ::egglog_experimental::typed::__private::Expr::call(#definition, vec![#(::egglog_experimental::typed::EgglogValue::expression(&#hidden).clone()),*]),
            )
        }
    };
    Ok((method, extra))
}

#[proc_macro_attribute]
/// Declare a canonical constructor. On unary constructors, `from` derives
/// conversions from the input sort and its borrow; `from(T, U)` additionally
/// derives concrete conversions from those Rust types through the input's
/// existing `Into` implementations. It does not evaluate the constructed Call
/// or search for indirect conversions. `try_from` retains exact field decoding.
pub fn constructor(args: TokenStream, item: TokenStream) -> TokenStream {
    let stub = parse_macro_input!(item as Stub);
    options(args.into())
        .and_then(|opts| callable(stub, opts, None, CallableKind::Constructor, None))
        .map(|(method, extra)| quote!(#method #extra))
        .unwrap_or_else(syn::Error::into_compile_error)
        .into()
}

#[proc_macro_attribute]
pub fn function(args: TokenStream, item: TokenStream) -> TokenStream {
    let stub = parse_macro_input!(item as Stub);
    options(args.into())
        .and_then(|opts| callable(stub, opts, None, CallableKind::Function, None))
        .map(|(method, extra)| quote!(#method #extra))
        .unwrap_or_else(syn::Error::into_compile_error)
        .into()
}

#[proc_macro_attribute]
pub fn relation(args: TokenStream, item: TokenStream) -> TokenStream {
    let stub = parse_macro_input!(item as Stub);
    options(args.into())
        .and_then(|opts| callable(stub, opts, None, CallableKind::Relation, None))
        .map(|(method, extra)| quote!(#method #extra))
        .unwrap_or_else(syn::Error::into_compile_error)
        .into()
}

// Project only conditional removal onto the whole generated declaration. Other
// cfg_attr effects stay on their authored method/impl, not on the cache item.
fn declaration_cfg(meta: &Meta) -> syn::Result<Option<Meta>> {
    if meta.path().is_ident("cfg") {
        return Ok(Some(meta.clone()));
    }
    let Meta::List(list) = meta else {
        return Ok(None);
    };
    if !list.path.is_ident("cfg_attr") {
        return Ok(None);
    }
    let args = list.parse_args_with(Punctuated::<Meta, Token![,]>::parse_terminated)?;
    let Some(predicate) = args.first() else {
        return Err(syn::Error::new_spanned(list, "cfg_attr needs a predicate"));
    };
    let projected = args
        .iter()
        .skip(1)
        .map(declaration_cfg)
        .collect::<syn::Result<Vec<_>>>()?
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    Ok((!projected.is_empty()).then(|| syn::parse_quote!(cfg_attr(#predicate, #(#projected),*))))
}

fn operator_sort(ty: &Type, owner: &Type, input: bool) -> syn::Result<Type> {
    let ty = if matches!(ty, Type::Path(path) if path.qself.is_none() && path.path.is_ident("Self"))
    {
        owner.clone()
    } else {
        ty.clone()
    };
    let ty = if let Type::Reference(reference) = ty {
        if !input || reference.mutability.is_some() {
            return Err(syn::Error::new_spanned(
                reference,
                "operator sorts must be owned, with immutable borrows allowed only for inputs",
            ));
        }
        *reference.elem
    } else {
        ty
    };
    let ty = resolve_type(&ty, Some(owner))?;
    // Reject a second borrow, including &Self when the authored Self is &Sort.
    resolve_type(&ty, None)
}

fn operator_declarations(item: Declarations) -> syn::Result<Tokens> {
    let Declarations {
        attrs,
        owner,
        trait_path,
        members,
    } = item;
    let trait_path = trait_path.unwrap();
    if !members
        .iter()
        .any(|member| matches!(member, Member::Declaration(_)))
    {
        let mut ordinary = Tokens::new();
        for member in members {
            let Member::Other(item) = member else {
                unreachable!()
            };
            if let ImplItem::Fn(method) = item.as_ref()
                && method.attrs.iter().any(|attr| {
                    attr.path().is_ident("constructor")
                        || attr.path().is_ident("function")
                        || attr.path().is_ident("relation")
                })
            {
                return Err(syn::Error::new_spanned(
                    &method.sig,
                    "symbolic declarations must be bodyless",
                ));
            }
            ordinary.extend(quote!(#item));
        }
        return Ok(quote!(#(#attrs)* impl #trait_path for #owner { #ordinary }));
    }
    let segments = trait_path.segments.iter().collect::<Vec<_>>();
    if segments.len() != 3
        || !(segments[0].ident == "std" || segments[0].ident == "core")
        || segments[1].ident != "ops"
    {
        return Err(syn::Error::new_spanned(
            &trait_path,
            "only qualified std::ops/core::ops binary constructor traits are supported",
        ));
    }
    let method_name = match segments[2].ident.to_string().as_str() {
        "Add" => "add",
        "Sub" => "sub",
        "Mul" => "mul",
        "Div" => "div",
        "Rem" => "rem",
        _ => {
            return Err(syn::Error::new_spanned(
                &trait_path,
                "only Add/Sub/Mul/Div/Rem constructor traits are supported",
            ));
        }
    };
    let syn::PathArguments::AngleBracketed(args) = &segments[2].arguments else {
        return Err(syn::Error::new_spanned(
            &trait_path,
            "binary constructor traits require one explicit RHS type",
        ));
    };
    if args.args.len() != 1 {
        return Err(syn::Error::new_spanned(
            args,
            "binary constructor traits require one explicit RHS type",
        ));
    }
    let Some(syn::GenericArgument::Type(trait_rhs)) = args.args.first() else {
        return Err(syn::Error::new_spanned(
            args,
            "binary constructor traits require one explicit RHS type",
        ));
    };
    let trait_rhs = trait_rhs.clone();
    let mut declaration = None;
    let mut associated_output = None;
    for member in members {
        match member {
            Member::Declaration(stub) if declaration.is_none() => declaration = Some(*stub),
            Member::Other(item)
                if matches!(item.as_ref(), ImplItem::Type(output) if output.ident == "Output")
                    && associated_output.is_none() =>
            {
                let ImplItem::Type(output) = *item else {
                    unreachable!()
                };
                associated_output = Some(output);
            }
            _ => {
                return Err(syn::Error::new_spanned(
                    &trait_path,
                    "binary declarations need one bodyless method and type Output only",
                ));
            }
        }
    }
    let mut stub = declaration.unwrap();
    let output_item = associated_output.ok_or_else(|| {
        syn::Error::new_spanned(&trait_path, "binary declarations require type Output")
    })?;
    if !output_item.generics.params.is_empty() || output_item.generics.where_clause.is_some() {
        return Err(syn::Error::new_spanned(
            output_item,
            "operator output must be monomorphic",
        ));
    }
    if stub.sig.inputs.len() != 2 || !matches!(stub.sig.inputs.first(), Some(FnArg::Receiver(_))) {
        return Err(syn::Error::new_spanned(
            &stub.sig,
            "binary declarations require self and one RHS argument",
        ));
    }
    let FnArg::Typed(rhs) = &stub.sig.inputs[1] else {
        return Err(syn::Error::new_spanned(
            &stub.sig,
            "operator RHS must be a named argument",
        ));
    };
    let rhs_sort = operator_sort(&rhs.ty, &owner, true)?;
    let lhs_sort = operator_sort(&owner, &owner, true)?;
    let output_sort = operator_sort(&output_item.ty, &owner, false)?;
    if matches!(stub.sig.output, ReturnType::Default) {
        return Err(syn::Error::new_spanned(
            &stub.sig,
            "an operator output sort is required",
        ));
    }
    let (retained, mut opts, kind) = declaration_attrs(stub.attrs)?;
    stub.attrs = retained;
    if kind != CallableKind::Constructor || opts.iter().any(|opt| !opt.path().is_ident("name")) {
        return Err(syn::Error::new_spanned(
            &stub.sig,
            "binary constructor declarations support only name",
        ));
    }
    if !opts.iter().any(|opt| opt.path().is_ident("name")) {
        let method = &stub.sig.ident;
        opts.push(syn::parse_quote!(
            name = concat!(
                module_path!(),
                "::<",
                stringify!(#lhs_sort),
                " as ",
                stringify!(#trait_path),
                ">::",
                stringify!(#method)
            )
        ));
    }
    let mut occupied = std::collections::HashSet::new();
    let sig = &stub.sig;
    let mut pending = vec![quote!(#owner #trait_path #output_item #sig #(#opts)*)];
    while let Some(tokens) = pending.pop() {
        for token in tokens {
            match token {
                proc_macro2::TokenTree::Ident(ident) => {
                    occupied.insert(ident.unraw().to_string());
                }
                proc_macro2::TokenTree::Group(group) => pending.push(group.stream()),
                _ => {}
            }
        }
    }
    let cache = fresh_ident("__EGGLOG_OPERATOR_DEFINITION", &mut occupied);
    let initializer = fresh_ident("__egglog_operator_initializer", &mut occupied);
    let witness = fresh_ident("__EgglogSignature", &mut occupied);
    let rhs_parameter = fresh_ident("__EgglogRhs", &mut occupied);
    let checked_method = Ident::new(method_name, stub.sig.ident.span());
    let original_sig = stub.sig.clone();
    let original_attrs = stub.attrs.clone();
    let original_vis = stub.vis.clone();
    let cfg = attrs
        .iter()
        .chain(&stub.attrs)
        .map(|attr| declaration_cfg(&attr.meta))
        .collect::<syn::Result<Vec<_>>>()?
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();

    let FnArg::Typed(rhs) = &mut stub.sig.inputs[1] else {
        unreachable!()
    };
    rhs.ty = Box::new(rhs_sort.clone());
    stub.sig.output = syn::parse_quote!(-> #output_sort);
    let (method, initialization) = callable(
        stub,
        opts,
        Some(&lhs_sort),
        CallableKind::Constructor,
        Some((&cache, &initializer)),
    )?;
    let mut method = syn::parse2::<syn::ImplItemFn>(method)?;
    let FnArg::Typed(rhs) = &mut method.sig.inputs[1] else {
        unreachable!()
    };
    rhs.ty = Box::new(syn::parse_quote!(#rhs_parameter));
    let mut generated_trait = trait_path.clone();
    generated_trait.segments.last_mut().unwrap().arguments =
        syn::PathArguments::AngleBracketed(syn::parse_quote!(<#rhs_parameter>));
    let mut generated_output = output_item.clone();
    generated_output.ty = output_sort;
    let implementations = [quote!(#lhs_sort), quote!(&#lhs_sort)].map(|lhs| quote! {
        #(#attrs)* impl<#rhs_parameter: ::std::convert::Into<#rhs_sort>> #generated_trait for #lhs {
            #generated_output
            #method
        }
    });
    Ok(quote! {
        #(#[#cfg])*
        const _: () = {
            // Keep the authored signature checked before replacing its RHS by
            // a conversion parameter; no runtime wrapper or second IR exists.
            #[allow(dead_code)]
            trait #witness<#rhs_parameter> {
                type Output;
                fn #checked_method(self, rhs: #rhs_parameter) -> Self::Output;
            }
            #[allow(unused_variables)]
            impl #witness<#trait_rhs> for #owner {
                #output_item
                #(#original_attrs)* #original_vis #original_sig { ::core::unreachable!() }
            }
            #initialization
            static #cache: ::std::sync::OnceLock<::egglog_experimental::typed::__private::Callable> = ::std::sync::OnceLock::new();
            #(#implementations)*
        };
    })
}

fn ruleset_item(mut item: syn::ItemFn, opts: Vec<Meta>) -> syn::Result<Tokens> {
    let sig = &item.sig;
    if !sig.generics.params.is_empty()
        || sig.generics.where_clause.is_some()
        || sig.asyncness.is_some()
        || sig.constness.is_some()
        || sig.unsafety.is_some()
        || sig.abi.is_some()
        || sig.variadic.is_some()
    {
        return Err(syn::Error::new_spanned(
            sig,
            "rulesets require monomorphic safe ordinary signatures",
        ));
    }
    if sig.inputs.len() > 35 {
        return Err(syn::Error::new_spanned(
            &sig.inputs,
            "rulesets support at most 35 borrowed arguments",
        ));
    }
    for input in &sig.inputs {
        let FnArg::Typed(arg) = input else {
            return Err(syn::Error::new_spanned(
                input,
                "ruleset arguments must be plain identifiers",
            ));
        };
        let Pat::Ident(pat) = arg.pat.as_ref() else {
            return Err(syn::Error::new_spanned(
                &arg.pat,
                "ruleset arguments must be plain identifiers",
            ));
        };
        if pat.by_ref.is_some() || pat.subpat.is_some() {
            return Err(syn::Error::new_spanned(
                pat,
                "ruleset arguments must be plain identifiers",
            ));
        }
        let Type::Reference(reference) = arg.ty.as_ref() else {
            return Err(syn::Error::new_spanned(
                &arg.ty,
                "ruleset arguments must be immutable borrows",
            ));
        };
        if reference.mutability.is_some() {
            return Err(syn::Error::new_spanned(
                reference,
                "ruleset arguments must be immutable borrows",
            ));
        }
        if matches!(reference.elem.as_ref(), Type::ImplTrait(_)) {
            return Err(syn::Error::new_spanned(
                reference,
                "ruleset callbacks do not support impl Trait inputs",
            ));
        }
    }
    if matches!(&sig.output, ReturnType::Type(_, ty) if matches!(ty.as_ref(), Type::ImplTrait(_))) {
        return Err(syn::Error::new_spanned(
            &sig.output,
            "ruleset callbacks do not support impl Trait outputs",
        ));
    }
    let ident = &sig.ident;
    let mut name = quote!(concat!(module_path!(), "::", stringify!(#ident)));
    for option in opts {
        match option {
            Meta::NameValue(n) if n.path.is_ident("name") => {
                let value = n.value;
                name = quote!(#value);
            }
            other => {
                return Err(syn::Error::new_spanned(
                    other,
                    "only name is supported on a ruleset",
                ));
            }
        }
    }
    for attr in &mut item.attrs {
        attr.style = syn::AttrStyle::Outer;
    }
    let syn::ItemFn {
        attrs,
        vis,
        sig,
        block,
    } = item;
    let ident = sig.ident;
    let inputs = sig.inputs;
    let output = sig.output;
    Ok(quote! {
        #(#attrs)*
        #[allow(non_upper_case_globals)]
        #vis static #ident: ::std::sync::LazyLock<::egglog_experimental::typed::Ruleset> =
            ::std::sync::LazyLock::new(|| ::egglog_experimental::typed::__private::named_ruleset(
                || ::std::option::Option::Some((#name).into()), |#inputs| #output #block,
            ));
    })
}

#[proc_macro_attribute]
pub fn ruleset(args: TokenStream, item: TokenStream) -> TokenStream {
    let item = parse_macro_input!(item as syn::ItemFn);
    options(args.into())
        .and_then(|opts| ruleset_item(item, opts))
        .unwrap_or_else(syn::Error::into_compile_error)
        .into()
}

#[proc_macro_attribute]
pub fn declarations(args: TokenStream, item: TokenStream) -> TokenStream {
    if !args.is_empty() {
        return syn::Error::new(
            proc_macro2::Span::call_site(),
            "declarations takes no arguments",
        )
        .into_compile_error()
        .into();
    }
    let item = parse_macro_input!(item as Declarations);
    let result = (|| {
        if item.trait_path.is_some() {
            return operator_declarations(item);
        }
        let mut members = Tokens::new();
        let mut extra = Tokens::new();
        for member in item.members {
            match member {
                Member::Other(item) => members.extend(quote!(#item)),
                Member::Declaration(stub) => {
                    let mut stub = *stub;
                    let (retained, opts, kind) = declaration_attrs(stub.attrs)?;
                    stub.attrs = retained;
                    let (method, generated) = callable(stub, opts, Some(&item.owner), kind, None)?;
                    members.extend(method);
                    extra.extend(generated);
                }
            }
        }
        let Declarations { attrs, owner, .. } = item;
        Ok(quote!(#(#attrs)* impl #owner { #members } #extra))
    })();
    result.unwrap_or_else(syn::Error::into_compile_error).into()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn relation_free_and_borrowed_receiver_forms_have_one_input_only_cache() {
        for (source, owner) in [
            ("pub fn predicate(value: IList, index: I64);", None),
            ("pub fn predicate(value: IList, index: I64) -> ();", None),
            (
                "pub fn predicate(&self, index: I64);",
                Some(syn::parse_quote!(IList)),
            ),
            (
                "pub fn predicate(&self, index: I64) -> ();",
                Some(syn::parse_quote!(IList)),
            ),
        ] {
            let (method, extra) = callable(
                syn::parse_str(source).unwrap(),
                options(quote!(name = counted_relation_name())).unwrap(),
                owner.as_ref(),
                CallableKind::Relation,
                None,
            )
            .unwrap();
            assert!(extra.is_empty());
            let parsed = syn::parse2::<syn::ItemFn>(method.clone()).unwrap();
            assert!(matches!(parsed.vis, Visibility::Public(_)));
            assert_eq!(
                parsed.sig.output.to_token_stream().to_string(),
                quote!(-> ::egglog_experimental::typed::builtins::Unit).to_string()
            );
            assert_eq!(
                matches!(&parsed.sig.inputs[0], FnArg::Receiver(_)),
                owner.is_some()
            );
            let tokens = method.to_string();
            assert_eq!(tokens.matches("OnceLock :: new").count(), 1);
            assert_eq!(tokens.matches("get_or_init").count(), 1);
            assert_eq!(tokens.matches("counted_relation_name").count(), 1);
            assert_eq!(tokens.matches("Into :: into").count(), 2);
            assert!(
                tokens.contains(
                    &quote!(::egglog_experimental::typed::__private::Callable::relation(
                        counted_relation_name(),
                        vec![
                            <IList as ::egglog_experimental::typed::EgglogValue>::sort_ref(),
                            <I64 as ::egglog_experimental::typed::EgglogValue>::sort_ref()
                        ],
                    ))
                    .to_string()
                )
            );
            assert!(!tokens.contains(
                &quote!(<::egglog_experimental::typed::builtins::Unit as ::egglog_experimental::typed::EgglogValue>::sort_ref()).to_string()
            ));
            assert_eq!(tokens.matches("Expr :: call").count(), 1);
        }
    }

    #[test]
    fn relation_attributes_keep_identity_and_reject_mixed_callable_attributes() {
        for owner in [None, Some(syn::parse_quote!(IList))] {
            let mut stub = syn::parse_str::<Stub>(
                "#[cfg(feature = \"authored\")] #[relation] pub fn predicate(value: IList);",
            )
            .unwrap();
            let (retained, opts, kind) = declaration_attrs(stub.attrs).unwrap();
            assert_eq!(kind, CallableKind::Relation);
            assert!(opts.is_empty());
            assert_eq!(retained.len(), 1);
            assert!(retained[0].path().is_ident("cfg"));
            stub.attrs = retained;
            let (method, extra) = callable(stub, opts, owner.as_ref(), kind, None).unwrap();
            assert!(extra.is_empty());
            let parsed = syn::parse2::<syn::ItemFn>(method.clone()).unwrap();
            assert!(parsed.attrs[0].path().is_ident("cfg"));
            let nominal = if owner.is_some() {
                quote!(concat!(
                    module_path!(),
                    "::",
                    stringify!(IList),
                    "::",
                    stringify!(predicate)
                ))
            } else {
                quote!(concat!(module_path!(), "::", stringify!(predicate)))
            };
            assert!(method.to_string().contains(&nominal.to_string()));
        }
        for attrs in [
            quote!(#[constructor] #[relation]),
            quote!(#[function(no_merge)] #[relation]),
            quote!(#[relation] #[relation]),
        ] {
            let stub = syn::parse2::<Stub>(quote!(#attrs fn predicate(value: IList);)).unwrap();
            assert_eq!(
                declaration_attrs(stub.attrs)
                    .err()
                    .expect("mixed callable attributes must be rejected")
                    .to_string(),
                "duplicate callable attribute"
            );
        }
    }

    #[test]
    fn relation_boundaries_reject_outputs_options_and_operator_extension() {
        for output in [quote!(I64), quote!(Unit), quote!(_), quote!(!)] {
            let stub = syn::parse2(quote!(fn predicate(value: IList) -> #output;)).unwrap();
            assert_eq!(
                callable(stub, vec![], None, CallableKind::Relation, None)
                    .unwrap_err()
                    .to_string(),
                "relations require an omitted or () output"
            );
        }
        for opts in [
            quote!(no_merge),
            quote!(merge = |old, new| new),
            quote!(from),
            quote!(from(I64)),
            quote!(try_from),
        ] {
            assert_eq!(
                callable(
                    syn::parse_quote!(
                        fn predicate(value: IList);
                    ),
                    options(opts).unwrap(),
                    None,
                    CallableKind::Relation,
                    None,
                )
                .unwrap_err()
                .to_string(),
                "unsupported callable option (from/try_from are constructor-only)"
            );
        }
        for (source, expected) in [
            (
                "impl std::ops::Add<&Right> for &Left { type Output = Left; #[relation] fn add(self, rhs: &Right) -> Left; }",
                "binary constructor declarations support only name",
            ),
            (
                "impl std::ops::Add<&Right> for &Left { type Output = Left; #[relation] fn add(self, rhs: &Right) -> Left { let _ = rhs; Left } }",
                "symbolic declarations must be bodyless",
            ),
        ] {
            assert_eq!(
                operator_declarations(syn::parse_str(source).unwrap())
                    .unwrap_err()
                    .to_string(),
                expected
            );
        }
    }

    #[test]
    fn borrowed_receivers_are_uniform_without_ufcs_conversion_or_named_records() {
        for (kind, source, opts) in [
            (
                CallableKind::Constructor,
                "fn next(&self, index: I64) -> IList;",
                quote!(),
            ),
            (
                CallableKind::Function,
                "fn next(&self, index: I64) -> I64;",
                quote!(no_merge),
            ),
            (
                CallableKind::Relation,
                "fn next(&self, index: I64);",
                quote!(),
            ),
        ] {
            let (method, extra) = callable(
                syn::parse_str(source).unwrap(),
                options(opts).unwrap(),
                Some(&syn::parse_quote!(IList)),
                kind,
                None,
            )
            .unwrap();
            assert!(extra.is_empty());
            let parsed = syn::parse2::<syn::ImplItemFn>(method).unwrap();
            assert!(matches!(&parsed.sig.inputs[0], FnArg::Receiver(receiver)
                if receiver.reference.is_some() && receiver.mutability.is_none()));
        }
        for opts in [quote!(from), quote!(from(I64)), quote!(try_from)] {
            assert_eq!(
                callable(
                    syn::parse_quote!(
                        fn next(&self) -> Other;
                    ),
                    options(opts).unwrap(),
                    Some(&syn::parse_quote!(IList)),
                    CallableKind::Constructor,
                    None,
                )
                .unwrap_err()
                .to_string(),
                "receiver declarations do not support from/try_from"
            );
        }
        for source in ["fn predicate(self);", "fn predicate(&mut self);"] {
            assert_eq!(
                callable(
                    syn::parse_str(source).unwrap(),
                    vec![],
                    Some(&syn::parse_quote!(IList)),
                    CallableKind::Relation,
                    None,
                )
                .unwrap_err()
                .to_string(),
                "relation declarations support only &self receivers"
            );
        }
        assert_eq!(
            callable(
                syn::parse_quote!(
                    fn predicate(&self);
                ),
                options(quote!(args = PredicateArgs)).unwrap(),
                Some(&syn::parse_quote!(IList)),
                CallableKind::Relation,
                None,
            )
            .unwrap_err()
            .to_string(),
            "named argument records require explicit owned arguments"
        );
    }

    #[test]
    fn operator_metadata_has_one_nongeneric_initializer_not_call_site_context() {
        for name in [
            quote!("fixed-name"),
            quote!(counted_name()),
            quote!(::std::any::type_name::<Self>()),
            quote!(::std::any::type_name_of_val(&rhs)),
        ] {
            let item = syn::parse2::<Declarations>(quote! {
                impl std::ops::Add<&Right> for &Left {
                    type Output = Out;
                    #[constructor(name = #name)] fn add(self, rhs: &Right) -> Out;
                }
            })
            .unwrap();
            let expanded = operator_declarations(item).unwrap();
            let parsed = syn::parse2::<syn::ItemConst>(expanded.clone()).unwrap();
            let syn::Expr::Block(block) = parsed.expr.as_ref() else {
                panic!("expected lexical declaration scope")
            };
            let functions = block
                .block
                .stmts
                .iter()
                .filter_map(|stmt| {
                    if let syn::Stmt::Item(syn::Item::Fn(item)) = stmt {
                        Some(item)
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();
            assert_eq!(functions.len(), 1);
            let initializer = functions[0];
            assert!(initializer.sig.generics.params.is_empty());
            assert!(initializer.sig.generics.where_clause.is_none());
            assert!(initializer.sig.inputs.is_empty());
            assert!(
                initializer
                    .block
                    .to_token_stream()
                    .to_string()
                    .contains(&name.to_string())
            );
            assert_eq!(
                expanded
                    .to_string()
                    .matches("Callable :: constructor")
                    .count(),
                1
            );
            for implementation in block
                .block
                .stmts
                .iter()
                .filter_map(|stmt| {
                    if let syn::Stmt::Item(syn::Item::Impl(item)) = stmt {
                        Some(item)
                    } else {
                        None
                    }
                })
                .filter(|item| !item.generics.params.is_empty())
            {
                let ImplItem::Fn(method) = &implementation.items[1] else {
                    panic!("expected operator method")
                };
                assert!(
                    !method
                        .block
                        .to_token_stream()
                        .to_string()
                        .contains(&name.to_string())
                );
                let syn::Stmt::Local(binding) = &method.block.stmts[0] else {
                    panic!("expected cached definition")
                };
                let syn::Expr::MethodCall(call) = binding.init.as_ref().unwrap().expr.as_ref()
                else {
                    panic!("expected get_or_init")
                };
                assert_eq!(call.method, "get_or_init");
                let syn::Expr::Path(factory) = &call.args[0] else {
                    panic!("expected nongeneric initializer item")
                };
                assert!(factory.path.leading_colon.is_none());
                assert_eq!(factory.path.segments.len(), 1);
                assert_eq!(factory.path.segments[0].ident, initializer.sig.ident);
            }
        }
    }

    #[test]
    fn ordinary_free_and_inherent_name_expressions_keep_their_original_context() {
        for owner in [None, Some(syn::parse_quote!(Term))] {
            let stub = syn::parse_str::<Stub>("fn make(rhs: Term) -> Term;").unwrap();
            let (method, extra) = callable(
                stub,
                options(quote!(name = ::std::any::type_name_of_val(&rhs))).unwrap(),
                owner.as_ref(),
                CallableKind::Constructor,
                None,
            )
            .unwrap();
            assert!(extra.is_empty());
            let parsed = syn::parse2::<syn::ItemFn>(method).unwrap();
            assert!(
                parsed
                    .block
                    .to_token_stream()
                    .to_string()
                    .contains(&quote!(::std::any::type_name_of_val(&rhs)).to_string())
            );
            assert!(
                parsed
                    .block
                    .stmts
                    .iter()
                    .any(|stmt| matches!(stmt, syn::Stmt::Item(syn::Item::Static(_))))
            );
        }
        let stub = syn::parse_str::<Stub>("fn read(&self) -> I64;").unwrap();
        let (method, extra) = callable(
            stub,
            options(quote!(no_merge, name = ::std::any::type_name::<Self>())).unwrap(),
            Some(&syn::parse_quote!(Term)),
            CallableKind::Function,
            None,
        )
        .unwrap();
        assert!(extra.is_empty());
        assert!(
            method
                .to_string()
                .contains(&quote!(::std::any::type_name::<Self>()).to_string())
        );
    }

    #[test]
    fn binary_operator_variants_share_one_cache_and_fixed_owned_signature() {
        for (operator, method) in [
            ("Add", "add"),
            ("Sub", "sub"),
            ("Mul", "mul"),
            ("Div", "div"),
            ("Rem", "rem"),
        ] {
            let item = syn::parse_str::<Declarations>(&format!(
                "impl std::ops::{operator}<&Right> for &Left {{ type Output = Out; #[constructor(name = \"exact-name\")] fn {method}(self, rhs: &Right) -> Out; }}"
            )).unwrap();
            let expanded = operator_declarations(item).unwrap();
            let parsed = syn::parse2::<syn::ItemConst>(expanded.clone()).unwrap();
            let syn::Expr::Block(block) = parsed.expr.as_ref() else {
                panic!("expected lexical declaration scope")
            };
            let statics = block
                .block
                .stmts
                .iter()
                .filter(|stmt| matches!(stmt, syn::Stmt::Item(syn::Item::Static(_))))
                .count();
            assert_eq!(statics, 1);
            let impls = block
                .block
                .stmts
                .iter()
                .filter_map(|stmt| {
                    if let syn::Stmt::Item(syn::Item::Impl(item)) = stmt {
                        Some(item)
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();
            assert_eq!(impls.len(), 3); // original-signature witness + two real trait impls
            assert!(impls[0].generics.params.is_empty());
            let ImplItem::Fn(witness) = &impls[0].items[1] else {
                panic!("expected original signature witness")
            };
            assert!(
                matches!(&witness.sig.inputs[1], FnArg::Typed(rhs) if matches!(rhs.ty.as_ref(), Type::Reference(_)))
            );
            for implementation in &impls[1..] {
                assert_eq!(implementation.generics.params.len(), 1);
                let ImplItem::Fn(member) = &implementation.items[1] else {
                    panic!("expected concrete trait method")
                };
                assert_eq!(member.sig.ident, method);
                assert!(
                    matches!(&member.sig.inputs[1], FnArg::Typed(rhs) if matches!(rhs.ty.as_ref(), Type::Path(_)))
                );
                let tuple = member
                    .block
                    .stmts
                    .iter()
                    .find_map(|stmt| {
                        let syn::Stmt::Local(local) = stmt else {
                            return None;
                        };
                        let Pat::Type(typed) = &local.pat else {
                            return None;
                        };
                        let Type::Tuple(tuple) = typed.ty.as_ref() else {
                            return None;
                        };
                        Some(tuple)
                    })
                    .expect("expected once-converted fixed-sort tuple");
                assert_eq!(
                    tuple
                        .elems
                        .iter()
                        .map(|ty| ty.to_token_stream().to_string())
                        .collect::<Vec<_>>(),
                    ["Left", "Right"]
                );
            }
            let tokens = expanded.to_string();
            assert_eq!(tokens.matches("OnceLock :: new").count(), 1);
            assert_eq!(tokens.matches("get_or_init").count(), 2);
            assert!(tokens.contains(&quote!(::std::convert::Into<Right>).to_string()));
            assert!(
                tokens.contains(
                    &quote!(<Right as ::egglog_experimental::typed::EgglogValue>::sort_ref())
                        .to_string()
                )
            );
            assert!(tokens.contains(
                &quote!(<Out as ::egglog_experimental::typed::EgglogValue>::sort_ref()).to_string()
            ));
        }
    }

    #[test]
    fn operator_default_identity_keeps_original_trait_not_generated_rhs() {
        let item = syn::parse_str::<Declarations>(
            "impl core::ops::Add<&Right> for &Left { type Output = Out; #[constructor] fn add(self, rhs: &Right) -> Out; }"
        ).unwrap();
        let expanded = operator_declarations(item).unwrap().to_string();
        assert!(expanded.contains(&quote!(stringify!(Left)).to_string()));
        assert!(expanded.contains(&quote!(stringify!(core::ops::Add<&Right>)).to_string()));
        assert!(!expanded.contains(&quote!(stringify!(__EgglogRhs)).to_string()));
        let wrong = syn::parse_str::<Declarations>(
            "impl std::ops::Sub<&Right> for &Left { type Output = Out; #[constructor] fn add(self, rhs: &Right) -> Out; }"
        ).unwrap();
        let wrong = operator_declarations(wrong).unwrap().to_string();
        // Do not silently rename the authored method to make invalid Rust pass.
        assert!(wrong.contains("fn sub (self , rhs : __EgglogRhs)"));
        assert!(wrong.contains("fn add (self , rhs : & Right)"));
    }

    #[test]
    fn operator_hygiene_and_cfg_projection_preserve_authored_item_scopes() {
        let item = syn::parse_str::<Declarations>(
            "#[cfg_attr(feature = \"outer\", cfg(any()), allow(dead_code))] impl std::ops::Add<&__EgglogRhs> for &__EgglogSignature { type Output = __EgglogSignature; #[cfg_attr(feature = \"inner\", cfg(any()), inline)] #[constructor] fn add(self, __egglog_argument_0: &__EgglogRhs) -> __EgglogSignature; }"
        ).unwrap();
        let expanded = operator_declarations(item).unwrap();
        let parsed = syn::parse2::<syn::ItemConst>(expanded.clone()).unwrap();
        assert_eq!(parsed.attrs.len(), 2);
        assert_eq!(
            parsed.attrs[0].meta.to_token_stream().to_string(),
            quote!(cfg_attr(feature = "outer", cfg(any()))).to_string()
        );
        assert_eq!(
            parsed.attrs[1].meta.to_token_stream().to_string(),
            quote!(cfg_attr(feature = "inner", cfg(any()))).to_string()
        );
        let tokens = expanded.to_string();
        assert!(tokens.contains("trait __EgglogSignature_1"));
        assert!(tokens.contains("__EgglogRhs_1 : :: std :: convert :: Into < __EgglogRhs >"));
        assert!(
            tokens.contains(&quote!(cfg_attr(feature = "inner", cfg(any()), inline)).to_string())
        );
        assert!(tokens.contains(&quote!(::core::unreachable!()).to_string()));
    }

    #[test]
    fn binary_operator_boundary_keeps_ordinary_bodies_unexpanded() {
        for source in [
            "impl custom::Add<&Right> for &Left { type Output = Left; fn add(self, rhs: &Right) -> Left; }",
            "impl std::ops::BitAnd<&Right> for &Left { type Output = Left; fn bitand(self, rhs: &Right) -> Left; }",
            "impl std::ops::Add for Left { type Output = Left; fn add(self, rhs: Left) -> Left; }",
            "impl std::ops::Add<&Right> for &Left { type Output = Left; #[function(no_merge)] fn add(self, rhs: &Right) -> Left; }",
            "impl std::ops::Add<&Right> for &Left { type Output = Left; #[constructor(from)] fn add(self, rhs: &Right) -> Left; }",
            "impl std::ops::Add<&Right> for &Left { type Output = Left; fn add(&mut self, rhs: &Right) -> Left; }",
        ] {
            let item = syn::parse_str::<Declarations>(source).unwrap();
            assert!(operator_declarations(item).is_err(), "{source}");
        }
        let item = syn::parse_str::<Declarations>(
            "impl std::ops::Add<&Plain> for &Plain { type Output = Plain; fn add(self, rhs: &Plain) -> Plain { let _ = rhs; Plain } }"
        ).unwrap();
        let expanded = operator_declarations(item).unwrap();
        let parsed = syn::parse2::<syn::ItemImpl>(expanded.clone()).unwrap();
        assert!(parsed.generics.params.is_empty());
        assert!(matches!(parsed.self_ty.as_ref(), Type::Reference(_)));
        assert!(!expanded.to_string().contains("OnceLock"));
    }

    #[test]
    fn constructor_source_lists_preserve_concrete_impls_cfg_and_bare_conversions() {
        let stub = syn::parse_str::<Stub>(
            "#[cfg(feature = \"authored\")] pub fn MNum(__egglog_value: I64) -> Self;",
        )
        .unwrap();
        let (method, extra) = callable(
            stub,
            options(quote!(from(i32, i64, &i32, &i64))).unwrap(),
            Some(&syn::parse_quote!(DimExpr)),
            CallableKind::Constructor,
            None,
        )
        .unwrap();
        assert!(method.to_string().contains("OnceLock"));
        let items = syn::parse2::<syn::File>(extra).unwrap();
        let sources = items
            .items
            .iter()
            .map(|item| {
                let syn::Item::Impl(item) = item else {
                    panic!("expected a concrete conversion impl");
                };
                assert!(item.generics.params.is_empty());
                assert_eq!(item.attrs.len(), 1);
                assert!(item.attrs[0].path().is_ident("cfg"));
                let (_, path, _) = item.trait_.as_ref().unwrap();
                let syn::PathArguments::AngleBracketed(args) =
                    &path.segments.last().unwrap().arguments
                else {
                    panic!("expected From source");
                };
                assert!(
                    item.to_token_stream()
                        .to_string()
                        .contains("DimExpr > :: MNum")
                );
                args.args[0].to_token_stream().to_string()
            })
            .collect::<Vec<_>>();
        assert_eq!(sources, ["I64", "& I64", "i32", "i64", "& i32", "& i64"]);

        for opts in [quote!(from, try_from), quote!(from(), try_from)] {
            let stub = syn::parse_str::<Stub>("fn Wrap(value: Atom) -> Math;").unwrap();
            let (_, extra) = callable(
                stub,
                options(opts).unwrap(),
                None,
                CallableKind::Constructor,
                None,
            )
            .unwrap();
            assert_eq!(syn::parse2::<syn::File>(extra).unwrap().items.len(), 4);
        }
    }

    #[test]
    fn constructor_source_lists_retain_coherence_and_callable_guards() {
        for (opts, expected) in [
            (quote!(from(i64, i64)), "duplicate from source type"),
            (quote!(from(I64)), "duplicate from source type"),
            (quote!(from(&I64)), "duplicate from source type"),
            (
                quote!(from(Self)),
                "from cannot replace an identity or borrowed sort conversion",
            ),
            (
                quote!(from(&Self)),
                "from cannot replace an identity or borrowed sort conversion",
            ),
            (
                quote!(try_from(i64)),
                "unsupported callable option (from/try_from are constructor-only)",
            ),
        ] {
            let stub = syn::parse_str::<Stub>("fn MNum(value: I64) -> Self;").unwrap();
            assert_eq!(
                callable(
                    stub,
                    options(opts).unwrap(),
                    Some(&syn::parse_quote!(DimExpr)),
                    CallableKind::Constructor,
                    None,
                )
                .expect_err("invalid source list must be rejected")
                .to_string(),
                expected
            );
        }
        for source in [
            "fn Empty() -> DimExpr;",
            "fn Pair(a: I64, b: I64) -> DimExpr;",
        ] {
            let stub = syn::parse_str::<Stub>(source).unwrap();
            assert_eq!(
                callable(
                    stub,
                    options(quote!(from(i64))).unwrap(),
                    None,
                    CallableKind::Constructor,
                    None,
                )
                .expect_err("nonunary conversion must be rejected")
                .to_string(),
                "from/try_from require a unary constructor with a different input sort"
            );
        }
        let stub = syn::parse_str::<Stub>("fn Read(key: I64) -> I64;").unwrap();
        assert_eq!(
            callable(
                stub,
                options(quote!(no_merge, from(i64))).unwrap(),
                None,
                CallableKind::Function,
                None,
            )
            .expect_err("function conversion must be rejected")
            .to_string(),
            "unsupported callable option (from/try_from are constructor-only)"
        );
        assert_eq!(
            options(quote!(from, from(i64)))
                .err()
                .expect("duplicate options must be rejected")
                .to_string(),
            "duplicate declaration option"
        );
    }

    #[test]
    fn luminal_loop_start_has_five_ordered_fields() {
        let stub = syn::parse_str::<Stub>(
            "pub fn LoopStart(inp: Ir, loop_id: I64, slot_idx: I64, iters: DimExpr, dtype: DType) -> Self;",
        )
        .unwrap();
        let (method, extra) = callable(
            stub,
            options(quote!(name = "LoopStart", args = LoopStartArgs)).unwrap(),
            Some(&syn::parse_quote!(Ir)),
            CallableKind::Constructor,
            None,
        )
        .unwrap();
        syn::parse2::<syn::ItemFn>(method).unwrap();
        let items = syn::parse2::<syn::File>(extra).unwrap();
        let syn::Item::Struct(fields) = &items.items[0] else {
            panic!("expected the named argument record");
        };
        assert_eq!(
            fields
                .fields
                .iter()
                .map(|field| (
                    field.ident.as_ref().unwrap().to_string(),
                    field.ty.to_token_stream().to_string(),
                ))
                .collect::<Vec<_>>(),
            [
                ("inp", "Ir"),
                ("loop_id", "I64"),
                ("slot_idx", "I64"),
                ("iters", "DimExpr"),
                ("dtype", "DType"),
            ]
            .map(|(name, sort)| (name.to_owned(), sort.to_owned()))
        );
    }

    #[test]
    fn function_options_have_specific_diagnostics_and_share_named_record_emission() {
        for (opts, expected) in [
            (
                quote!(),
                "functions require exactly one of no_merge or merge",
            ),
            (
                quote!(no_merge, from),
                "unsupported callable option (from/try_from are constructor-only)",
            ),
            (
                quote!(no_merge, try_from),
                "unsupported callable option (from/try_from are constructor-only)",
            ),
            (quote!(no_merge, args = "bad"), "args needs a record name"),
            (
                quote!(no_merge, args = path::Record),
                "args needs an unqualified record name",
            ),
        ] {
            let stub = syn::parse_str::<Stub>("fn read(key: I64) -> I64;").unwrap();
            assert_eq!(
                callable(
                    stub,
                    options(opts).unwrap(),
                    None,
                    CallableKind::Function,
                    None
                )
                .unwrap_err()
                .to_string(),
                expected
            );
        }
        for source in [
            "fn read<T>(key: T) -> I64;",
            "unsafe fn read(key: I64) -> I64;",
        ] {
            let stub = syn::parse_str::<Stub>(source).unwrap();
            assert_eq!(
                callable(
                    stub,
                    options(quote!(no_merge)).unwrap(),
                    None,
                    CallableKind::Function,
                    None,
                )
                .unwrap_err()
                .to_string(),
                "callables require monomorphic safe ordinary signatures"
            );
        }
        for function in [false, true] {
            let stub = syn::parse_str::<Stub>("pub fn read(key: I64) -> I64;").unwrap();
            let opts = if function {
                quote!(no_merge, args = ReadArgs)
            } else {
                quote!(args = ReadArgs)
            };
            let (_, record) = callable(
                stub,
                options(opts).unwrap(),
                None,
                if function {
                    CallableKind::Function
                } else {
                    CallableKind::Constructor
                },
                None,
            )
            .unwrap();
            assert!(record.to_string().contains("pub struct ReadArgs"));
        }
    }

    #[test]
    fn merged_functions_keep_owned_callback_sorts_and_borrowed_inherent_receiver() {
        let stub = syn::parse_str::<Stub>("pub fn lower(&self) -> I64;").unwrap();
        let (method, extra) = callable(
            stub,
            options(quote!(
                name = "lower",
                merge = |old: I64, new: I64| old.max(new)
            ))
            .unwrap(),
            Some(&syn::parse_quote!(DimExpr)),
            CallableKind::Function,
            None,
        )
        .unwrap();
        let parsed = syn::parse2::<syn::ImplItemFn>(method.clone()).unwrap();
        assert!(extra.is_empty());
        let output = method.to_string();
        assert!(matches!(parsed.vis, Visibility::Public(_)));
        assert!(
            matches!(&parsed.sig.inputs[0], FnArg::Receiver(receiver) if receiver.reference.is_some())
        );
        assert!(output.contains(
            &quote!(<DimExpr as ::egglog_experimental::typed::EgglogValue>::sort_ref()).to_string()
        ));
        assert!(output.contains(&quote!(|old: I64, new: I64| old.max(new)).to_string()));
        assert!(output.contains("OnceLock"));
        assert!(output.contains("get_or_init"));
        for (opts, expected) in [
            (
                quote!(no_merge, merge = |old: I64, new: I64| old.max(new)),
                "functions require exactly one of no_merge or merge",
            ),
            (
                quote!(merge = callback),
                "merge needs a two-argument closure",
            ),
            (
                quote!(merge = |old: I64| old),
                "merge needs an ordinary two-argument closure",
            ),
        ] {
            let stub = syn::parse_str::<Stub>("fn read(key: I64) -> I64;").unwrap();
            assert_eq!(
                callable(
                    stub,
                    options(opts).unwrap(),
                    None,
                    CallableKind::Function,
                    None
                )
                .unwrap_err()
                .to_string(),
                expected
            );
        }
        for source in ["fn lower(self) -> I64;", "fn lower(&mut self) -> I64;"] {
            let stub = syn::parse_str::<Stub>(source).unwrap();
            assert_eq!(
                callable(
                    stub,
                    options(quote!(no_merge)).unwrap(),
                    Some(&syn::parse_quote!(DimExpr)),
                    CallableKind::Function,
                    None,
                )
                .unwrap_err()
                .to_string(),
                "function declarations support only &self receivers"
            );
        }
    }

    #[test]
    fn lazy_ruleset_preserves_body_output_visibility_and_attributes() {
        let item = syn::parse_quote! {
            #[cfg(feature = "lazy-test")]
            /// Authored documentation.
            pub(crate) fn authored(mut first: &I64, second: &Bool) -> Vec<Rule> {
                #![allow(unused_variables)]
                let chosen = first;
                vec![rewrite(chosen, second)]
            }
        };
        let expanded = ruleset_item(item, vec![]).unwrap();
        let parsed = syn::parse2::<syn::ItemStatic>(expanded.clone()).unwrap();
        assert!(
            parsed
                .attrs
                .iter()
                .all(|attr| matches!(attr.style, syn::AttrStyle::Outer))
        );
        let expected = quote! {
            #[cfg(feature = "lazy-test")]
            /// Authored documentation.
            #[allow(unused_variables)]
            #[allow(non_upper_case_globals)]
            pub(crate) static authored: ::std::sync::LazyLock<::egglog_experimental::typed::Ruleset> =
                ::std::sync::LazyLock::new(|| ::egglog_experimental::typed::__private::named_ruleset(
                    || ::std::option::Option::Some((concat!(module_path!(), "::", stringify!(authored))).into()),
                    |mut first: &I64, second: &Bool| -> Vec<Rule> {
                        let chosen = first;
                        vec![rewrite(chosen, second)]
                    },
                ));
        };
        assert_eq!(expanded.to_string(), expected.to_string());
    }

    #[test]
    fn lazy_ruleset_evaluates_the_exact_name_expression_only_in_its_initializer() {
        for name in [
            quote!(""),
            quote!({
                NAME_CALLS.fetch_add(1, Ordering::SeqCst);
                String::from("exact::name")
            }),
        ] {
            let item = syn::parse_quote!(
                fn named() -> _ {
                    vec![]
                }
            );
            let expanded = ruleset_item(item, options(quote!(name = #name)).unwrap()).unwrap();
            let parsed = syn::parse2::<syn::ItemStatic>(expanded.clone()).unwrap();
            let syn::Expr::Call(initializer) = parsed.expr.as_ref() else {
                panic!("expected LazyLock::new");
            };
            let syn::Expr::Closure(lazy) = &initializer.args[0] else {
                panic!("expected one lazy initializer");
            };
            assert!(lazy.inputs.is_empty());
            let syn::Expr::Call(construction) = lazy.body.as_ref() else {
                panic!("expected construction inside the initializer");
            };
            assert_eq!(construction.args.len(), 2);
            let syn::Expr::Closure(name_initializer) = &construction.args[0] else {
                panic!("expected deferred name evaluation");
            };
            assert!(name_initializer.inputs.is_empty());
            assert_eq!(
                name_initializer.body.to_token_stream().to_string(),
                quote!(::std::option::Option::Some((#name).into())).to_string()
            );
            let syn::Expr::Closure(callback) = &construction.args[1] else {
                panic!("expected the original callback");
            };
            assert!(callback.inputs.is_empty());
            assert!(matches!(
                &callback.output,
                ReturnType::Type(_, ty) if matches!(ty.as_ref(), Type::Infer(_))
            ));
            assert_eq!(
                expanded.to_string().matches("NAME_CALLS").count(),
                usize::from(name.to_string().contains("NAME_CALLS"))
            );
        }
    }

    #[test]
    fn lazy_ruleset_rejects_unsupported_options_signatures_and_parameters() {
        assert_eq!(
            options(quote!(name = "one", name = "two"))
                .err()
                .expect("duplicate options must be rejected")
                .to_string(),
            "duplicate declaration option"
        );
        for option in [quote!(name), quote!(name("bad")), quote!(label = "bad")] {
            assert_eq!(
                ruleset_item(
                    syn::parse_quote!(
                        fn group() {}
                    ),
                    options(option).unwrap()
                )
                .unwrap_err()
                .to_string(),
                "only name is supported on a ruleset"
            );
        }
        for source in [
            "fn group<T>() {}",
            "fn group() where I64: Clone {}",
            "const fn group() {}",
            "async fn group() {}",
            "unsafe fn group() {}",
            "extern \"C\" fn group() {}",
            "extern \"C\" fn group(...) {}",
        ] {
            let item = syn::parse_str(source).unwrap();
            assert_eq!(
                ruleset_item(item, vec![]).unwrap_err().to_string(),
                "rulesets require monomorphic safe ordinary signatures"
            );
        }
        for source in [
            "fn group(&self) {}",
            "fn group(ref value: &I64) {}",
            "fn group((left, right): &(I64, I64)) {}",
            "fn group(value @ _: &I64) {}",
        ] {
            let item = syn::parse_str(source).unwrap();
            assert_eq!(
                ruleset_item(item, vec![]).unwrap_err().to_string(),
                "ruleset arguments must be plain identifiers"
            );
        }
        for source in ["fn group(value: I64) {}", "fn group(value: &mut I64) {}"] {
            let item = syn::parse_str(source).unwrap();
            assert_eq!(
                ruleset_item(item, vec![]).unwrap_err().to_string(),
                "ruleset arguments must be immutable borrows"
            );
        }
        for (source, expected) in [
            (
                "fn group(value: &impl EgglogValue) {}",
                "ruleset callbacks do not support impl Trait inputs",
            ),
            (
                "fn group() -> impl IntoRuleset {}",
                "ruleset callbacks do not support impl Trait outputs",
            ),
        ] {
            assert_eq!(
                ruleset_item(syn::parse_str(source).unwrap(), vec![])
                    .unwrap_err()
                    .to_string(),
                expected
            );
        }
        for count in [35, 36] {
            let names = (0..count)
                .map(|index| Ident::new(&format!("value_{index}"), proc_macro2::Span::call_site()))
                .collect::<Vec<_>>();
            let item = syn::parse2(quote!(fn group(#(#names: &I64),*) {})).unwrap();
            let expanded = ruleset_item(item, vec![]);
            if count == 35 {
                syn::parse2::<syn::ItemStatic>(expanded.unwrap()).unwrap();
            } else {
                assert_eq!(
                    expanded.unwrap_err().to_string(),
                    "rulesets support at most 35 borrowed arguments"
                );
            }
        }
    }
}
