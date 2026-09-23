//! Ordinary Rust declarations constructing portable symbolic expressions.
//!
//! Callable names default to their declaration's module and Rust name: free
//! declarations use `module::function`, inherent methods
//! use `module::Type::method`, and trait methods include the authored trait path
//! as `module::<Type as Trait>::method`. Generated operator ownership and
//! conversion forms share that one name. Importing or reexporting a declaration
//! does not change its identity.
//!
//! Use `name = "native-name"` only when an external integration or an intentional
//! compatible alias needs a particular Egglog identity. It does not rename the
//! Rust callable or its displayed syntax; declarations sharing an explicit name
//! must have compatible sorts, kind, and semantic options.
use proc_macro::TokenStream;
use proc_macro2::TokenStream as Tokens;
use quote::{ToTokens, quote};
use syn::{
    Attribute, Fields, FnArg, Ident, ImplItem, ItemStruct, Meta, Pat, Path, ReturnType, Signature,
    Token, Type, Visibility,
    parse::{Parse, ParseStream},
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
        let value = Self {
            attrs: input.call(Attribute::parse_outer)?,
            vis: input.parse()?,
            sig: input.parse()?,
        };
        input.parse::<Token![;]>()?;
        Ok(value)
    }
}
fn unique_options(opts: impl IntoIterator<Item = Meta>) -> syn::Result<Vec<Meta>> {
    let mut seen = std::collections::HashSet::new();
    opts.into_iter()
        .map(|option| {
            if let Some(name) = option.path().get_ident()
                && !seen.insert(name.to_string())
            {
                return Err(syn::Error::new_spanned(
                    &option,
                    format!("duplicate declaration option `{name}`"),
                ));
            }
            Ok(option)
        })
        .collect()
}
fn options(input: TokenStream) -> syn::Result<Vec<Meta>> {
    use syn::parse::Parser;
    Punctuated::<Meta, Token![,]>::parse_terminated
        .parse(input)
        .and_then(unique_options)
}
/// Defines a lazily authored, immutable ruleset with the function's name.
#[proc_macro_attribute]
pub fn ruleset(args: TokenStream, item: TokenStream) -> TokenStream {
    let item = parse_macro_input!(item as syn::ItemFn);
    let result = (|| {
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
                "rulesets require monomorphic, safe, non-const, non-async Rust functions",
            ));
        }
        if sig.inputs.len() > 128 {
            return Err(syn::Error::new_spanned(
                &sig.inputs,
                "rulesets support at most 128 borrowed parameters",
            ));
        }
        for input in &sig.inputs {
            let FnArg::Typed(input) = input else {
                return Err(syn::Error::new_spanned(
                    input,
                    "rulesets cannot have a receiver",
                ));
            };
            if !matches!(&*input.pat, Pat::Ident(pat) if pat.by_ref.is_none() && pat.subpat.is_none())
            {
                return Err(syn::Error::new_spanned(
                    &input.pat,
                    "a ruleset parameter must be a named borrowed variable",
                ));
            }
            if !matches!(&*input.ty, Type::Reference(reference) if reference.mutability.is_none()) {
                return Err(syn::Error::new_spanned(
                    &input.ty,
                    "a ruleset parameter must borrow its symbolic sort: name: &Sort",
                ));
            }
        }
        let ident = &sig.ident;
        let mut name = quote!(concat!(module_path!(), "::", stringify!(#ident)));
        for opt in options(args)? {
            match opt {
                Meta::NameValue(value) if value.path.is_ident("name") => {
                    let value = value.value;
                    name = quote!(#value);
                }
                value => {
                    return Err(syn::Error::new_spanned(
                        value,
                        "expected name = \"diagnostic name\"",
                    ));
                }
            }
        }
        let syn::ItemFn {
            mut attrs,
            vis,
            sig,
            block,
        } = item;
        // Inner function attributes apply to the item too (including cfg/docs).
        // Keep that scope on the generated static, which has no function body.
        for attr in &mut attrs {
            attr.style = syn::AttrStyle::Outer;
        }
        let ident = sig.ident;
        let inputs = sig.inputs;
        let output = sig.output;
        Ok(quote! {
            #(#attrs)*
            #[allow(non_upper_case_globals)]
            #vis static #ident: ::std::sync::LazyLock<::egglog_experimental::typed::Ruleset> =
                ::std::sync::LazyLock::new(|| {
                    ::egglog_experimental::typed::ruleset(|#inputs| #output #block).label(#name)
                });
        })
    })();
    result.unwrap_or_else(syn::Error::into_compile_error).into()
}
fn sort_impl(vis: &Visibility, ident: &Ident, attrs: &[Attribute], name: Tokens) -> Tokens {
    quote! {
        #(#attrs)* #[derive(Clone,PartialEq,Eq,Hash,Debug)] #vis struct #ident(::egglog_experimental::typed::__private::Expr);
        impl ::egglog_experimental::typed::__private::ValueInput for #ident {type Owned=Self;}
        impl From<&#ident> for #ident {fn from(value:&#ident)->Self {value.clone()}}
        impl ::egglog_experimental::typed::EgglogValue for #ident {
            fn sort_ref()->::egglog_experimental::typed::SortRef {::egglog_experimental::typed::SortRef::equality(#name)}
            fn expression(&self)->&::egglog_experimental::typed::__private::Expr {&self.0}
            fn from_expression(expr: ::egglog_experimental::typed::__private::Expr)->Self {Self(expr)}
        }
        impl ::egglog_experimental::typed::EqualitySort for #ident {}
        impl ::std::fmt::Display for #ident {
            fn fmt(&self,f:&mut ::std::fmt::Formatter<'_>)->::std::fmt::Result {::std::fmt::Display::fmt(&self.0,f)}
        }
    }
}
#[proc_macro_attribute]
pub fn sort(args: TokenStream, item: TokenStream) -> TokenStream {
    let item = parse_macro_input!(item as ItemStruct);
    let result = (|| {
        if !matches!(item.fields, Fields::Unit) || !item.generics.params.is_empty() {
            return Err(syn::Error::new_spanned(
                &item,
                "a sort must be a monomorphic unit struct",
            ));
        }
        let ident = &item.ident;
        let mut name = quote!(concat!(module_path!(), "::", stringify!(#ident)));
        for opt in options(args)? {
            match opt {
                Meta::NameValue(x) if x.path.is_ident("name") => {
                    let v = x.value;
                    name = quote!(#v);
                }
                x => {
                    return Err(syn::Error::new_spanned(
                        x,
                        "expected name = \"qualified-name\"",
                    ));
                }
            }
        }
        Ok(sort_impl(&item.vis, ident, &item.attrs, name))
    })();
    result.unwrap_or_else(syn::Error::into_compile_error).into()
}

#[derive(Clone, Default)]
struct Context {
    owner: Option<Type>,
    trait_path: Option<Path>,
    output: Option<Type>,
    nominal: Option<Tokens>,
    syntax: Option<Tokens>,
    shared: bool,
    // The generated Rust RHS is generic, but the callable has one fixed sort.
    binary_rhs: Option<Type>,
    cfg: Vec<Attribute>,
}
fn fresh_ident(prefix: &str, authored: &str) -> Ident {
    let mut suffix = 0;
    while authored.contains(&format!("{prefix}{suffix}")) {
        suffix += 1;
    }
    Ident::new(
        &format!("{prefix}{suffix}"),
        proc_macro2::Span::mixed_site(),
    )
}
fn resolve_type(ty: &Type, context: &Context, keep_reference: bool) -> syn::Result<Type> {
    if let Type::Reference(reference) = ty
        && !keep_reference
    {
        if reference.mutability.is_some() {
            return Err(syn::Error::new_spanned(
                ty,
                "mutable references are not symbolic operands",
            ));
        }
        return resolve_type(&reference.elem, context, false);
    }
    // Metadata lives outside the authored impl's `Self` scope, including when
    // `Self` occurs inside a container's type arguments.
    struct Resolve<'a> {
        context: &'a Context,
        error: Option<syn::Error>,
    }
    impl syn::visit_mut::VisitMut for Resolve<'_> {
        fn visit_type_mut(&mut self, ty: &mut Type) {
            if let Type::Path(path) = ty
                && path.qself.is_none()
                && path
                    .path
                    .segments
                    .first()
                    .is_some_and(|s| s.ident == "Self")
            {
                let replacement = if path.path.is_ident("Self") {
                    self.context.owner.clone()
                } else if path.path.segments.len() == 2 && path.path.segments[1].ident == "Output" {
                    self.context.output.clone()
                } else {
                    None
                };
                if let Some(replacement) = replacement {
                    *ty = replacement;
                } else {
                    self.error = Some(syn::Error::new_spanned(
                        ty,
                        "declarations require concrete Self or Self::Output types",
                    ));
                }
                return;
            }
            syn::visit_mut::visit_type_mut(self, ty);
        }
    }
    let mut resolved = ty.clone();
    let mut resolver = Resolve {
        context,
        error: None,
    };
    syn::visit_mut::VisitMut::visit_type_mut(&mut resolver, &mut resolved);
    resolver.error.map_or(Ok(resolved), Err)
}
fn callable(
    mut stub: Stub,
    opts: Vec<Meta>,
    kind: &str,
    context: &Context,
) -> syn::Result<(Tokens, Tokens, Tokens, Tokens)> {
    let authored = quote!(#(#opts)*).to_string()
        + &stub.sig.to_token_stream().to_string()
        + &context.owner.to_token_stream().to_string()
        + &context.binary_rhs.to_token_stream().to_string();
    let declaration = fresh_ident("__EgglogDeclaration", &authored);
    if !stub.sig.generics.params.is_empty()
        || stub.sig.generics.where_clause.is_some()
        || stub.sig.asyncness.is_some()
        || stub.sig.unsafety.is_some()
        || stub.sig.variadic.is_some()
        || stub.sig.constness.is_some()
        || stub.sig.abi.is_some()
    {
        return Err(syn::Error::new_spanned(
            &stub.sig,
            "declarations must be monomorphic fixed-arity safe functions",
        ));
    }
    let name = stub.sig.ident.clone();
    let mut nominal =
        context
            .nominal
            .clone()
            .unwrap_or_else(|| match (&context.owner, &context.trait_path) {
                (Some(owner), Some(trait_path)) => quote!(concat!(
                    module_path!(),
                    "::<",
                    stringify!(#owner),
                    " as ",
                    stringify!(#trait_path),
                    ">::",
                    stringify!(#name)
                )),
                (Some(owner), None) => quote!(concat!(
                    module_path!(),
                    "::",
                    stringify!(#owner),
                    "::",
                    stringify!(#name)
                )),
                _ => quote!(concat!(module_path!(), "::", stringify!(#name))),
            });
    let mut fields = vec![];
    let mut types = vec![];
    let mut record_fields = vec![];
    let mut borrowed_inputs = vec![];
    let mut receiver = false;
    for input in &mut stub.sig.inputs {
        match input {
            FnArg::Receiver(r) => {
                if r.mutability.is_some() || r.colon_token.is_some() {
                    return Err(syn::Error::new_spanned(
                        r,
                        "only self or &self receivers are supported",
                    ));
                }
                receiver = true;
                fields.push(quote!(self));
                record_fields.push(Ident::new("receiver", r.self_token.span));
                borrowed_inputs.push(r.reference.is_some());
                types.push(context.owner.clone().ok_or_else(|| {
                    syn::Error::new_spanned(r, "receivers require #[declarations] on an impl")
                })?);
            }
            FnArg::Typed(p) => {
                let Pat::Ident(ident) = p.pat.as_ref() else {
                    return Err(syn::Error::new_spanned(p, "arguments must be named"));
                };
                if ident.by_ref.is_some() || ident.subpat.is_some() {
                    return Err(syn::Error::new_spanned(
                        ident,
                        "arguments must be plain identifiers",
                    ));
                }
                let field = &ident.ident;
                fields.push(quote!(#field));
                record_fields.push(field.clone());
                borrowed_inputs.push(matches!(p.ty.as_ref(), Type::Reference(_)));
                let ty = match &context.binary_rhs {
                    Some(rhs) => rhs.clone(),
                    None => resolve_type(&p.ty, context, false)?,
                };
                if context.trait_path.is_none() {
                    p.ty = Box::new(syn::parse_quote!(impl Into<#ty>));
                }
                types.push(ty);
            }
        }
    }
    let output: Type = if kind == "Relation" {
        if matches!(stub.sig.output, ReturnType::Default) {
            stub.sig.output = syn::parse_quote!(-> ::egglog_experimental::typed::Relation);
        } else if context.trait_path.is_some() {
            match &stub.sig.output {
                ReturnType::Type(_, t) if matches!(t.as_ref(),Type::Path(p) if p.path.segments.last().is_some_and(|s|s.ident=="Relation")) =>
                    {}
                _ => {
                    return Err(syn::Error::new_spanned(
                        &stub.sig,
                        "a relation trait method must return Relation",
                    ));
                }
            }
        } else {
            return Err(syn::Error::new_spanned(
                &stub.sig,
                "free and inherent relation stubs omit their return type",
            ));
        }
        syn::parse_quote!(::egglog_experimental::typed::builtins::Unit)
    } else {
        let ReturnType::Type(_, ty) = &stub.sig.output else {
            return Err(syn::Error::new_spanned(
                &stub.sig,
                "an output sort is required",
            ));
        };
        if matches!(ty.as_ref(), Type::Reference(_)) {
            return Err(syn::Error::new_spanned(
                ty,
                "symbolic outputs must be owned sort wrappers",
            ));
        }
        resolve_type(ty, context, false)?
    };
    let mut cost = quote!(None);
    let mut unextractable = false;
    let mut merge = quote!(None);
    let mut policy = false;
    let mut from = None;
    let mut try_from = None;
    let mut named_args = None;
    let span = Ident::new("__egglog_span", proc_macro2::Span::mixed_site());
    let old = Ident::new("__egglog_old", proc_macro2::Span::mixed_site());
    let new = Ident::new("__egglog_new", proc_macro2::Span::mixed_site());
    let merged = Ident::new("__egglog_merged", proc_macro2::Span::mixed_site());
    for opt in opts {
        match opt {
            Meta::NameValue(x) if x.path.is_ident("name") => {
                let v = x.value;
                nominal = quote!(#v);
            }
            Meta::NameValue(x) if x.path.is_ident("args") => {
                let syn::Expr::Path(path) = &x.value else {
                    return Err(syn::Error::new_spanned(x, "args requires a record name"));
                };
                if path.qself.is_some() {
                    return Err(syn::Error::new_spanned(
                        &x.value,
                        "args requires an unqualified record name",
                    ));
                }
                named_args = Some(path.path.get_ident().cloned().ok_or_else(|| {
                    syn::Error::new_spanned(&x.value, "args requires an unqualified record name")
                })?);
            }
            Meta::NameValue(x) if x.path.is_ident("cost") && kind == "Constructor" => {
                let v = x.value;
                cost = quote!(Some(#v));
            }
            Meta::Path(p) if p.is_ident("unextractable") && kind == "Constructor" => {
                unextractable = true
            }
            Meta::Path(p) if p.is_ident("from") && kind == "Constructor" => {
                from = Some(Vec::new());
            }
            Meta::List(list) if list.path.is_ident("from") && kind == "Constructor" => {
                from = Some(
                    list.parse_args_with(Punctuated::<Type, Token![,]>::parse_terminated)?
                        .into_iter()
                        .collect(),
                );
            }
            Meta::Path(p) if p.is_ident("try_from") && kind == "Constructor" => {
                try_from = Some(Vec::new());
            }
            Meta::List(list) if list.path.is_ident("try_from") && kind == "Constructor" => {
                try_from = Some(
                    list.parse_args_with(Punctuated::<Type, Token![,]>::parse_terminated)?
                        .into_iter()
                        .collect(),
                );
            }
            Meta::Path(p) if p.is_ident("no_merge") && kind == "Function" && !policy => {
                policy = true
            }
            Meta::NameValue(x) if x.path.is_ident("merge") && kind == "Function" && !policy => {
                policy = true;
                let builder = x.value;
                merge = quote!({
                    let #old=<#output as ::egglog_experimental::typed::EgglogValue>::from_expression(::egglog_experimental::typed::__private::Expr::new(<#output as ::egglog_experimental::typed::EgglogValue>::sort_ref(),::egglog_experimental::typed::__private::NodeKind::MergeVariable("old"),#span.clone()));
                    let #new=<#output as ::egglog_experimental::typed::EgglogValue>::from_expression(::egglog_experimental::typed::__private::Expr::new(<#output as ::egglog_experimental::typed::EgglogValue>::sort_ref(),::egglog_experimental::typed::__private::NodeKind::MergeVariable("new"),#span.clone()));
                    let #merged:#output=(#builder)(#old,#new);Some(::egglog_experimental::typed::EgglogValue::expression(&#merged).clone())
                });
            }
            x => {
                return Err(syn::Error::new_spanned(
                    x,
                    "unsupported or duplicate declaration option",
                ));
            }
        }
    }
    if kind == "Function" && !policy {
        return Err(syn::Error::new_spanned(
            &name,
            "functions require no_merge or merge = builder",
        ));
    }
    let mut records = Tokens::new();
    if let Some(record) = named_args {
        if fields.len() > 32 {
            return Err(syn::Error::new_spanned(
                &stub.sig.inputs,
                "named argument records support at most 32 arguments, including the receiver",
            ));
        }
        if receiver
            && record_fields
                .iter()
                .skip(1)
                .any(|field| field == "receiver" || field == "r#receiver")
        {
            return Err(syn::Error::new_spanned(
                &stub.sig.inputs,
                "named argument records reserve `receiver` for the method receiver",
            ));
        }
        let target = match (&context.owner, &context.trait_path) {
            (Some(owner), Some(trait_path)) => quote!(<#owner as #trait_path>::#name),
            (Some(owner), None) => quote!(<#owner>::#name),
            (None, _) => quote!(#name),
        };
        let root = if kind == "Relation" {
            quote!(::egglog_experimental::typed::Relation)
        } else {
            quote!(#output)
        };
        let arguments = (0..fields.len())
            .map(|index| fresh_ident(&format!("__egglog_selected_{index}_"), &authored))
            .collect::<Vec<_>>();
        let probe = arguments.iter().enumerate().map(|(index, argument)| {
            if (context.trait_path.is_some() || (receiver && index == 0)) && !borrowed_inputs[index]
            {
                quote!(::std::clone::Clone::clone(#argument))
            } else {
                quote!(#argument)
            }
        });
        let value = fresh_ident("__egglog_record", &authored);
        let node = fresh_ident("__egglog_node", &authored);
        let scope = fresh_ident("__egglog_scope", &authored);
        let slots = 0..fields.len();
        let construct = record_fields.iter().enumerate().map(|(index, field)| {
            if (context.trait_path.is_some() || (receiver && index == 0)) && borrowed_inputs[index]
            {
                quote!(&#value.#field)
            } else {
                quote!(#value.#field)
            }
        });
        let mut cfg = context.cfg.clone();
        cfg.extend(configuration_attrs(&stub.attrs)?);
        let vis = &stub.vis;
        records = quote! {
            #(#cfg)*
            #[derive(::std::clone::Clone, ::std::fmt::Debug)]
            #vis struct #record { #(pub #record_fields: #types,)* }

            #(#cfg)*
            impl #record {
                /// Create distinct fresh query variables for every argument.
                /// Each invocation is independent; cloning preserves variable identities.
                /// Use struct update to constrain fields or retain matched fields on the RHS.
                /// These are not default values: RHS-only variables remain unbound errors.
                #[track_caller]
                pub fn fresh() -> Self {
                    let #scope = ::egglog_experimental::typed::__private::Identity(
                        ::egglog_experimental::typed::__private::Arc::new(()),
                    );
                    let _ = &#scope;
                    Self {
                        #(#record_fields: ::egglog_experimental::typed::__private::variable::<#types>(
                            ::std::clone::Clone::clone(&#scope), #slots,
                        ),)*
                    }
                }

                /// Inspect this exact call's immediate symbolic arguments.
                /// A different root returns `None`; incompatible declarations are errors.
                /// Frozen constructor fields retain their original snapshot provenance.
                /// Relation records inspect authored calls, not rows in a relation table.
                pub fn get_args(#node: &#root) -> ::std::result::Result<
                    ::std::option::Option<Self>, ::egglog_experimental::typed::TypedError,
                > {
                    let ::std::option::Option::Some((#(#arguments,)*)) =
                        ::egglog_experimental::typed::get_args(
                            #node, |#(#arguments: &#types),*| #target(#(#probe),*),
                        )?
                    else { return ::std::result::Result::Ok(::std::option::Option::None); };
                    ::std::result::Result::Ok(::std::option::Option::Some(Self {
                        #(#record_fields: #arguments,)*
                    }))
                }
            }

            #(#cfg)*
            impl ::std::convert::From<#record> for #root {
                #[track_caller]
                fn from(#value: #record) -> Self { #target(#(#construct),*) }
            }
        };
    }
    let mut conversions = Tokens::new();
    if from.is_some() || try_from.is_some() {
        if receiver || types.len() != 1 {
            let option = if from.is_some() { "from" } else { "try_from" };
            return Err(syn::Error::new_spanned(
                &stub.sig,
                format!("{option} requires a unary constructor without a receiver"),
            ));
        }
        let input = &types[0];
        let target = match (&context.owner, &context.trait_path) {
            (Some(owner), Some(trait_path)) => quote!(<#owner as #trait_path>::#name),
            (Some(owner), None) => quote!(<#owner>::#name),
            (None, _) => quote!(#name),
        };
        let cfg = configuration_attrs(&stub.attrs)?;
        let value = fresh_ident("__egglog_source", &authored);
        let argument = if context.trait_path.is_some() {
            let converted = quote!(::std::convert::Into::<#input>::into(#value));
            if matches!(&stub.sig.inputs[0], FnArg::Typed(arg) if matches!(arg.ty.as_ref(), Type::Reference(_)))
            {
                quote!(&#converted)
            } else {
                converted
            }
        } else {
            quote!(#value)
        };
        if let Some(extra) = from {
            let mut sources: Vec<Type> = vec![input.clone(), syn::parse_quote!(&#input)];
            sources.extend(extra);
            let mut seen = std::collections::HashSet::new();
            for source in sources {
                let source = resolve_type(&source, context, true)?;
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
                conversions.extend(quote! {
                    #(#cfg)*
                    impl ::std::convert::From<#source> for #output {
                        #[track_caller]
                        fn from(#value: #source) -> Self { #target(#argument) }
                    }
                });
            }
        }
        if let Some(extra) = try_from {
            let mut targets = vec![input.clone()];
            targets.extend(extra);
            let mut seen = std::collections::HashSet::new();
            let field = fresh_ident("__egglog_field", &authored);
            let error = fresh_ident("__egglog_error", &authored);
            let argument = if context.trait_path.is_some()
                && matches!(&stub.sig.inputs[0], FnArg::Typed(arg) if !matches!(arg.ty.as_ref(), Type::Reference(_)))
            {
                quote!(::std::clone::Clone::clone(#field))
            } else {
                quote!(#field)
            };
            for (index, destination) in targets.into_iter().enumerate() {
                let destination = resolve_type(&destination, context, true)?;
                let spelling = destination.to_token_stream().to_string();
                if !seen.insert(spelling.clone()) {
                    return Err(syn::Error::new_spanned(
                        destination,
                        "duplicate try_from target type",
                    ));
                }
                if spelling == output.to_token_stream().to_string() {
                    return Err(syn::Error::new_spanned(
                        destination,
                        "try_from cannot replace an identity conversion",
                    ));
                }
                if matches!(destination, Type::Reference(_)) {
                    return Err(syn::Error::new_spanned(
                        destination,
                        "try_from targets must be owned types",
                    ));
                }
                let converted = if index == 0 {
                    quote!(::std::result::Result::Ok(#field))
                } else {
                    quote!(<#destination as ::std::convert::TryFrom<#input>>::try_from(#field)
                        .map_err(|#error| ::egglog_experimental::typed::TypedError::Decode(::std::string::ToString::to_string(&#error))))
                };
                conversions.extend(quote! {
                    #(#cfg)*
                    impl ::std::convert::TryFrom<&#output> for #destination {
                        type Error = ::egglog_experimental::typed::TypedError;
                        fn try_from(#value: &#output) -> ::std::result::Result<Self, Self::Error> {
                            let ::std::option::Option::Some((#field,)) = ::egglog_experimental::typed::get_args(
                                #value, |#field: &#input| #target(#argument),
                            )? else {
                                return ::std::result::Result::Err(::egglog_experimental::typed::TypedError::Decode(
                                    concat!("expected constructor ", stringify!(#target)).into(),
                                ));
                            };
                            #converted
                        }
                    }
                    #(#cfg)*
                    impl ::std::convert::TryFrom<#output> for #destination {
                        type Error = ::egglog_experimental::typed::TypedError;
                        fn try_from(#value: #output) -> ::std::result::Result<Self, Self::Error> {
                            <Self as ::std::convert::TryFrom<&#output>>::try_from(&#value)
                        }
                    }
                });
            }
        }
    }
    let kind = Ident::new(kind, name.span());
    let syntax = context.syntax.clone().unwrap_or_else(|| {
        if receiver {
            quote!(::egglog_experimental::typed::__private::CallSyntax::Method(
                stringify!(#name)
            ))
        } else if let Some(owner) = &context.owner {
            quote!(
                ::egglog_experimental::typed::__private::CallSyntax::Function(concat!(
                    stringify!(#owner),
                    "::",
                    stringify!(#name)
                ))
            )
        } else {
            quote!(::egglog_experimental::typed::__private::CallSyntax::Function(stringify!(#name)))
        }
    });
    let constraint = if kind == "Constructor" {
        quote!(fn assert_equality<S: ::egglog_experimental::typed::EqualitySort>(){} assert_equality::<#output>();)
    } else {
        quote!()
    };
    let args = (0..fields.len())
        .map(|i| {
            Ident::new(
                &format!("__egglog_arg_{i}"),
                proc_macro2::Span::mixed_site(),
            )
        })
        .collect::<Vec<_>>();
    let reference = Ident::new("__egglog_reference", proc_macro2::Span::mixed_site());
    let resolve = Ident::new("__egglog_resolve", proc_macro2::Span::mixed_site());
    let definition = Ident::new("__EGGLOG_DEFINITION", proc_macro2::Span::mixed_site());
    let expr = Ident::new("__egglog_expression", proc_macro2::Span::mixed_site());
    let result = if kind == "Relation" {
        quote!(::egglog_experimental::typed::Relation::from_expression(#expr))
    } else {
        quote!(<#output as ::egglog_experimental::typed::EgglogValue>::from_expression(#expr))
    };
    let Stub { attrs, vis, sig } = stub;
    let metadata = quote! {
            struct #declaration;
            impl #declaration {
            fn #reference()->::egglog_experimental::typed::__private::CallableRef {
                ::egglog_experimental::typed::__private::CallableRef::declared(#nominal,::egglog_experimental::typed::__private::CallKind::#kind,::egglog_experimental::typed::__private::DefinitionSource{token: ::std::any::TypeId::of::<Self>(),resolve:Self::#resolve},Some(#syntax))
            }
            fn #resolve()->&'static ::egglog_experimental::typed::__private::CallableDef {
                static #definition: ::std::sync::OnceLock<::egglog_experimental::typed::__private::CallableDef>=::std::sync::OnceLock::new();
                #definition.get_or_init(|| {
                    #constraint
                    let #span=::egglog_experimental::typed::__private::Span::Rust(::std::sync::Arc::new(::egglog_experimental::typed::__private::RustSpan{file:file!().into(),line:line!(),column:column!()}));let _=&#span;
                    ::egglog_experimental::typed::__private::CallableDef{callable:Self::#reference(),inputs:vec![#(<#types as ::egglog_experimental::typed::EgglogValue>::sort_ref()),*],output:<#output as ::egglog_experimental::typed::EgglogValue>::sort_ref(),merge:#merge,cost:#cost,unextractable:#unextractable}
                })
            }
            }
    };
    let local = if context.shared {
        Tokens::new()
    } else {
        metadata.clone()
    };
    Ok((
        metadata,
        quote! {
            #(#attrs)* #[track_caller] #[allow(non_snake_case)] #vis #sig {
                let (#(#args,)*):(#(#types,)*)=(#(::std::convert::Into::into(#fields),)*);
                let #expr={#local ::egglog_experimental::typed::__private::Expr::call(<#output as ::egglog_experimental::typed::EgglogValue>::sort_ref(),#declaration::#reference(),vec![#(::egglog_experimental::typed::EgglogValue::expression(&#args).clone()),*])};
                #result
            }
        },
        conversions,
        records,
    ))
}
fn expand(args: TokenStream, item: TokenStream, kind: &str) -> TokenStream {
    let stub = parse_macro_input!(item as Stub);
    options(args)
        .and_then(|opts| {
            callable(stub, opts, kind, &Context::default())
                .map(|(_, method, conversions, records)| quote!(#method #conversions #records))
        })
        .unwrap_or_else(syn::Error::into_compile_error)
        .into()
}
/// Declare a constructor, using its module-qualified Rust name by default.
/// Override `name` for an existing native identity; retain `cost` and
/// `unextractable` independently of naming.
/// On a unary constructor without a receiver, `from` derives concrete `From`
/// implementations for its input sort and a borrow of that sort. `from(T, U)`
/// additionally accepts the listed Rust types through the input's existing `Into`
/// conversions. There is no blanket conversion or search for indirect routes.
/// `try_from` generates the reverse `TryFrom` implementations from owned and
/// borrowed result sorts to the input sort. `try_from(T, U)` also converts that
/// field through each listed type's existing `TryFrom<Input>` implementation.
/// Targets must be owned; their conversion errors must implement `Display` and
/// are reported as `TypedError::Decode`. Inspection requires this exact call:
/// it never evaluates an expression or selects a frozen e-class alternative.
/// Both options are independent and can be combined on one constructor.
/// `args = RecordName` additionally generates a named record of owned symbolic
/// arguments, `RecordName::fresh()` for distinct query variables in every field,
/// `RecordName::get_args(&value)` for exact inspection, and
/// `From<RecordName>` for construction. The record has the declaration's
/// visibility and public fields; methods name their receiver field `receiver`.
/// Struct update constrains selected fields or preserves matched ones. Fresh
/// fields are independent variables, not defaults; cloning retains their identity.
/// Records are siblings of the declaration's impl, including trait impls where
/// the record is private. Up to 32 arguments, including the receiver, are supported.
#[proc_macro_attribute]
pub fn constructor(args: TokenStream, item: TokenStream) -> TokenStream {
    expand(args, item, "Constructor")
}
/// Declare a function with an explicit `merge` or `no_merge` policy.
/// Its module-qualified Rust name is the default identity; `name` overrides it.
/// `args = RecordName` provides the same named call arguments as `constructor`.
#[proc_macro_attribute]
pub fn function(args: TokenStream, item: TokenStream) -> TokenStream {
    expand(args, item, "Function")
}
/// Declare a relation, using its module-qualified Rust name unless `name` is set.
/// `args = RecordName` provides named construction and inspection of authored
/// relation calls. It does not inspect rows in a runtime relation table.
#[proc_macro_attribute]
pub fn relation(args: TokenStream, item: TokenStream) -> TokenStream {
    expand(args, item, "Relation")
}

enum Member {
    Declaration(Box<Stub>),
    Other(Box<ImplItem>),
}
struct Declarations {
    attrs: Vec<Attribute>,
    owner: Type,
    trait_path: Option<Path>,
    members: Vec<Member>,
}
impl Parse for Declarations {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let mut attrs = input.call(Attribute::parse_outer)?;
        input.parse::<Token![impl]>()?;
        if input.peek(Token![<]) {
            return Err(input.error("declaration impls must be monomorphic"));
        }
        let first: Type = input.parse()?;
        let (owner, trait_path) = if input.peek(Token![for]) {
            input.parse::<Token![for]>()?;
            let Type::Path(path) = first else {
                return Err(input.error("expected a trait path"));
            };
            (input.parse()?, Some(path.path))
        } else {
            (first, None)
        };
        let body;
        syn::braced!(body in input);
        attrs.extend(
            body.call(Attribute::parse_inner)?
                .into_iter()
                .map(|mut attr| {
                    attr.style = syn::AttrStyle::Outer;
                    attr
                }),
        );
        let mut members = vec![];
        while !body.is_empty() {
            let fork = body.fork();
            let _: Vec<Attribute> = fork.call(Attribute::parse_outer)?;
            let _: Visibility = fork.parse()?;
            if fork.parse::<Signature>().is_ok() && fork.peek(Token![;]) {
                let stub = Stub {
                    attrs: body.call(Attribute::parse_outer)?,
                    vis: body.parse()?,
                    sig: body.parse()?,
                };
                body.parse::<Token![;]>()?;
                members.push(Member::Declaration(Box::new(stub)));
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
type DeclarationOptions = (&'static str, Vec<Meta>);
// A generated conversion has the callable's availability, but not its function-
// specific attributes or lint expectations. Retain conditional cfg recursively.
fn configuration_attrs(attrs: &[Attribute]) -> syn::Result<Vec<Attribute>> {
    fn filter(meta: &Meta) -> syn::Result<Option<Meta>> {
        if meta.path().is_ident("cfg") {
            return Ok(Some(meta.clone()));
        }
        if let Meta::List(list) = meta
            && list.path.is_ident("cfg_attr")
        {
            let args = list.parse_args_with(Punctuated::<Meta, Token![,]>::parse_terminated)?;
            let mut args = args.iter();
            let predicate = args
                .next()
                .ok_or_else(|| syn::Error::new_spanned(list, "cfg_attr requires a predicate"))?;
            let retained = args
                .filter_map(|arg| filter(arg).transpose())
                .collect::<syn::Result<Vec<_>>>()?;
            if !retained.is_empty() {
                let mut list = list.clone();
                list.tokens = quote!(#predicate, #(#retained),*);
                return Ok(Some(Meta::List(list)));
            }
        }
        Ok(None)
    }
    attrs
        .iter()
        .filter_map(|attr| {
            filter(&attr.meta)
                .map(|meta| {
                    meta.map(|meta| {
                        let mut attr = attr.clone();
                        attr.meta = meta;
                        attr
                    })
                })
                .transpose()
        })
        .collect()
}
fn declaration_attrs(
    attrs: Vec<Attribute>,
) -> syn::Result<(Vec<Attribute>, Option<DeclarationOptions>)> {
    let mut retained = vec![];
    let mut declaration = None;
    for attr in attrs {
        let kind = if attr.path().is_ident("constructor") {
            Some("Constructor")
        } else if attr.path().is_ident("function") {
            Some("Function")
        } else if attr.path().is_ident("relation") {
            Some("Relation")
        } else {
            None
        };
        if let Some(kind) = kind {
            if declaration.is_some() {
                return Err(syn::Error::new_spanned(
                    attr,
                    "one callable declaration attribute is allowed per method",
                ));
            }
            let opts = match &attr.meta {
                Meta::Path(_) => vec![],
                Meta::List(_) => unique_options(
                    attr.parse_args_with(Punctuated::<Meta, Token![,]>::parse_terminated)?,
                )?,
                _ => {
                    return Err(syn::Error::new_spanned(
                        attr,
                        "expected declaration options",
                    ));
                }
            };
            declaration = Some((kind, opts));
        } else {
            retained.push(attr);
        }
    }
    Ok((retained, declaration))
}
/// Expand bodyless inherent or trait methods into symbolic Rust calls.
/// A return sort defaults to a constructor; an omitted return type declares a
/// relation and becomes `-> Relation`, including in trait implementations.
/// Functions retain explicit `merge` or `no_merge` attributes. Ordinary method
/// bodies are preserved, without generating symbolic calls or operator variants.
/// Default identities include the owner type and, for trait methods, the
/// authored trait path. Per-method `name` options override those defaults.
#[proc_macro_attribute]
pub fn declarations(args: TokenStream, item: TokenStream) -> TokenStream {
    let authored = item.to_string();
    let item = parse_macro_input!(item as Declarations);
    let result = (|| -> syn::Result<Tokens> {
        if !args.is_empty() {
            return Err(syn::Error::new(
                proc_macro2::Span::call_site(),
                "#[declarations] takes no options",
            ));
        }
        let mut context = Context {
            owner: Some(resolve_type(&item.owner, &Context::default(), false)?),
            trait_path: item.trait_path.clone(),
            cfg: configuration_attrs(&item.attrs)?,
            ..Context::default()
        };
        for member in &item.members {
            if let Member::Other(impl_item) = member
                && let ImplItem::Type(ty) = impl_item.as_ref()
                && ty.ident == "Output"
            {
                let authored = Context {
                    owner: Some(item.owner.clone()),
                    ..context.clone()
                };
                context.output = Some(if matches!(ty.ty, Type::Reference(_)) {
                    ty.ty.clone()
                } else {
                    resolve_type(&ty.ty, &authored, false)?
                });
            }
        }
        let operator = item.trait_path.as_ref().and_then(|path| {
            let s = path.segments.iter().collect::<Vec<_>>();
            if s.len() != 3
                || !matches!(s[0].ident.to_string().as_str(), "std" | "core")
                || s[1].ident != "ops"
            {
                return None;
            }
            Some(match s[2].ident.to_string().as_str() {
                "Add" => ("+", 2, "add"),
                "Sub" => ("-", 2, "sub"),
                "Mul" => ("*", 2, "mul"),
                "Div" => ("/", 2, "div"),
                "Rem" => ("%", 2, "rem"),
                "BitAnd" => ("&", 2, "bitand"),
                "BitOr" => ("|", 2, "bitor"),
                "BitXor" => ("^", 2, "bitxor"),
                "Shl" => ("<<", 2, "shl"),
                "Shr" => (">>", 2, "shr"),
                "Neg" => ("-", 1, "neg"),
                "Not" => ("!", 1, "not"),
                _ => return None,
            })
        });
        if let Some((symbol, arity, canonical_method)) = operator
            && item
                .members
                .iter()
                .any(|member| matches!(member, Member::Declaration(_)))
        {
            if item.members.len() != 2 {
                return Err(syn::Error::new_spanned(
                    &item.owner,
                    "operator declarations require exactly type Output and one bodyless method",
                ));
            }
            let mut method = None;
            for member in item.members {
                if let Member::Declaration(stub) = member {
                    method = Some(stub);
                }
            }
            let mut stub = method
                .ok_or_else(|| syn::Error::new_spanned(&item.owner, "operator method missing"))?;
            let (attrs, decl) = declaration_attrs(stub.attrs)?;
            stub.attrs = attrs;
            let (kind, mut opts) = decl.unwrap_or(("Constructor", vec![]));
            if kind == "Relation" || stub.sig.inputs.len() != arity {
                return Err(syn::Error::new_spanned(
                    &stub.sig,
                    "operator requires symbolic owned output and its standard arity",
                ));
            }
            if !matches!(stub.sig.inputs.first(),Some(FnArg::Receiver(r)) if r.reference.is_none() && r.mutability.is_none() && r.colon_token.is_none())
            {
                return Err(syn::Error::new_spanned(
                    &stub.sig,
                    "standard operator declarations require a self receiver",
                ));
            }
            let lhs = context.owner.clone().unwrap();
            let output = context.output.clone().ok_or_else(|| {
                syn::Error::new_spanned(&stub.sig, "operator requires concrete type Output")
            })?;
            if matches!(output, Type::Reference(_)) {
                return Err(syn::Error::new_spanned(
                    &stub.sig,
                    "symbolic operator Output must be an owned sort wrapper",
                ));
            }
            let rhs = if arity == 2 {
                let FnArg::Typed(arg) = &stub.sig.inputs[1] else {
                    return Err(syn::Error::new_spanned(&stub.sig, "operator rhs missing"));
                };
                Some(resolve_type(&arg.ty, &context, false)?)
            } else {
                None
            };
            let original_trait = item.trait_path.as_ref().unwrap();
            let method_name = &stub.sig.ident;
            context.nominal = Some(quote!(concat!(
                module_path!(),
                "::<",
                stringify!(#lhs),
                " as ",
                stringify!(#original_trait),
                ">::",
                stringify!(#method_name)
            )));
            context.syntax = Some(if arity == 2 {
                quote!(::egglog_experimental::typed::__private::CallSyntax::Binary(#symbol))
            } else {
                quote!(::egglog_experimental::typed::__private::CallSyntax::Unary(#symbol))
            });
            // The named record uses the authored signature once, outside the
            // const containing generated owned/borrowed operator variants.
            let records = if opts.iter().any(|option| option.path().is_ident("args")) {
                callable(
                    Stub {
                        attrs: stub.attrs.clone(),
                        vis: stub.vis.clone(),
                        sig: stub.sig.clone(),
                    },
                    opts.clone(),
                    kind,
                    &context,
                )?
                .3
            } else {
                Tokens::new()
            };
            opts.retain(|option| !option.path().is_ident("args"));
            let attrs = &item.attrs;
            let rhs_parameter = fresh_ident("__EgglogRhs", &authored);
            let witness = if arity == 2 {
                let signature = fresh_ident("__EgglogSignature", &authored);
                let method = Ident::new(canonical_method, stub.sig.ident.span());
                let arguments = &original_trait.segments.last().unwrap().arguments;
                let owner = &item.owner;
                let sig = &stub.sig;
                // A separate private trait checks the authored signature without
                // overlapping the conversion-based std::ops implementations.
                quote! {
                    #(#attrs)* #[allow(dead_code)]
                    trait #signature<#rhs_parameter = Self> {
                        type Output;
                        fn #method(self, rhs: #rhs_parameter) -> Self::Output;
                    }
                    #(#attrs)* #[allow(unused_variables)]
                    impl #signature #arguments for #owner {
                        type Output = #output;
                        #sig { ::core::unreachable!() }
                    }
                }
            } else {
                Tokens::new()
            };
            let mut expanded = vec![];
            let mut metadata = None;
            context.shared = true;
            context.binary_rhs = rhs.clone();
            for borrowed_lhs in [false, true] {
                let self_ty: Type = if borrowed_lhs {
                    syn::parse_quote!(&#lhs)
                } else {
                    lhs.clone()
                };
                let mut trait_path = original_trait.clone();
                let mut sig = stub.sig.clone();
                sig.inputs[0] = syn::parse_quote!(self);
                sig.output = syn::parse_quote!(->#output);
                let generics = if let Some(rhs) = &rhs {
                    trait_path.segments.last_mut().unwrap().arguments =
                        syn::PathArguments::AngleBracketed(syn::parse_quote!(<#rhs_parameter>));
                    let FnArg::Typed(input) = &mut sig.inputs[1] else {
                        unreachable!()
                    };
                    input.ty = Box::new(syn::parse_quote!(#rhs_parameter));
                    quote!(<#rhs_parameter: ::std::convert::Into<#rhs>>)
                } else {
                    Tokens::new()
                };
                // Unary declarations can still retain their exact authored impl.
                if arity == 1 && borrowed_lhs == matches!(&item.owner, Type::Reference(_)) {
                    trait_path = original_trait.clone();
                    sig = stub.sig.clone();
                }
                let mut ctx = context.clone();
                ctx.trait_path = Some(trait_path.clone());
                let (definition, method, _, _) = callable(
                    Stub {
                        attrs: stub.attrs.clone(),
                        vis: stub.vis.clone(),
                        sig,
                    },
                    opts.clone(),
                    kind,
                    &ctx,
                )?;
                if metadata.is_none() {
                    metadata = Some(definition);
                }
                expanded.push(quote!(#(#attrs)* impl #generics #trait_path for #self_ty{type Output=#output;#method}));
            }
            return Ok(quote!(const _: ()={#witness #metadata #(#expanded)*}; #records));
        }
        let mut members = vec![];
        let mut conversions = Tokens::new();
        let mut records = Tokens::new();
        for member in item.members {
            match member {
                Member::Other(item) => {
                    if let ImplItem::Fn(method) = item.as_ref()
                        && declaration_attrs(method.attrs.clone())?.1.is_some()
                    {
                        return Err(syn::Error::new_spanned(
                            &method.sig,
                            "symbolic declarations must be bodyless",
                        ));
                    }
                    members.push(quote!(#item));
                }
                Member::Declaration(mut stub) => {
                    let (attrs, decl) = declaration_attrs(stub.attrs)?;
                    stub.attrs = attrs;
                    let inferred = if matches!(stub.sig.output, ReturnType::Default) {
                        "Relation"
                    } else {
                        "Constructor"
                    };
                    let (kind, opts) = decl.unwrap_or((inferred, vec![]));
                    let (_, method, from, named) = callable(*stub, opts, kind, &context)?;
                    members.push(method);
                    conversions.extend(from);
                    records.extend(named);
                }
            }
        }
        let Declarations {
            attrs,
            owner,
            trait_path,
            ..
        } = item;
        let header = trait_path.map(|t| quote!(#t for));
        if !conversions.is_empty() {
            let cfg = configuration_attrs(&attrs)?;
            conversions = quote!(#(#cfg)* const _: () = {#conversions};);
        }
        Ok(quote!(#(#attrs)* impl #header #owner{#(#members)*} #conversions #records))
    })();
    result.unwrap_or_else(syn::Error::into_compile_error).into()
}
