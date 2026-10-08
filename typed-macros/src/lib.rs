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
    members: Vec<Member>,
}
impl Parse for Declarations {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        input.parse::<Token![impl]>()?;
        if input.peek(Token![<]) {
            return Err(input.error("declaration impls must be monomorphic"));
        }
        let owner = input.parse()?;
        if input.peek(Token![for]) {
            return Err(
                input.error("trait declarations are not supported in the initial typed subset")
            );
        }
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
            members,
        })
    }
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

fn callable(
    mut stub: Stub,
    opts: Vec<Meta>,
    owner: Option<&Type>,
) -> syn::Result<(Tokens, Tokens)> {
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
            "constructors require monomorphic safe ordinary signatures",
        ));
    }
    if stub.sig.inputs.len() > 4 {
        return Err(syn::Error::new_spanned(
            &stub.sig.inputs,
            "the first typed subset supports at most four arguments",
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
    let mut from = false;
    let mut try_from = false;
    let mut args_record = None;
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
            Meta::Path(p) if p.is_ident("from") => from = true,
            Meta::Path(p) if p.is_ident("try_from") => try_from = true,
            other => {
                return Err(syn::Error::new_spanned(
                    other,
                    "unsupported constructor option in the initial typed subset",
                ));
            }
        }
    }
    let mut names = vec![];
    let mut types = vec![];
    for input in &mut stub.sig.inputs {
        let FnArg::Typed(arg) = input else {
            return Err(syn::Error::new_spanned(
                input,
                "receivers await the next declaration slice",
            ));
        };
        let Pat::Ident(pat) = arg.pat.as_ref() else {
            return Err(syn::Error::new_spanned(
                &arg.pat,
                "constructor arguments must be plain identifiers",
            ));
        };
        if pat.by_ref.is_some() || pat.subpat.is_some() {
            return Err(syn::Error::new_spanned(
                pat,
                "constructor arguments must be plain identifiers",
            ));
        }
        let ty = resolve_type(&arg.ty, owner)?;
        names.push(pat.ident.clone());
        types.push(ty.clone());
        arg.ty = Box::new(syn::parse_quote!(impl Into<#ty>));
    }
    let ReturnType::Type(_, output) = &stub.sig.output else {
        return Err(syn::Error::new_spanned(
            &stub.sig,
            "a constructor output sort is required",
        ));
    };
    let output = resolve_type(output, owner)?;
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
    let mut fresh = |base: &str| {
        let mut spelling = base.to_owned();
        let mut suffix = 0;
        while !occupied.insert(spelling.clone()) {
            suffix += 1;
            spelling = format!("{base}_{suffix}");
        }
        Ident::new(&spelling, proc_macro2::Span::mixed_site())
    };
    let definition_static = fresh("__EGGLOG_DEFINITION");
    let definition = fresh("__egglog_definition");
    let value = fresh("__egglog_value");
    let field = fresh("__egglog_field");
    let scope = fresh("__egglog_scope");
    let mut extra = Tokens::new();
    let cfg: Vec<_> = stub
        .attrs
        .iter()
        .filter(|a| a.path().is_ident("cfg"))
        .collect();
    if from || try_from {
        if types.len() != 1
            || types[0].to_token_stream().to_string() == output.to_token_stream().to_string()
        {
            return Err(syn::Error::new_spanned(
                &stub.sig,
                "from/try_from require a unary constructor with a different input sort",
            ));
        }
        let input = &types[0];
        if from {
            extra.extend(quote! {
                #(#cfg)* impl From<#input> for #output { fn from(#value: #input) -> Self { #target(#value) } }
                #(#cfg)* impl From<&#input> for #output { fn from(#value: &#input) -> Self { #target(#value) } }
            });
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
    let method = quote! {
        #(#attrs)* #[allow(non_snake_case)] #vis #sig {
            static #definition_static: ::std::sync::OnceLock<::egglog_experimental::typed::__private::Callable> = ::std::sync::OnceLock::new();
            let #definition = #definition_static.get_or_init(|| ::egglog_experimental::typed::__private::Callable::constructor(
                #nominal, vec![#(<#types as ::egglog_experimental::typed::EgglogValue>::sort_ref()),*],
                <#output as ::egglog_experimental::typed::EgglogValue>::sort_ref(),
            ));
            let (#(#hidden,)*): (#(#types,)*) = (#(::std::convert::Into::into(#names),)*);
            <#output as ::egglog_experimental::typed::EgglogValue>::from_expression(
                ::egglog_experimental::typed::__private::Expr::call(#definition, vec![#(::egglog_experimental::typed::EgglogValue::expression(&#hidden).clone()),*]),
            )
        }
    };
    Ok((method, extra))
}

#[proc_macro_attribute]
pub fn constructor(args: TokenStream, item: TokenStream) -> TokenStream {
    let stub = parse_macro_input!(item as Stub);
    options(args.into())
        .and_then(|opts| callable(stub, opts, None))
        .map(|(method, extra)| quote!(#method #extra))
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
        let mut members = Tokens::new();
        let mut extra = Tokens::new();
        for member in item.members {
            match member {
                Member::Other(item) => members.extend(quote!(#item)),
                Member::Declaration(stub) => {
                    let mut stub = *stub;
                    let mut opts = vec![];
                    let mut retained = vec![];
                    let mut seen = false;
                    for attr in stub.attrs {
                        if attr.path().is_ident("constructor") {
                            if seen {
                                return Err(syn::Error::new_spanned(
                                    attr,
                                    "duplicate constructor attribute",
                                ));
                            }
                            seen = true;
                            opts = match &attr.meta {
                                Meta::Path(_) => vec![],
                                Meta::List(l) => options(l.tokens.clone())?,
                                _ => {
                                    return Err(syn::Error::new_spanned(
                                        attr,
                                        "invalid constructor attribute",
                                    ));
                                }
                            };
                        } else {
                            retained.push(attr);
                        }
                    }
                    stub.attrs = retained;
                    let (method, generated) = callable(stub, opts, Some(&item.owner))?;
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
