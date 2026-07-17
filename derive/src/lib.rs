//! `#[derive(Recursive)]`, borrowed edition.
//!
//! * The generated `fold` takes `&self`: the tree survives, payloads reach
//!   the algebra as `&'a P` — **no `Clone`, no `Comonoid`, no bounds**.
//!   Duplication is the algebra's decision at the leaf, paid only if it
//!   keeps a payload.
//! * A hole is ANY single-argument wrapper chain terminating in `Self`,
//!   resolved through `affine_cat::cata::Holes` — a custom owning
//!   pointer with a `Holes` impl works as a plain field, no attribute.
//!   The `{Box, Vec, Option, Thunk}` list gates the CONSUMING face
//!   only: other wrappers (`Rc`, `Arc`, custom pointers) fold
//!   borrowed-face-only, and consuming machinery for them waits for the
//!   `#[recursive(movable)]` escape hatch — the SYMPTOM of that gate is
//!   `E0599: no method named \`into_fold\` found`: the consuming driver
//!   was not generated, which is the gate working, not a bug.
//!   `#[recursive(hole)]` covers
//!   OPAQUE field types with no syntactic `Self` (handles, newtyped
//!   ids); a shared-arena HANDLE additionally does not fit `Holes` at
//!   all — see that trait's owning-vs-denoting note; hand-write
//!   `Recursive` (`examples/arena.rs` is the worked witness).
//!   If a wrapper lacks the needed impl, the error names the trait.
//! * The wrapper-chain classifier is itself a fold over `syn::Type` using
//!   [`affine_cat::cata::Recursor`] (the Mendler face on a foreign AST —
//!   the crate folds its own dogfood; `affine-cat` is a real dependency
//!   of this proc-macro, so the link resolves).
use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::{parse_macro_input, parse_quote, Data, DeriveInput, Fields, Type};

use affine_cat::cata::{run, Recursor};

enum Shape {
    /// wrapper chain, outermost first: (container type, element type)
    Chain(Vec<(Type, Type)>),
    Bare, // literal Self: illegal in an enum field, reported
    Payload,
}

struct Classify<'a> {
    me: &'a syn::Ident,
}
impl Recursor<Type, ()> for Classify<'_> {
    type Out = Shape;
    fn step(
        &self,
        env: &mut (),
        node: &Type,
        rec: &mut dyn FnMut(&mut (), &Type) -> Shape,
    ) -> Shape {
        match node {
            Type::Path(tp) => {
                if tp.qself.is_none()
                    && tp.path.segments.len() == 1
                    && tp.path.segments[0].ident == *self.me
                {
                    return Shape::Bare;
                }
                let Some(seg) = tp.path.segments.last() else {
                    return Shape::Payload;
                };
                let syn::PathArguments::AngleBracketed(args) = &seg.arguments else {
                    return Shape::Payload;
                };
                let mut inner_tys = args.args.iter().filter_map(|a| match a {
                    syn::GenericArgument::Type(t) => Some(t),
                    _ => None,
                });
                let (Some(inner), None) = (inner_tys.next(), inner_tys.next()) else {
                    return Shape::Payload;
                };
                match rec(env, inner) {
                    Shape::Bare => Shape::Chain(vec![(node.clone(), inner.clone())]),
                    Shape::Chain(mut c) => {
                        c.insert(0, (node.clone(), inner.clone()));
                        Shape::Chain(c)
                    }
                    Shape::Payload => Shape::Payload,
                }
            }
            Type::Paren(p) => rec(env, &p.elem),
            Type::Group(g) => rec(env, &g.elem),
            _ => Shape::Payload,
        }
    }
}

/// hole layer type: nested `<W as Holes<E>>::Mapped<..>` projections
fn mapped_ty(chain: &[(Type, Type)]) -> proc_macro2::TokenStream {
    match chain {
        [] => quote!(T),
        [(w, e), rest @ ..] => {
            let inner = mapped_ty(rest);
            quote!(<#w as ::affine_cat::cata::Hole<#e>>::Mapped<#inner>)
        }
    }
}

/// fold code: nested try_map_ref, innermost recursing + absorption check
fn map_expr(chain: &[(Type, Type)], recv: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    match chain {
        [] => quote! {
            match self_fold(alg, env, #recv) {
                ::core::ops::ControlFlow::Break(__x) => ::core::ops::ControlFlow::Break(__x),
                ::core::ops::ControlFlow::Continue(__v) => {
                    if alg.absorbing(&__v) {
                        ::core::ops::ControlFlow::Break(__v)
                    } else {
                        ::core::ops::ControlFlow::Continue(__v)
                    }
                }
            }
        },
        [(w, e), rest @ ..] => {
            let inner = map_expr(rest, quote!(__c));
            quote!(<#w as ::affine_cat::cata::Holes<#e>>::try_map_ref(#recv, &mut |__c| #inner))
        }
    }
}

/// unzip code: nested unzip_with, innermost splitter = identity on the pair
fn unzip_expr(chain: &[(Type, Type)], recv: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    match chain {
        [] => quote!(#recv),
        [(w, e), rest @ ..] => {
            let inner = unzip_expr(rest, quote!(__p));
            quote!(<#w as ::affine_cat::cata::Hole<#e>>::unzip_with(#recv, &mut |__p| #inner))
        }
    }
}

/// consuming fold code with absorption: nested try_map_move
fn try_move_expr(
    chain: &[(Type, Type)],
    recv: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    match chain {
        [] => quote! {
            match self_fold(alg, env, #recv) {
                ::core::ops::ControlFlow::Break(__x) => ::core::ops::ControlFlow::Break(__x),
                ::core::ops::ControlFlow::Continue(__v) => {
                    if alg.absorbing(&__v) {
                        ::core::ops::ControlFlow::Break(__v)
                    } else {
                        ::core::ops::ControlFlow::Continue(__v)
                    }
                }
            }
        },
        [(w, e), rest @ ..] => {
            let inner = try_move_expr(rest, quote!(__c));
            quote!(<#w as ::affine_cat::cata::HolesMove<#e>>::try_map_move(#recv, &mut |__c| #inner))
        }
    }
}

/// embed code: rebuild the original field type from Mapped<Self>,
/// wrapping at collapsing levels, mapping through Vec/Option shapes
fn wrap_expr(chain: &[(Type, Type)], recv: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    match chain {
        [] => recv,
        [(w, e), rest @ ..] => {
            let ident = if let Type::Path(tp) = w {
                tp.path.segments.last().map(|s| s.ident.to_string())
            } else {
                None
            };
            match ident.as_deref() {
                Some("Vec") => {
                    let inner = wrap_expr(rest, quote!(__x));
                    quote!(<#w as ::affine_cat::cata::HolesWrap<#e>>::wrap(
                        #recv.into_iter().map(|__x| #inner).collect()))
                }
                Some("Option") => {
                    let inner = wrap_expr(rest, quote!(__x));
                    quote!(<#w as ::affine_cat::cata::HolesWrap<#e>>::wrap(
                        #recv.map(|__x| #inner)))
                }
                _ => {
                    // collapsing (Box/Thunk/custom): Mapped is the inner Mapped
                    let inner = wrap_expr(rest, recv);
                    quote!(<#w as ::affine_cat::cata::HolesWrap<#e>>::wrap(#inner))
                }
            }
        }
    }
}

/// scoped fold code: nested try_map_ref, recursion reborrows &mut env
fn try_map_scoped(
    chain: &[(Type, Type)],
    recv: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    match chain {
        [] => quote! {
            match self_fold(alg, &mut *env, #recv) {
                ::core::ops::ControlFlow::Break(__x) => ::core::ops::ControlFlow::Break(__x),
                ::core::ops::ControlFlow::Continue(__v) => {
                    if alg.absorbing(&__v) {
                        ::core::ops::ControlFlow::Break(__v)
                    } else {
                        ::core::ops::ControlFlow::Continue(__v)
                    }
                }
            }
        },
        [(w, e), rest @ ..] => {
            let inner = try_map_scoped(rest, quote!(__c));
            quote!(<#w as ::affine_cat::cata::Holes<#e>>::try_map_ref(#recv, &mut |__c| #inner))
        }
    }
}

#[proc_macro_derive(Recursive, attributes(recursive))]
pub fn derive_recursive(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);
    let name = &ast.ident;
    let vis = &ast.vis;
    if ast.generics.lifetimes().next().is_some() {
        return syn::Error::new_spanned(
            &ast.generics,
            "lifetime-generic enums unsupported: the biased split's \
             continuation requires 'static (a bounded-HRTB language gap; \
             see the walls)",
        )
        .to_compile_error()
        .into();
    }
    if ast.generics.const_params().next().is_some() {
        return syn::Error::new_spanned(&ast.generics, "const generics unsupported (v1)")
            .to_compile_error()
            .into();
    }
    let (impl_g, ty_g, where_c) = ast.generics.split_for_impl();
    let ep: Vec<_> = ast
        .generics
        .type_params()
        .map(|p| p.ident.clone())
        .collect();
    let epb: Vec<_> = ast.generics.type_params().cloned().collect(); // with bounds
    // inner fns: bare params, ALL bounds in where — one location per param
    let ep_bounds: Vec<_> = ast
        .generics
        .type_params()
        .filter(|p| !p.bounds.is_empty())
        .map(|p| {
            let (id, b) = (&p.ident, &p.bounds);
            quote!(#id: #b,)
        })
        .collect();
    let impl_g_env = quote!(<#(#ep,)* Env, Alg>);
    // the biased split's HRTB needs every enum param 'static (the same
    // bounded-HRTB wall, now visible through generics) — stated at the
    // RecursiveOwned impl, where where-clauses may exceed the trait's
    let owned_where = {
        let user = ast.generics.where_clause.as_ref().map(|w| {
            let p = &w.predicates;
            quote!(#p,)
        });
        if ep.is_empty() && user.is_none() {
            quote!()
        } else {
            quote!(where #user #(#ep: 'static,)*)
        }
    };
    let layer_decl = |hp: bool| {
        if hp {
            quote!(<'a, #(#epb,)* T>)
        } else {
            quote!(<#(#epb,)* T>)
        }
    };
    let impl_g_env_scoped = quote!(<#(#ep,)* Env, Alg>);
    let inner_where = match &ast.generics.where_clause {
        Some(w) => {
            let preds = &w.predicates;
            quote!(#preds, #(#ep_bounds)*)
        }
        None => quote!(#(#ep_bounds)*),
    };
    let inner_where_owned = quote!(#inner_where #(#ep: 'static,)*);
    // GAT sharp edge: `Self: 'a` does not decompose for impl-assoc WF;
    // the outlives must be written (and is then accepted as implied)
    let gat_where = if ep.is_empty() {
        quote!()
    } else {
        quote!(where #(#ep: 'a,)*)
    };
    let layer = format_ident!("{}Layer", name);
    let owned = format_ident!("{}LayerOwned", name);
    let Data::Enum(en) = &ast.data else {
        return syn::Error::new_spanned(&ast, "derive(Recursive): enums only")
            .to_compile_error()
            .into();
    };
    let classify = Classify { me: name };

    let mut layer_variants = Vec::new();
    let mut owned_variants = Vec::new();
    let mut unzip_arms = Vec::new();
    let mut fold_arms = Vec::new();
    let mut scoped_arms = Vec::new();
    let mut into_arms = Vec::new();
    let mut embed_arms = Vec::new();
    let mut split_arms = Vec::new();
    let mut hole_count = 0usize;
    // v1 gate: consuming machinery only when every wrapper is known-movable.
    // (Shared/memoized containers rightly lack HolesMove; unknown custom
    // containers wait for the #[recursive(movable)] escape hatch.)
    let mut movable = true;
    // borrowed `fold` is generated only when no chain contains a Thunk:
    // Thunk grants no borrowed forcing (the husk sacrifice) — codata IRs
    // are consuming-only.
    let mut borrowable = true;
    let mut has_payload = false;
    let mut any_scoped = false;
    let mut positivity_suspects: Vec<proc_macro2::Span> = Vec::new();

    for v in &en.variants {
        let vname = &v.ident;
        let (fields_vec, braces): (Vec<&syn::Field>, bool) = match &v.fields {
            Fields::Unnamed(f) => (f.unnamed.iter().collect(), false),
            Fields::Named(f) => (f.named.iter().collect(), true),
            Fields::Unit => {
                layer_variants.push(quote! { #vname });
                owned_variants.push(quote! { #vname });
                unzip_arms.push(quote! { #layer::#vname => (#layer::#vname, #layer::#vname) });
                fold_arms.push(quote! {
                    #name::#vname => ::core::ops::ControlFlow::Continue(
                        alg.reduce(env, #layer::#vname))
                });
                scoped_arms.push(quote! {
                    #name::#vname => ::core::ops::ControlFlow::Continue(
                        alg.reduce(&*env, #layer::#vname))
                });
                into_arms.push(quote! {
                    #name::#vname => ::core::ops::ControlFlow::Continue(
                        alg.reduce(env, #owned::#vname))
                });
                embed_arms.push(quote! { #owned::#vname => #name::#vname });
                split_arms.push(quote! {
                    #owned::#vname => {
                        let __o = k(#layer::#vname);
                        (#owned::#vname, __o)
                    }
                });
                continue;
            }
        };

        // field-level escape hatches: #[recursive(hole)] forces a depth-1
        // hole whose container is the LITERAL field type — the generated
        // `<FieldTy as Hole<Enum>>::…` paths let rustc resolve aliases the
        // token-level classifier cannot see. #[recursive(payload)] forces
        // payload (e.g. quoted/unevaluated subtrees that are data, not
        // structure).
        let mut forced_err = None;
        let info: Vec<(Shape, &Type)> = fields_vec
            .iter()
            .map(|f| {
                let mut forced: Option<&str> = None;
                let mut via: Option<Type> = None;
                for a in &f.attrs {
                    if a.path().is_ident("recursive") {
                        if let Ok(id) = a.parse_args::<syn::Ident>() {
                            match id {
                                i if i == "hole" => forced = Some("hole"),
                                i if i == "payload" => forced = Some("payload"),
                                i if i == "scope" => {}
                                _ => {
                                    forced_err = Some(syn::Error::new_spanned(
                                        a,
                                        "expected #[recursive(hole|payload|scope|hole = \"Type\")]",
                                    ));
                                }
                            }
                        } else if let Ok(nv) = a.parse_args::<syn::MetaNameValue>() {
                            // #[recursive(hole = "Vec<Box<Expr>>")] — claim a
                            // de-aliased type; nominal equality makes the
                            // generated trait paths line up with the real field
                            if nv.path.is_ident("hole") {
                                if let syn::Expr::Lit(syn::ExprLit {
                                    lit: syn::Lit::Str(s),
                                    ..
                                }) = &nv.value
                                {
                                    match syn::parse_str::<Type>(&s.value()) {
                                        Ok(t) => via = Some(t),
                                        Err(_) => {
                                            forced_err = Some(syn::Error::new_spanned(
                                                a,
                                                "hole = \"…\": not a parseable type",
                                            ));
                                        }
                                    }
                                }
                            }
                        } else {
                            forced_err = Some(syn::Error::new_spanned(
                                a,
                                "expected #[recursive(hole|payload|scope|hole = \"Type\")]",
                            ));
                        }
                    }
                }
                let shape = if let Some(claimed) = via {
                    match run(&classify, &mut (), &claimed) {
                        Shape::Chain(c) => Shape::Chain(c),
                        _ => {
                            forced_err = Some(syn::Error::new_spanned(
                                &f.ty,
                                "hole = \"…\": claimed type is not a hole chain",
                            ));
                            Shape::Payload
                        }
                    }
                } else {
                    match forced {
                        Some("hole") => {
                            let me: Type = parse_quote!(#name #ty_g);
                            Shape::Chain(vec![(f.ty.clone(), me)])
                        }
                        Some("payload") => Shape::Payload,
                        _ => run(&classify, &mut (), &f.ty),
                    }
                };
                if matches!(shape, Shape::Payload) {
                    let tyt = {
                        let t = &f.ty;
                        quote!(#t).to_string()
                    };
                    if tyt.contains("dyn") && tyt.contains(&name.to_string()) {
                        positivity_suspects.push(syn::spanned::Spanned::span(&f.ty));
                    }
                }
                (shape, &f.ty)
            })
            .collect();
        if let Some(e) = forced_err {
            return e.to_compile_error().into();
        }
        // §2 (sqlfront report): only PLAIN-forced holes bypass the
        // whitelist — and they bypass it CONSERVATIVELY. An opted-in hole
        // has an unknown container, and the stated policy (consuming only
        // when known-movable) applies to it most of all: shared handles
        // (arena indices, Arc) must not be forced to supply `HolesMove`.
        // Via-form and scoped fields have real container chains; the
        // whitelist judges those like any other field (fixes the latent
        // scope-skip in the same stroke).
        let plain_forced: Vec<bool> = fields_vec
            .iter()
            .map(|f| {
                f.attrs.iter().any(|a| {
                    a.path().is_ident("recursive")
                        && a.parse_args::<syn::Ident>().is_ok_and(|i| i == "hole")
                })
            })
            .collect();
        let scoped_fields: Vec<bool> = fields_vec
            .iter()
            .map(|f| {
                f.attrs.iter().any(|a| {
                    a.path().is_ident("recursive")
                        && a.parse_args::<syn::Ident>()
                            .map(|i| i == "scope")
                            .unwrap_or(false)
                })
            })
            .collect();
        if scoped_fields.iter().any(|&s| s) {
            any_scoped = true;
        }
        if let Some((_, ty)) = info.iter().find(|(s, _)| matches!(s, Shape::Bare)) {
            return syn::Error::new_spanned(
                ty,
                "derive(Recursive): a recursive field must sit behind a pointer \
                 or container implementing affine_cat::cata::Holes",
            )
            .to_compile_error()
            .into();
        }
        hole_count += info
            .iter()
            .filter(|(s, _)| matches!(s, Shape::Chain(_)))
            .count();
        for (i, (s, _)) in info.iter().enumerate() {
            if plain_forced.get(i).copied().unwrap_or(false) {
                movable = false; // unknown container: borrowed face only
                continue;
            }
            if let Shape::Chain(c) = s {
                for (w, _) in c {
                    let known = if let Type::Path(tp) = w {
                        tp.path.segments.last().is_some_and(|seg| {
                            seg.ident == "Box"
                                || seg.ident == "Vec"
                                || seg.ident == "Option"
                                || seg.ident == "Thunk"
                        })
                    } else {
                        false
                    };
                    if !known {
                        movable = false;
                    }
                    if let Type::Path(tp) = w {
                        if tp
                            .path
                            .segments
                            .last()
                            .is_some_and(|s| s.ident == "Thunk")
                        {
                            borrowable = false;
                        }
                    }
                }
            }
        }

        // layer variant: holes as Mapped projections, payloads borrowed
        let binds: Vec<syn::Ident> = fields_vec
            .iter()
            .enumerate()
            .map(|(i, f)| f.ident.clone().unwrap_or_else(|| format_ident!("f{}", i)))
            .collect();
        // syntax helpers: shorthand `{ a, b }` works for both matching and
        // same-name construction; explicit `{ a: e }` only for renames
        let pat = |xs: &[syn::Ident]| -> proc_macro2::TokenStream {
            if braces {
                quote! { { #(#xs),* } }
            } else {
                quote! { ( #(#xs),* ) }
            }
        };
        let ctor_with = |names: &[syn::Ident], es: &[proc_macro2::TokenStream]| {
            if braces {
                quote! { { #(#names: #es),* } }
            } else {
                quote! { ( #(#es),* ) }
            }
        };
        let pb = pat(&binds);

        let tys: Vec<_> = info
            .iter()
            .map(|(s, ty)| match s {
                Shape::Chain(c) => mapped_ty(c),
                _ => {
                    has_payload = true;
                    quote!(&'a #ty)
                }
            })
            .collect();
        let lv = ctor_with(&binds, &tys);
        layer_variants.push(quote! { #vname #lv });
        // owned layer variant: same holes, payloads by value
        let otys: Vec<_> = info
            .iter()
            .map(|(s, ty)| match s {
                Shape::Chain(c) => mapped_ty(c),
                _ => quote!(#ty),
            })
            .collect();
        let ov = ctor_with(&binds, &otys);
        owned_variants.push(quote! { #vname #ov });

        // unzip: holes via unzip_with chains; borrowed payloads copy free
        let dup_stmts = info.iter().enumerate().map(|(i, (s, _))| {
            let f = &binds[i];
            let (fa, fb) = (format_ident!("{}a", f), format_ident!("{}b", f));
            match s {
                Shape::Chain(c) => {
                    let e = unzip_expr(c, quote!(#f));
                    quote! { let (#fa, #fb) = #e; }
                }
                _ => quote! { let (#fa, #fb) = (#f, #f); },
            }
        });
        let las: Vec<_> = binds.iter().map(|f| format_ident!("{}a", f)).collect();
        let lbs: Vec<_> = binds.iter().map(|f| format_ident!("{}b", f)).collect();
        let las_ts: Vec<_> = las.iter().map(|x| quote!(#x)).collect();
        let lbs_ts: Vec<_> = lbs.iter().map(|x| quote!(#x)).collect();
        let (ca, cb) = (ctor_with(&binds, &las_ts), ctor_with(&binds, &lbs_ts));
        unzip_arms.push(quote! {
            #layer::#vname #pb => {
                #(#dup_stmts)*
                (#layer::#vname #ca, #layer::#vname #cb)
            }
        });

        // fold: borrowed match; holes via map_ref chains; payloads pass as refs
        let steps = info.iter().enumerate().map(|(i, (s, _))| {
            let f = &binds[i];
            match s {
                Shape::Chain(c) => {
                    let e = map_expr(c, quote!(#f));
                    quote! {
                        let #f = match #e {
                            ::core::ops::ControlFlow::Continue(__m) => __m,
                            ::core::ops::ControlFlow::Break(__x) => {
                                return ::core::ops::ControlFlow::Break(__x)
                            }
                        };
                    }
                }
                _ => quote! {},
            }
        });
        fold_arms.push(quote! {
            #name::#vname #pb => {
                #(#steps)*
                ::core::ops::ControlFlow::Continue(alg.reduce(env, #layer::#vname #pb))
            }
        });
        // scoped arms: env is &mut; #[recursive(scope)] holes bracketed by
        // a Drop guard (restore on normal exit, Break, and panic alike)
        let ssteps = info.iter().enumerate().map(|(i, (s, _))| {
            let f = &binds[i];
            match s {
                Shape::Chain(c) => {
                    let e = try_map_scoped(c, quote!(#f));
                    if scoped_fields.get(i).copied().unwrap_or(false) {
                        quote! {
                            let #f = {
                                let mut __g = ::affine_cat::cata::ScopeGuard::new(&mut *env);
                                let env = __g.env();
                                match #e {
                                    ::core::ops::ControlFlow::Continue(__m) => __m,
                                    ::core::ops::ControlFlow::Break(__x) => {
                                        return ::core::ops::ControlFlow::Break(__x)
                                    }
                                }
                            };
                        }
                    } else {
                        quote! {
                            let #f = match #e {
                                ::core::ops::ControlFlow::Continue(__m) => __m,
                                ::core::ops::ControlFlow::Break(__x) => {
                                    return ::core::ops::ControlFlow::Break(__x)
                                }
                            };
                        }
                    }
                }
                _ => quote! {},
            }
        });
        scoped_arms.push(quote! {
            #name::#vname #pb => {
                #(#ssteps)*
                ::core::ops::ControlFlow::Continue(alg.reduce(&*env, #layer::#vname #pb))
            }
        });
        // consuming arms: holes via try_map_move chains, payloads moved,
        // absorption bubbles (remaining thunks drop unforced)
        let msteps = info.iter().enumerate().map(|(i, (s, _))| {
            let f = &binds[i];
            match s {
                Shape::Chain(c) => {
                    let e = try_move_expr(c, quote!(#f));
                    quote! {
                        let #f = match #e {
                            ::core::ops::ControlFlow::Continue(__m) => __m,
                            ::core::ops::ControlFlow::Break(__x) => {
                                return ::core::ops::ControlFlow::Break(__x)
                            }
                        };
                    }
                }
                _ => quote! {},
            }
        });
        into_arms.push(quote! {
            #name::#vname #pb => {
                #(#msteps)*
                ::core::ops::ControlFlow::Continue(alg.reduce(env, #owned::#vname #pb))
            }
        });
        let cons: Vec<_> = info
            .iter()
            .enumerate()
            .map(|(i, (s, _))| {
                let f = &binds[i];
                match s {
                    Shape::Chain(c) => wrap_expr(c, quote!(#f)),
                    _ => quote!(#f),
                }
            })
            .collect();
        let cc = ctor_with(&binds, &cons);
        embed_arms.push(quote! {
            #owned::#vname #pb => #name::#vname #cc
        });
        // split_with arm: unzip children pairs (free), lend payload refs to
        // k with the B-children, then rebuild the owned A-layer by move.
        let split_stmts = info.iter().enumerate().map(|(i, (s, _))| {
            let f = &binds[i];
            let (fa, fb) = (format_ident!("{}a", f), format_ident!("{}b", f));
            match s {
                Shape::Chain(c) => {
                    let e = unzip_expr(c, quote!(#f));
                    quote! { let (#fa, #fb) = #e; }
                }
                _ => quote! {},
            }
        });
        let borrowed_view: Vec<_> = info
            .iter()
            .enumerate()
            .map(|(i, (s, _))| {
                let f = &binds[i];
                let fb = format_ident!("{}b", f);
                match s {
                    Shape::Chain(_) => quote!(#fb),
                    _ => quote!(&#f),
                }
            })
            .collect();
        let owned_rebuild: Vec<_> = info
            .iter()
            .enumerate()
            .map(|(i, (s, _))| {
                let f = &binds[i];
                let fa = format_ident!("{}a", f);
                match s {
                    Shape::Chain(_) => quote!(#fa),
                    _ => quote!(#f),
                }
            })
            .collect();
        let (bv, orb) = (
            ctor_with(&binds, &borrowed_view),
            ctor_with(&binds, &owned_rebuild),
        );
        split_arms.push(quote! {
            #owned::#vname #pb => {
                #(#split_stmts)*
                let __o = k(#layer::#vname #bv);
                (#owned::#vname #orb, __o)
            }
        });
    }

    if hole_count == 0 {
        return syn::Error::new_spanned(
            &ast.ident,
            "derive(Recursive): no recursive positions found \
             (expected a field like Box<Self>, Vec<Self>, or W<Self> with W: Holes)",
        )
        .to_compile_error()
        .into();
    }

    let layer_decl_toks = layer_decl(has_payload);
    // borrowed layers hold `&'a P`: every enum type param must outlive 'a
    let layer_where = {
        let user = ast.generics.where_clause.as_ref().map(|w| {
            let p = &w.predicates;
            quote!(#p,)
        });
        if has_payload && !ep.is_empty() {
            quote!(where #user #(#ep: 'a,)*)
        } else if user.is_some() {
            quote!(where #user)
        } else {
            quote!()
        }
    };
    let (_layer_generics, layer_args, layer_ab, layer_a, layer_b, layer_bx) = if has_payload {
        (
            quote!(<'a, #(#ep,)* T>),
            quote!(<'a, #(#ep,)* T>),
            quote!(<'a, #(#ep,)* (A, B)>),
            quote!(<'a, #(#ep,)* A>),
            quote!(<'a, #(#ep,)* B>),
            quote!(<'x, #(#ep,)* B>),
        )
    } else {
        (
            quote!(<#(#ep,)* T>),
            quote!(<#(#ep,)* T>),
            quote!(<#(#ep,)* (A, B)>),
            quote!(<#(#ep,)* A>),
            quote!(<#(#ep,)* B>),
            quote!(<#(#ep,)* B>),
        )
    };
    // positivity lint: stable proc macros cannot emit warnings; a call to
    // a deprecated shim is the one channel that reaches the user
    let positivity = if positivity_suspects.is_empty() {
        quote! {}
    } else {
        // user-code spans dodge external-macro lint suppression AND point
        // the warning at the suspect field itself
        let triggers = positivity_suspects.iter().map(|sp| {
            quote::quote_spanned! {*sp=>
                __affine_cat_positivity_suspect();
            }
        });
        quote! {
            #[deprecated(note = "affine-cat: payload mentions `dyn ... Self ...` — \
                possible non-positive occurrence; folds over values built from \
                such payloads may not terminate (no positivity checker exists; \
                see examples/walls.rs). Silence with #[recursive(payload)] if \
                intentional.")]
            #[allow(dead_code)]
            fn __affine_cat_positivity_suspect() {}
            #[allow(dead_code)]
            fn __affine_cat_positivity_trigger() {
                #(#triggers)*
            }
        }
    };

    let borrowed_fold = if any_scoped {
        quote! {
            /// Fold in a SCOPED environment (generated): `env` is `&mut`,
            /// and each `#[recursive(scope)]` hole is bracketed by a
            /// `ScopeGuard` — restoration runs on normal exit, absorption
            /// `Break`, and panic alike (the Drop-guard shape mandated by
            /// `naive-leaks`/`balG`/`agree` in AbsorbEnv.agda). Field
            /// order is scoping order: order is contract. Algebras still
            /// read `&Env`; only the driver moves it.
            #vis fn fold_in<Env, Alg>(&self, env: &mut Env, alg: &Alg) -> Alg::Out
            where
                Env: ::affine_cat::cata::ScopedEnv + ?Sized,
                Alg: ::affine_cat::cata::FoldAlg<#name #ty_g, Env> + ?Sized,
            {
                fn self_fold #impl_g_env_scoped (
                    alg: &Alg,
                    env: &mut Env,
                    e: &#name #ty_g,
                ) -> ::core::ops::ControlFlow<Alg::Out, Alg::Out>
                where
                    Env: ::affine_cat::cata::ScopedEnv + ?Sized,
                    Alg: ::affine_cat::cata::FoldAlg<#name #ty_g, Env> + ?Sized,
                    #inner_where
                {
                    match e { #(#scoped_arms),* }
                }
                match self_fold(alg, env, self) {
                    ::core::ops::ControlFlow::Continue(x) => x,
                    ::core::ops::ControlFlow::Break(x) => x,
                }
            }
        }
    } else if borrowable {
        quote! {
            /// Fold with a bottom-up algebra, borrowing the tree (generated).
            /// No bounds: payloads are lent to the algebra, never cloned.
            /// (Not generated for Thunk-holed IRs — codata is consuming-only.)
            #vis fn fold<Env: ?Sized, Alg>(&self, env: &Env, alg: &Alg) -> Alg::Out
            where
                Alg: ::affine_cat::cata::FoldAlg<#name #ty_g, Env> + ?Sized,
            {
                fn self_fold #impl_g_env (
                    alg: &Alg,
                    env: &Env,
                    e: &#name #ty_g,
                ) -> ::core::ops::ControlFlow<Alg::Out, Alg::Out>
                where
                    Env: ?Sized,
                    Alg: ::affine_cat::cata::FoldAlg<#name #ty_g, Env> + ?Sized,
                    #inner_where
                {
                    match e { #(#fold_arms),* }
                }
                match self_fold(alg, env, self) {
                    ::core::ops::ControlFlow::Continue(x) => x,
                    ::core::ops::ControlFlow::Break(x) => x,
                }
            }
        }
    } else {
        quote! {}
    };

    let consuming = if movable {
        quote! {
            /// Owned pattern functor (generated): payloads by value, for
            /// consuming folds — the transformation family.
            #vis enum #owned<#(#epb,)* T> #where_c { #(#owned_variants),* }

            impl #impl_g ::affine_cat::cata::RecursiveOwned for #name #ty_g #owned_where {
                type LayerOwned<T> = #owned<#(#ep,)* T>;
                fn embed(layer: #owned<#(#ep,)* #name #ty_g>) -> #name #ty_g {
                    match layer { #(#embed_arms),* }
                }
                fn split_with<A, B, O>(
                    layer: #owned<#(#ep,)* (A, B)>,
                    k: &mut dyn for<'x> FnMut(#layer #layer_bx) -> O,
                ) -> (#owned<#(#ep,)* A>, O)
                where
                    Self: Sized + 'static,
                    B: 'static,
                {
                    match layer { #(#split_arms),* }
                }
            }

            impl #impl_g #name #ty_g #owned_where {
                /// Fold CONSUMING the tree (generated): payloads moved into
                /// owned layers — zero clones. Rewrites (`Out = Self`) reuse
                /// payloads directly. Thunks are forced by value: single-
                /// forcing is STATIC on this path. Generated only when every
                /// hole container is movable (`Box`/`Vec`/`Option`/`Thunk`);
                /// shared or memoized structure cannot be consumed.
                /// LIMIT: the tree type must not implement `Drop` —
                /// consuming folds destructure, which `Drop` types forbid
                /// (E0509 pointing at the derive; move instrumentation
                /// into a payload token instead, see examples/hylo.rs).
                #vis fn into_fold<Env: ?Sized, Alg>(self, env: &Env, alg: &Alg) -> Alg::Out
                where
                    Alg: ::affine_cat::cata::IntoFoldAlg<#name #ty_g, Env> + ?Sized,
                {
                    fn self_fold #impl_g_env (
                        alg: &Alg,
                        env: &Env,
                        e: #name #ty_g,
                    ) -> ::core::ops::ControlFlow<Alg::Out, Alg::Out>
                    where
                        Env: ?Sized,
                        Alg: ::affine_cat::cata::IntoFoldAlg<#name #ty_g, Env> + ?Sized,
                        #inner_where_owned
                    {
                        match e { #(#into_arms),* }
                    }
                    match self_fold(alg, env, self) {
                        ::core::ops::ControlFlow::Continue(x) => x,
                        ::core::ops::ControlFlow::Break(x) => x,
                    }
                }
            }
        }
    } else {
        quote! {}
    };

    quote! {
        #consuming

        /// Pattern functor for the derived type (generated). Payloads are
        /// borrowed from the tree; recursive positions carry results.
        #vis enum #layer #layer_decl_toks #layer_where { #(#layer_variants),* }

        #positivity

        impl #impl_g ::affine_cat::cata::Recursive for #name #ty_g #where_c {
            type Layer<'a, T> = #layer #layer_args #gat_where;
            fn unzip<'a, A, B>(
                l: #layer #layer_ab,
            ) -> (#layer #layer_a, #layer #layer_b)
            where
                Self: 'a,
            {
                match l { #(#unzip_arms),* }
            }
        }

        impl #impl_g #name #ty_g #where_c {
            #borrowed_fold

        }
    }
    .into()
}

// ===================== mutual recursion =====================

use syn::ItemMod;

/// Which sort a hole chain bottoms out in.
#[derive(Clone, Copy, PartialEq)]
enum Sort {
    S1,
    S2,
}

enum Shape2 {
    Chain(Vec<(Type, Type)>, Sort),
    Payload,
}

fn classify2(ty: &Type, e1: &syn::Ident, e2: &syn::Ident) -> Shape2 {
    if let Type::Path(tp) = ty {
        if let Some(seg) = tp.path.segments.last() {
            if tp.path.segments.len() == 1 && seg.arguments.is_none() {
                if &seg.ident == e1 {
                    return Shape2::Chain(Vec::new(), Sort::S1);
                }
                if &seg.ident == e2 {
                    return Shape2::Chain(Vec::new(), Sort::S2);
                }
                return Shape2::Payload;
            }
            if let syn::PathArguments::AngleBracketed(ab) = &seg.arguments {
                let tys: Vec<&Type> = ab
                    .args
                    .iter()
                    .filter_map(|a| {
                        if let syn::GenericArgument::Type(t) = a {
                            Some(t)
                        } else {
                            None
                        }
                    })
                    .collect();
                if tys.len() == 1 {
                    if let Shape2::Chain(mut c, s) = classify2(tys[0], e1, e2) {
                        c.insert(0, (ty.clone(), tys[0].clone()));
                        return Shape2::Chain(c, s);
                    }
                }
            }
        }
    }
    Shape2::Payload
}

fn mapped_ty2(chain: &[(Type, Type)], leaf: &proc_macro2::TokenStream) -> proc_macro2::TokenStream {
    match chain {
        [] => leaf.clone(),
        [(w, e), rest @ ..] => {
            let inner = mapped_ty2(rest, leaf);
            quote!(<#w as ::affine_cat::cata::Hole<#e>>::Mapped<#inner>)
        }
    }
}

fn try_map_expr2(
    chain: &[(Type, Type)],
    recv: proc_macro2::TokenStream,
    innermost: proc_macro2::TokenStream,
    absk: &syn::Ident,
    brkv: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    match chain {
        [] => quote! {
            match #innermost(alg, env, #recv) {
                ::core::ops::ControlFlow::Break(__b) => ::core::ops::ControlFlow::Break(__b),
                ::core::ops::ControlFlow::Continue(__v) => {
                    if alg.#absk(&__v) {
                        ::core::ops::ControlFlow::Break(#brkv(__v))
                    } else {
                        ::core::ops::ControlFlow::Continue(__v)
                    }
                }
            }
        },
        [(w, e), rest @ ..] => {
            let inner = try_map_expr2(rest, quote!(__c), innermost, absk, brkv);
            quote!(<#w as ::affine_cat::cata::Holes<#e>>::map_ref_until(#recv, &mut |__c| #inner))
        }
    }
}

fn map_expr2(
    chain: &[(Type, Type)],
    recv: proc_macro2::TokenStream,
    innermost: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    match chain {
        [] => quote!(#innermost(alg, env, #recv)),
        [(w, e), rest @ ..] => {
            let inner = map_expr2(rest, quote!(__c), innermost);
            quote!(<#w as ::affine_cat::cata::Holes<#e>>::map_ref(#recv, &mut |__c| #inner))
        }
    }
}

/// Mutual recursion for a two-sort family. Apply to a module holding
/// exactly two enums:
///
/// ```ignore
/// #[recursive_family]
/// mod ir {
///     pub enum Val { Lit(i64), Exists(#[recursive(scope)] Box<Rel>) }
///     pub enum Rel { Table(String), Filter(Box<Rel>, Box<Val>) }
/// }
/// ```
///
/// Generates: two-hole layers `{E}Layer<'a, S1, S2>` per sort, a
/// family-specific algebra trait `{E1}{E2}Fold<Env>` (Out1/Out2,
/// reduce per sort), and mutual drivers. If any field carries
/// `#[recursive(scope)]`, the drivers are `fold_in2` over a
/// `ScopedEnv`(affine_cat::cata::ScopedEnv) with Drop-guard
/// bracketing (balanced on normal exit and panic — the AbsorbEnv
/// discipline); otherwise plain `fold2` over `&Env`.
///
/// v1 limits, deliberate: exactly two sorts; tuple/unit variants;
/// borrowed drivers only (owned mutual waits for a consumer);
/// no absorption (the Out1/Out2 bubble type is undesigned until a
/// consumer's error shape picks it); frame CONTENT from sibling
/// folds is an open design — `enter` is content-free.
#[proc_macro_attribute]
pub fn recursive_family(
    _attr: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let mut m = parse_macro_input!(item as ItemMod);
    let Some((_, items)) = m.content.as_mut() else {
        return syn::Error::new_spanned(&m, "recursive_family needs an inline module")
            .to_compile_error()
            .into();
    };
    let mut enums: Vec<&mut syn::ItemEnum> = items
        .iter_mut()
        .filter_map(|i| {
            if let syn::Item::Enum(e) = i {
                Some(e)
            } else {
                None
            }
        })
        .collect();
    if enums.len() != 2 {
        return syn::Error::new_spanned(&m.ident, "recursive_family: exactly two enums (v1)")
            .to_compile_error()
            .into();
    }
    let (n1, n2) = (enums[0].ident.clone(), enums[1].ident.clone());
    let (l1, l2) = (format_ident!("{}Layer", n1), format_ident!("{}Layer", n2));
    let alg_trait = format_ident!("{}{}Fold", n1, n2);
    let absorb_trait = format_ident!("{}{}Absorb", n1, n2);
    let brk = format_ident!("{}{}Brk", n1, n2);
    let (r1, r2) = (
        format_ident!("reduce_{}", n1.to_string().to_lowercase()),
        format_ident!("reduce_{}", n2.to_string().to_lowercase()),
    );
    let vis = enums[0].vis.clone();

    let mut any_scoped = false;
    // ScopedEnvWith<I> bounds required by scope_prev sites (I = the
    // preceding hole's folded type, in algebra-generic form)
    let mut scope_info_bounds: Vec<proc_macro2::TokenStream> = Vec::new();
    let mut has_payload = [false, false];
    // uses[idx][s]: enum idx's layer mentions sort-s holes — hole-less
    // sorts must not emit phantom params (E0392, the family edition)
    let mut uses = [[false, false], [false, false]];
    let mut layer_variants = [Vec::new(), Vec::new()];
    let mut arms = [Vec::new(), Vec::new()];
    let mut try_arms: [Vec<proc_macro2::TokenStream>; 2] = [Vec::new(), Vec::new()];

    for (idx, en) in enums.iter_mut().enumerate() {
        let name = en.ident.clone();
        let layer = if idx == 0 { &l1 } else { &l2 };
        let self_fold = [format_ident!("self_fold1"), format_ident!("self_fold2")];
        for v in &mut en.variants {
            let vname = &v.ident;
            let fields = match &mut v.fields {
                Fields::Unit => {
                    layer_variants[idx].push(quote! { #vname });
                    let red = if idx == 0 { &r1 } else { &r2 };
                    arms[idx].push(quote! {
                        #name::#vname => alg.#red(&*env, #layer::#vname)
                    });
                    let absk = if idx == 0 {
                        format_ident!("absorbing1")
                    } else {
                        format_ident!("absorbing2")
                    };
                    let bv = if idx == 0 {
                        quote!(#brk::S1)
                    } else {
                        quote!(#brk::S2)
                    };
                    try_arms[idx].push(quote! {
                        #name::#vname => {
                            let __v = alg.#red(&*env, #layer::#vname);
                            if alg.#absk(&__v) {
                                ::core::ops::ControlFlow::Break(#bv(__v))
                            } else {
                                ::core::ops::ControlFlow::Continue(__v)
                            }
                        }
                    });
                    continue;
                }
                Fields::Unnamed(f) => f,
                Fields::Named(_) => {
                    return syn::Error::new_spanned(vname, "named fields unsupported (v1)")
                        .to_compile_error()
                        .into();
                }
            };
            let mut shapes = Vec::new();
            let mut scoped = Vec::new();
            for f in &mut fields.unnamed {
                let mut forced: Option<&str> = None;
                let mut sc = 0u8; // 0 plain, 1 scope, 2 scope_prev
                for a in &f.attrs {
                    if a.path().is_ident("recursive") {
                        if let Ok(id) = a.parse_args::<syn::Ident>() {
                            if id == "hole" {
                                forced = Some("hole");
                            }
                            if id == "payload" {
                                forced = Some("payload");
                            }
                            if id == "scope" {
                                sc = 1;
                                any_scoped = true;
                            }
                            if id == "scope_prev" {
                                sc = 2;
                                any_scoped = true;
                            }
                        }
                    }
                }
                // attribute macros must strip helper attrs from the output
                f.attrs.retain(|a| !a.path().is_ident("recursive"));
                let shape = match forced {
                    Some("payload") => Shape2::Payload,
                    Some("hole") => {
                        // literal field type, sort = whichever ident it names;
                        // default to self-sort when opaque
                        match classify2(&f.ty, &n1, &n2) {
                            Shape2::Chain(_, s) => Shape2::Chain(vec![], s),
                            Shape2::Payload => {
                                let s = if idx == 0 { Sort::S1 } else { Sort::S2 };
                                Shape2::Chain(vec![], s)
                            }
                        }
                    }
                    _ => classify2(&f.ty, &n1, &n2),
                };
                // forced hole: depth-1 with literal type
                let shape = if forced == Some("hole") {
                    if let Shape2::Chain(_, s) = shape {
                        let elem: Type = if s == Sort::S1 {
                            syn::parse_quote!(#n1)
                        } else {
                            syn::parse_quote!(#n2)
                        };
                        Shape2::Chain(vec![(f.ty.clone(), elem)], s)
                    } else {
                        shape
                    }
                } else {
                    shape
                };
                if let Shape2::Chain(_, s) = &shape {
                    uses[idx][if *s == Sort::S1 { 0 } else { 1 }] = true;
                }
                shapes.push((shape, f.ty.clone()));
                scoped.push(sc);
            }
            let binds: Vec<_> = (0..shapes.len()).map(|i| format_ident!("f{}", i)).collect();
            let tys: Vec<_> = shapes
                .iter()
                .map(|(s, ty)| match s {
                    Shape2::Chain(c, sort) => {
                        let leaf = if *sort == Sort::S1 {
                            quote!(S1)
                        } else {
                            quote!(S2)
                        };
                        mapped_ty2(c, &leaf)
                    }
                    Shape2::Payload => {
                        has_payload[idx] = true;
                        quote!(&'a #ty)
                    }
                })
                .collect();
            layer_variants[idx].push(quote! { #vname( #(#tys),* ) });
            let steps: Vec<_> = shapes
            .iter()
            .enumerate()
            .map(|(i, (s, _))| {
                let f = &binds[i];
                match s {
                    Shape2::Chain(c, sort) => {
                        let inner = if *sort == Sort::S1 {
                            let sf = &self_fold[0];
                            quote!(#sf)
                        } else {
                            let sf = &self_fold[1];
                            quote!(#sf)
                        };
                        let e = map_expr2(c, quote!(#f), inner);
                        match scoped[i] {
                            1 => quote! {
                                let #f = {
                                    let mut __g = ::affine_cat::cata::ScopeGuard::new(&mut *env);
                                    let env = __g.env();
                                    #e
                                };
                            },
                            2 => {
                                if i == 0 {
                                    return syn::Error::new_spanned(
                                        vname,
                                        "scope_prev needs a preceding field to draw from",
                                    )
                                    .to_compile_error()
                                    .into();
                                }
                                let Shape2::Chain(pc, ps) = &shapes[i - 1].0 else {
                                    return syn::Error::new_spanned(
                                        vname,
                                        "scope_prev: the preceding field must be a hole \
                                         (its folded value feeds the frame)",
                                    )
                                    .to_compile_error()
                                    .into();
                                };
                                let leaf = if *ps == Sort::S1 {
                                    quote!(A::Out1)
                                } else {
                                    quote!(A::Out2)
                                };
                                scope_info_bounds.push(mapped_ty2(pc, &leaf));
                                let prev = &binds[i - 1];
                                quote! {
                                    let #f = {
                                        let __fr = ::affine_cat::cata::ScopedEnvWith::enter_with(
                                            &mut *env, &#prev,
                                        );
                                        let mut __g =
                                            ::affine_cat::cata::ScopeGuard::from_frame(&mut *env, __fr);
                                        let env = __g.env();
                                        #e
                                    };
                                }
                            }
                            _ => quote! { let #f = #e; },
                        }
                    }
                    Shape2::Payload => quote! {},
                }
            })
            .collect();
            let red = if idx == 0 { &r1 } else { &r2 };
            arms[idx].push(quote! {
                #name::#vname( #(#binds),* ) => {
                    #(#steps)*
                    alg.#red(&*env, #layer::#vname(#(#binds),*))
                }
            });

            // absorbing (try) arms: same guards, break-typed traversal,
            // per-sort absorption checks, either-shaped bubble
            let absk = if idx == 0 {
                format_ident!("absorbing1")
            } else {
                format_ident!("absorbing2")
            };
            let bv = if idx == 0 {
                quote!(#brk::S1)
            } else {
                quote!(#brk::S2)
            };
            let try_steps: Vec<_> = shapes
                .iter()
                .enumerate()
                .map(|(i, (s, _))| {
                    let f = &binds[i];
                    match s {
                        Shape2::Chain(c, sort) => {
                            let (inner, iabsk, ibv) = if *sort == Sort::S1 {
                                let sf = format_ident!("try_self_fold1");
                                (quote!(#sf), format_ident!("absorbing1"), quote!(#brk::S1))
                            } else {
                                let sf = format_ident!("try_self_fold2");
                                (quote!(#sf), format_ident!("absorbing2"), quote!(#brk::S2))
                            };
                            let e = try_map_expr2(c, quote!(#f), inner, &iabsk, ibv);
                            let body = quote! {
                                match #e {
                                    ::core::ops::ControlFlow::Continue(__m) => __m,
                                    ::core::ops::ControlFlow::Break(__b) => {
                                        return ::core::ops::ControlFlow::Break(__b)
                                    }
                                }
                            };
                            match scoped[i] {
                                1 => quote! {
                                    let #f = {
                                        let mut __g =
                                            ::affine_cat::cata::ScopeGuard::new(&mut *env);
                                        let env = __g.env();
                                        #body
                                    };
                                },
                                2 => {
                                    let prev = &binds[i - 1];
                                    quote! {
                                        let #f = {
                                            let __fr =
                                                ::affine_cat::cata::ScopedEnvWith::enter_with(
                                                    &mut *env, &#prev,
                                                );
                                            let mut __g =
                                                ::affine_cat::cata::ScopeGuard::from_frame(
                                                    &mut *env, __fr,
                                                );
                                            let env = __g.env();
                                            #body
                                        };
                                    }
                                }
                                _ => quote! { let #f = #body; },
                            }
                        }
                        Shape2::Payload => quote! {},
                    }
                })
                .collect();
            try_arms[idx].push(quote! {
                #name::#vname( #(#binds),* ) => {
                    #(#try_steps)*
                    let __v = alg.#red(&*env, #layer::#vname(#(#binds),*));
                    if alg.#absk(&__v) {
                        ::core::ops::ControlFlow::Break(#bv(__v))
                    } else {
                        ::core::ops::ControlFlow::Continue(__v)
                    }
                }
            });
        }
    }

    let params = |hp: bool, u: [bool; 2], s1: proc_macro2::TokenStream, s2: proc_macro2::TokenStream| {
        let mut ps: Vec<proc_macro2::TokenStream> = Vec::new();
        if hp {
            ps.push(quote!('a));
        }
        if u[0] {
            ps.push(s1);
        }
        if u[1] {
            ps.push(s2);
        }
        if ps.is_empty() {
            quote!()
        } else {
            quote!(<#(#ps),*>)
        }
    };
    let gen_layer = |layer: &syn::Ident, variants: &Vec<proc_macro2::TokenStream>, hp: bool, u: [bool; 2]| {
        let generics = params(hp, u, quote!(S1), quote!(S2));
        quote! {
            /// Two-hole pattern functor (generated): hole params carry
            /// the sorts' results (pruned to the sorts this layer
            /// actually contains); payloads are borrowed from the tree.
            #vis enum #layer #generics { #(#variants),* }
        }
    };
    let layer1 = gen_layer(&l1, &layer_variants[0], has_payload[0], uses[0]);
    let layer2 = gen_layer(&l2, &layer_variants[1], has_payload[1], uses[1]);
    let la1 = params(has_payload[0], uses[0], quote!(Self::Out1), quote!(Self::Out2));
    let la2 = params(has_payload[1], uses[1], quote!(Self::Out1), quote!(Self::Out2));
    let (arms1, arms2) = (&arms[0], &arms[1]);
    let (tarms1, tarms2) = (&try_arms[0], &try_arms[1]);
    // dedup ScopedEnvWith bounds (multiple scope_prev sites of one sort)
    {
        let mut seen = std::collections::HashSet::new();
        scope_info_bounds.retain(|t| seen.insert(t.to_string()));
    }

    let (env_param, env_bound, entry_env) = if any_scoped {
        (
            quote!(&mut Env),
            quote!(::affine_cat::cata::ScopedEnv
                #(+ ::affine_cat::cata::ScopedEnvWith<#scope_info_bounds>)* + ?Sized),
            quote!(env),
        )
    } else {
        (quote!(&Env), quote!(?Sized), quote!(env))
    };
    let driver_name = if any_scoped {
        format_ident!("fold_in2")
    } else {
        format_ident!("fold2")
    };
    let try_driver_name = if any_scoped {
        format_ident!("try_fold_in2")
    } else {
        format_ident!("try_fold2")
    };
    let driver_doc = if any_scoped {
        "Mutual scoped fold (generated): `#[recursive(scope)]` holes are Drop-guard bracketed; balanced on every exit."
    } else {
        "Mutual fold (generated): both sorts, one environment, borrowed layers."
    };

    let glue = quote! {
        #layer1
        #layer2

        /// Two-sorted bottom-up algebra for this family (generated —
        /// family-specific by design: multirec-style generic machinery
        /// traded for monomorphic clarity).
        #vis trait #alg_trait<Env: ?Sized> {
            /// Result at the first sort.
            type Out1;
            /// Result at the second sort.
            type Out2;
            /// Reduce one layer of the first sort.
            fn #r1<'a>(&self, env: &Env, l: #l1 #la1) -> Self::Out1;
            /// Reduce one layer of the second sort.
            fn #r2<'a>(&self, env: &Env, l: #l2 #la2) -> Self::Out2;
        }

        fn self_fold1<Env: #env_bound, A: #alg_trait<Env> + ?Sized>(
            alg: &A,
            env: #env_param,
            e: &#n1,
        ) -> A::Out1 {
            match e { #(#arms1),* }
        }
        fn self_fold2<Env: #env_bound, A: #alg_trait<Env> + ?Sized>(
            alg: &A,
            env: #env_param,
            e: &#n2,
        ) -> A::Out2 {
            match e { #(#arms2),* }
        }

        impl #n1 {
            #[doc = #driver_doc]
            #vis fn #driver_name<Env: #env_bound, A: #alg_trait<Env> + ?Sized>(
                &self,
                env: #env_param,
                alg: &A,
            ) -> A::Out1 {
                self_fold1(alg, #entry_env, self)
            }
        }
        impl #n2 {
            #[doc = #driver_doc]
            #vis fn #driver_name<Env: #env_bound, A: #alg_trait<Env> + ?Sized>(
                &self,
                env: #env_param,
                alg: &A,
            ) -> A::Out2 {
                self_fold2(alg, #entry_env, self)
            }
        }

        /// The cross-sort bubble (generated): a short-circuit carries ONE
        /// value; this either is its type until the entry sort promotes it.
        #vis enum #brk<A, B> {
            /// absorbed at the first sort
            S1(A),
            /// absorbed at the second sort
            S2(B),
        }

        /// Opt-in absorption for this family (generated). Predicates
        /// default to `false`; the promotes are REQUIRED — no defaulted
        /// panic traps.
        ///
        /// # Law (bubble-form annihilation — `TwoAbsorb.agda`, T-X)
        /// At every hole, the reduce applied to a bubble's reading at
        /// that sort must equal the bubble's reading at the node's sort.
        /// Same-sort bubbles: ordinary annihilation. CROSS-SORT bubbles:
        /// additionally requires promotes to act as SECTIONS on absorbed
        /// values (`reduce(promote(x)) ≡ x`-shaped). Satisfied vacuously
        /// by single-sort-absorbing algebras (a resolver whose errors
        /// live in one sort), and by shared-error `Result` carriers via
        /// `Err`-passthrough; a LOSSY promote with double-crossing
        /// bubbles violates it — the proof, not the docs, found this
        /// obligation. Under scoped drivers the annihilation must also
        /// be ENV-UNIFORM — a bubble transits scopes on the way out, so
        /// its license cannot depend on the environment
        /// (`ScopedAbsorb.agda`, T2X; `Err`-passthrough is depth-blind).
        #vis trait #absorb_trait<Env: ?Sized>: #alg_trait<Env> {
            /// Is this first-sort value absorbing?
            fn absorbing1(&self, _out: &Self::Out1) -> bool {
                false
            }
            /// Is this second-sort value absorbing?
            fn absorbing2(&self, _out: &Self::Out2) -> bool {
                false
            }
            /// Carry a second-sort bubble across a first-sort entry.
            fn promote_2_to_1(&self, out: Self::Out2) -> Self::Out1;
            /// Carry a first-sort bubble across a second-sort entry.
            fn promote_1_to_2(&self, out: Self::Out1) -> Self::Out2;
        }

        fn try_self_fold1<Env: #env_bound, A: #absorb_trait<Env> + ?Sized>(
            alg: &A,
            env: #env_param,
            e: &#n1,
        ) -> ::core::ops::ControlFlow<#brk<A::Out1, A::Out2>, A::Out1> {
            match e { #(#tarms1),* }
        }
        fn try_self_fold2<Env: #env_bound, A: #absorb_trait<Env> + ?Sized>(
            alg: &A,
            env: #env_param,
            e: &#n2,
        ) -> ::core::ops::ControlFlow<#brk<A::Out1, A::Out2>, A::Out2> {
            match e { #(#tarms2),* }
        }

        impl #n1 {
            /// Absorbing mutual fold (generated): short-circuits on
            /// absorbing values of EITHER sort; a cross-sort bubble is
            /// promoted at this entry. Guards keep the env balanced on
            /// the bubble path (the AbsorbEnv discipline).
            #vis fn #try_driver_name<Env: #env_bound, A: #absorb_trait<Env> + ?Sized>(
                &self,
                env: #env_param,
                alg: &A,
            ) -> A::Out1 {
                match try_self_fold1(alg, #entry_env, self) {
                    ::core::ops::ControlFlow::Continue(x) => x,
                    ::core::ops::ControlFlow::Break(#brk::S1(x)) => x,
                    ::core::ops::ControlFlow::Break(#brk::S2(y)) => alg.promote_2_to_1(y),
                }
            }
        }
        impl #n2 {
            /// Absorbing mutual fold (generated), second-sort entry.
            #vis fn #try_driver_name<Env: #env_bound, A: #absorb_trait<Env> + ?Sized>(
                &self,
                env: #env_param,
                alg: &A,
            ) -> A::Out2 {
                match try_self_fold2(alg, #entry_env, self) {
                    ::core::ops::ControlFlow::Continue(x) => x,
                    ::core::ops::ControlFlow::Break(#brk::S2(x)) => x,
                    ::core::ops::ControlFlow::Break(#brk::S1(y)) => alg.promote_1_to_2(y),
                }
            }
        }
    };
    items.push(syn::Item::Verbatim(glue));
    quote!(#m).into()
}
