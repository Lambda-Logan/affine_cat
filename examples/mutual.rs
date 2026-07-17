//! Mutual recursion + the resolver pattern: `Filter`'s predicate is
//! scoped BY the relation's fold result (`scope_prev`) — bindings flow
//! from the sibling fold into the frame, algebras still read `&Env`,
//! and nothing is laundered through interior mutability.
use affine_cat::cata::{ScopedEnv, ScopedEnvWith};
use affine_cat_derive::recursive_family;

#[recursive_family]
mod ir {
    pub enum Val {
        #[allow(dead_code)]
        Lit(i64),
        Col(String),
        Add(Box<Val>, Box<Val>),
        Exists(#[recursive(scope)] Box<Rel>),
    }
    pub enum Rel {
        Table(String),
        // rel first, predicate scoped by the rel's RESULT: order is contract
        Filter(Box<Rel>, #[recursive(scope_prev)] Box<Val>),
        #[allow(dead_code)]
        Union(Vec<Rel>),
    }
}
use ir::*;

/// binding stack: frames are length snapshots (the AbsorbEnv model)
struct Scopes {
    stack: Vec<Vec<String>>,
}
impl ScopedEnv for Scopes {
    type Frame = usize;
    fn enter(&mut self) -> usize {
        self.stack.len() // plain scope: a marker frame, no bindings
    }
    fn exit(&mut self, saved: usize) {
        self.stack.truncate(saved);
    }
}
/// the resolver's content-carrying entry: the relation's columns.
/// (Out2 is a Result — errors woven by hand across the sort boundary,
/// which is exactly the weave two-sorted absorption will relieve; an
/// errored relation contributes an empty frame and the error rides on.)
impl ScopedEnvWith<Result<Vec<String>, String>> for Scopes {
    fn enter_with(&mut self, cols: &Result<Vec<String>, String>) -> usize {
        let saved = self.stack.len();
        if let Ok(c) = cols {
            self.stack.push(c.clone());
        }
        saved
    }
}
/// enter_with for a plain-Vec Out2 (the absorbing resolver below)
impl ScopedEnvWith<Vec<String>> for Scopes {
    fn enter_with(&mut self, cols: &Vec<String>) -> usize {
        let saved = self.stack.len();
        self.stack.push(cols.clone());
        saved
    }
}
/// algebras whose Out2 carries no bindings delegate to plain enter
impl ScopedEnvWith<Option<String>> for Scopes {
    fn enter_with(&mut self, _: &Option<String>) -> usize {
        self.enter()
    }
}
impl ScopedEnvWith<String> for Scopes {
    fn enter_with(&mut self, _: &String) -> usize {
        self.enter()
    }
}

fn table_cols(t: &str) -> Vec<String> {
    match t {
        "t" => vec!["a".into(), "b".into()],
        "u" => vec!["c".into()],
        _ => vec![],
    }
}

/// name resolution: Out2 = the relation's columns; Out1 = Result.
/// Col checks membership across the visible stack — WSV/safeV, live.
struct Resolve;
impl ValRelFold<Scopes> for Resolve {
    type Out1 = Result<(), String>;
    type Out2 = Result<Vec<String>, String>;
    fn reduce_val<'a>(&self, env: &Scopes, l: ValLayer<'a, Self::Out1, Self::Out2>) -> Self::Out1 {
        match l {
            ValLayer::Lit(_) => Ok(()),
            ValLayer::Col(c) => {
                if env.stack.iter().any(|f| f.iter().any(|x| x == c)) {
                    Ok(())
                } else {
                    Err(format!("unresolved column: {c}"))
                }
            }
            ValLayer::Add(a, b) => a.and(b),
            ValLayer::Exists(r) => r.map(|_| ()),
        }
    }
    fn reduce_rel<'a>(&self, _: &Scopes, l: RelLayer<'a, Self::Out1, Self::Out2>) -> Self::Out2 {
        match l {
            RelLayer::Table(t) => Ok(table_cols(t)),
            // the by-hand weave: the predicate's error must be threaded
            // through the RELATION's output or it dies here
            RelLayer::Filter(cols, pred) => {
                let cols = cols?;
                pred?;
                Ok(cols)
            }
            RelLayer::Union(rs) => {
                let mut all = Vec::new();
                for r in rs {
                    all.extend(r?);
                }
                Ok(all)
            }
        }
    }
}

/// render still works: its Out2 = String takes the delegating impl
struct Render;
impl ValRelFold<Scopes> for Render {
    type Out1 = String;
    type Out2 = String;
    fn reduce_val<'a>(&self, _: &Scopes, l: ValLayer<'a, String, String>) -> String {
        match l {
            ValLayer::Lit(n) => n.to_string(),
            ValLayer::Col(c) => c.clone(),
            ValLayer::Add(a, b) => format!("({a} + {b})"),
            ValLayer::Exists(r) => format!("exists[{r}]"),
        }
    }
    fn reduce_rel<'a>(&self, _: &Scopes, l: RelLayer<'a, String, String>) -> String {
        match l {
            RelLayer::Table(t) => t.clone(),
            RelLayer::Filter(r, p) => format!("{r} where {p}"),
            RelLayer::Union(rs) => rs.join(" union "),
        }
    }
}

fn col(c: &str) -> Val {
    Val::Col(c.into())
}
fn filter(t: &str, p: Val) -> Rel {
    Rel::Filter(Box::new(Rel::Table(t.into())), Box::new(p))
}

fn main() {
    // exists[t where (a + exists[u where (c + b)])]
    // - `a` resolves in t's frame; `c` in u's; `b` in the OUTER t frame
    //   (correlated subquery) — the stack search across scope_prev frames
    let good = Val::Exists(Box::new(filter(
        "t",
        Val::Add(
            Box::new(col("a")),
            Box::new(Val::Exists(Box::new(filter(
                "u",
                Val::Add(Box::new(col("c")), Box::new(col("b"))),
            )))),
        ),
    )));
    let mut env = Scopes { stack: vec![] };
    assert_eq!(good.fold_in2(&mut env, &Resolve), Ok(()));
    assert!(env.stack.is_empty(), "balanced: every frame popped");

    // a column that exists nowhere: the error carries out, env balanced
    let bad = Val::Exists(Box::new(filter("t", col("zz"))));
    let mut env = Scopes { stack: vec![] };
    assert_eq!(
        bad.fold_in2(&mut env, &Resolve),
        Err("unresolved column: zz".into())
    );
    assert!(env.stack.is_empty(), "balanced on the error path too");

    // an out-of-scope reference: `c` lives in u's frame, not visible at t
    let leaky = Val::Exists(Box::new(filter("t", col("c"))));
    let mut env = Scopes { stack: vec![] };
    assert!(leaky.fold_in2(&mut env, &Resolve).is_err());

    // the delegating-impl path: render is oblivious to binding content
    let mut env = Scopes { stack: vec![] };
    let s = good.fold_in2(&mut env, &Render);
    assert_eq!(s, "exists[t where (a + exists[u where (c + b)])]");

    // ===== the CONTRAST: the same resolver, unwoven, via absorption =====
    // Out2 returns to plain Vec<String>; the predicate's error is carried
    // by the DRIVER as a cross-sort bubble — Filter can ignore it, the
    // Union collect disappears, and promotes are written once.
    struct ResolveAbs;
    impl ValRelFold<Scopes> for ResolveAbs {
        type Out1 = Result<(), String>;
        type Out2 = Vec<String>;
        fn reduce_val<'a>(
            &self,
            env: &Scopes,
            l: ValLayer<'a, Self::Out1, Self::Out2>,
        ) -> Self::Out1 {
            match l {
                ValLayer::Lit(_) => Ok(()),
                ValLayer::Col(c) => {
                    if env.stack.iter().any(|f| f.iter().any(|x| x == c)) {
                        Ok(())
                    } else {
                        Err(format!("unresolved column: {c}"))
                    }
                }
                ValLayer::Add(a, b) => a.and(b),
                ValLayer::Exists(_) => Ok(()),
            }
        }
        fn reduce_rel<'a>(
            &self,
            _: &Scopes,
            l: RelLayer<'a, Self::Out1, Self::Out2>,
        ) -> Self::Out2 {
            match l {
                RelLayer::Table(t) => table_cols(t),
                RelLayer::Filter(cols, _pred) => cols, // errors bubbled already
                RelLayer::Union(rs) => rs.into_iter().flatten().collect(),
            }
        }
    }
    impl ValRelAbsorb<Scopes> for ResolveAbs {
        fn absorbing1(&self, o: &Self::Out1) -> bool {
            o.is_err()
        }
        fn promote_2_to_1(&self, _cols: Self::Out2) -> Self::Out1 {
            unreachable!("Out2 never absorbs (absorbing2 is false)")
        }
        fn promote_1_to_2(&self, _e: Self::Out1) -> Self::Out2 {
            unreachable!("second-sort entry unused in this pass")
        }
    }
    let mut env = Scopes { stack: vec![] };
    assert_eq!(good.try_fold_in2(&mut env, &ResolveAbs), Ok(()));
    assert!(env.stack.is_empty());

    let mut env = Scopes { stack: vec![] };
    let r = bad.try_fold_in2(&mut env, &ResolveAbs);
    assert_eq!(r, Err("unresolved column: zz".into()));
    assert!(
        env.stack.is_empty(),
        "balanced through the cross-sort bubble"
    );

    println!("resolver: {s}");
    // the CROSS-SORT bubble that actually crosses: absorption at the
    // REL sort, entry at the VAL sort — promote_2_to_1 executes.
    struct FindTable(&'static str);
    impl ValRelFold<Scopes> for FindTable {
        type Out1 = Option<String>;
        type Out2 = Option<String>;
        fn reduce_val<'a>(
            &self,
            _: &Scopes,
            l: ValLayer<'a, Self::Out1, Self::Out2>,
        ) -> Self::Out1 {
            match l {
                ValLayer::Lit(_) | ValLayer::Col(_) => None,
                ValLayer::Add(a, b) => a.or(b),
                ValLayer::Exists(r) => r,
            }
        }
        fn reduce_rel<'a>(
            &self,
            _: &Scopes,
            l: RelLayer<'a, Self::Out1, Self::Out2>,
        ) -> Self::Out2 {
            match l {
                RelLayer::Table(t) if t == self.0 => Some(t.clone()),
                RelLayer::Table(_) => None,
                RelLayer::Filter(r, p) => r.or(p),
                RelLayer::Union(rs) => rs.into_iter().flatten().next(),
            }
        }
    }
    impl ValRelAbsorb<Scopes> for FindTable {
        fn absorbing2(&self, o: &Self::Out2) -> bool {
            o.is_some() // absorbs at the REL sort
        }
        // identical Outs: promotes are identities — bubble-form laws
        // reduce to plain annihilation (TwoAbsorb's easy case)
        fn promote_2_to_1(&self, o: Self::Out2) -> Self::Out1 {
            o
        }
        fn promote_1_to_2(&self, o: Self::Out1) -> Self::Out2 {
            o
        }
    }
    let mut env = Scopes { stack: vec![] };
    // entry at Val; `u` found deep inside a Rel — the b2 bubble exits
    // through the Val entry via promote_2_to_1, env balanced through it
    let found = good.try_fold_in2(&mut env, &FindTable("u"));
    assert_eq!(found, Some("u".to_string()));
    assert!(env.stack.is_empty(), "balanced through the promoted exit");

    println!(
        "mutual: ok  |  scope_prev: ok  |  correlated subquery: ok  |  \
         absorption across sorts: ok  |  promote path: ok  |  balanced: ok"
    );
}
