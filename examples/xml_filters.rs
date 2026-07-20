//! A small port of HXT (the Haskell XML Toolbox) — its arrow-based XML
//! filters — over [`affine_cat::cps`], the crate's push-encoded morphism
//! module. This example is where that module came from: the filter trait
//! lived here until a second domain (compiler pass pipelines over an arena)
//! wanted the same shape, which fired the promotion rule.
//!
//! HXT's core is the *list arrow* `newtype LA a b = LA (a -> [b])`: one input,
//! many outputs, composed by `concatMap`. Every XML filter (`getChildren`,
//! `deep`, `hasName`, `getText`, `<+>`) is an instance, and a query reads
//! left-to-right: `getChildren >>> hasName "p" >>> getChildren >>> getText`.
//!
//! [`Piece`] is that arrow, push-encoded: a filter hands each output to a
//! continuation instead of returning a list. Compared to the naive ports —
//! `Fn(A) -> Vec<B>` clones every node; `Fn(A) -> impl Iterator` is lazy but
//! unboxable — the push form is borrowed (zero node clones), single-pass,
//! short-circuiting ([`ControlFlow::Break`]), and object-safe through
//! [`PieceDyn`], so query pipelines composed at *runtime* (XPath from a
//! string) work too.
//!
//! XML filters are stateless, so everything here runs at `Env = ()` — the
//! environment parameter is a ZST and costs nothing. The stateful face (an
//! arena threaded through the continuation) is exercised by the `cps`
//! module's own tests.
//!
//! What push cannot do: predicates over the *materialized* result list —
//! `[last()]`, `[position()=n]`, sorting, counts — must buffer, and a
//! borrowed node cannot escape its callback, so buffering clones (shown at
//! the end). That cost is real in Rust and invisible in Haskell, where the
//! GC'd `[b]` shares freely. Tree *transforms* (HXT's `processChildren`)
//! rebuild structure and belong to the functor spine, not to filters.

use affine_cat::cps::{Piece, PieceDyn};
use core::ops::ControlFlow;

/// A minimal XML node.
#[derive(Clone, Debug)]
enum Node {
    Elem(String, Vec<Node>),
    Text(String),
}

// ---- the leaf filters (HXT's ArrowXml vocabulary), Env = () ----

/// `getChildren`: emit each child of an element (nothing for text).
struct Children;
impl Piece<Node> for Children {
    type Out = Node;
    fn run<R>(
        &self,
        env: &mut (),
        n: &Node,
        k: &mut dyn FnMut(&mut (), &Node) -> ControlFlow<R>,
    ) -> ControlFlow<R> {
        if let Node::Elem(_, cs) = n {
            for c in cs {
                k(env, c)?;
            }
        }
        ControlFlow::Continue(())
    }
}

/// `hasName t`: keep the node iff it is an element named `t` (0-or-1 output).
struct Tag(&'static str);
impl Piece<Node> for Tag {
    type Out = Node;
    fn run<R>(
        &self,
        env: &mut (),
        n: &Node,
        k: &mut dyn FnMut(&mut (), &Node) -> ControlFlow<R>,
    ) -> ControlFlow<R> {
        match n {
            Node::Elem(t, _) if *t == self.0 => k(env, n),
            _ => ControlFlow::Continue(()),
        }
    }
}

/// `getText`: emit the string of a text node. `Out = str` (`?Sized` is fine).
struct Text;
impl Piece<Node> for Text {
    type Out = str;
    fn run<R>(
        &self,
        env: &mut (),
        n: &Node,
        k: &mut dyn FnMut(&mut (), &str) -> ControlFlow<R>,
    ) -> ControlFlow<R> {
        match n {
            Node::Text(s) => k(env, s),
            _ => ControlFlow::Continue(()),
        }
    }
}

/// `deep f`: the shallowest descendants matching `f`; does not descend into a
/// match (HXT's `deep`, vs `multi` which keeps descending).
struct Deep<F>(F);
impl<F: Piece<Node, Out = Node>> Piece<Node> for Deep<F> {
    type Out = Node;
    fn run<R>(
        &self,
        env: &mut (),
        n: &Node,
        k: &mut dyn FnMut(&mut (), &Node) -> ControlFlow<R>,
    ) -> ControlFlow<R> {
        let mut matched = false;
        self.0.run(env, n, &mut |env, m| {
            matched = true;
            k(env, m)
        })?;
        if !matched {
            if let Node::Elem(_, cs) = n {
                for c in cs {
                    self.run(env, c, k)?;
                }
            }
        }
        ControlFlow::Continue(())
    }
}

fn children() -> Children {
    Children
}
fn tag(t: &'static str) -> Tag {
    Tag(t)
}
fn text() -> Text {
    Text
}
fn deep<F: Piece<Node, Out = Node>>(f: F) -> Deep<F> {
    Deep(f)
}

/// Run a `str`-emitting filter to completion and collect (HXT's `runLA`).
fn collect_text(n: &Node, f: impl Piece<Node, Out = str>) -> Vec<String> {
    let mut out = Vec::new();
    let _: ControlFlow<()> = f.run(&mut (), n, &mut |_, s| {
        out.push(s.to_string());
        ControlFlow::Continue(())
    });
    out
}

fn main() {
    // <div><p>a</p><span><p>nested</p></span><p>b</p></div>
    let doc = Node::Elem(
        "div".into(),
        vec![
            Node::Elem("p".into(), vec![Node::Text("a".into())]),
            Node::Elem(
                "span".into(),
                vec![Node::Elem("p".into(), vec![Node::Text("nested".into())])],
            ),
            Node::Elem("p".into(), vec![Node::Text("b".into())]),
        ],
    );

    // 1. The HXT query, left-to-right:
    //    getChildren >>> hasName "p" >>> getChildren >>> getText
    let direct = collect_text(
        &doc,
        children().link(tag("p")).link(children()).link(text()),
    );
    println!("direct <p> text:  {direct:?}");
    assert_eq!(direct, ["a", "b"]); // nested <p> is not a direct child

    // 2. deep: every <p> anywhere, then its text.
    let all = collect_text(&doc, deep(tag("p")).link(children()).link(text()));
    println!("deep <p> text:    {all:?}");
    assert_eq!(all, ["a", "nested", "b"]);

    // 3. union (<+>) via `or`: direct <p> children, OR the <span>'s children
    //    (one level deeper, where its <p> lives) — then a shared text tail.
    let union = children()
        .link(tag("p"))
        .both(children().link(tag("span")).link(children()))
        .link(children().link(text()));
    let both = collect_text(&doc, union);
    println!("p-or-span text:   {both:?}");
    assert_eq!(both, ["a", "b", "nested"]); // left branch streams fully first

    // 4. short-circuit: first match only, via Break.
    let mut first = None;
    let _: ControlFlow<()> =
        deep(tag("p"))
            .link(children())
            .link(text())
            .run(&mut (), &doc, &mut |_, s| {
                first = Some(s.to_string());
                ControlFlow::Break(())
            });
    println!("first (break):    {first:?}");
    assert_eq!(first.as_deref(), Some("a"));

    // 5. runtime-composed pipeline (XPath-from-a-string): boxed PieceDyn
    //    stages nested by recursion. The blanket makes every filter above a
    //    PieceDyn for free; object safety is why this compiles.
    let stages: Vec<Box<dyn PieceDyn<Node, Out = Node>>> = vec![
        Box::new(children()),
        Box::new(tag("p")),
        Box::new(children()),
    ];
    fn run_pipeline(
        fs: &[Box<dyn PieceDyn<Node, Out = Node>>],
        n: &Node,
        sink: &mut dyn FnMut(&Node),
    ) {
        match fs.split_first() {
            None => sink(n),
            Some((f, rest)) => {
                let _ = f.run_dyn(&mut (), n, &mut |_, m| {
                    run_pipeline(rest, m, sink);
                    ControlFlow::Continue(())
                });
            }
        }
    }
    let mut count = 0;
    run_pipeline(&stages, &doc, &mut |_| count += 1);
    println!("runtime pipeline: {count} nodes");
    assert_eq!(count, 2);

    // 6. THE WALL: [last()] needs the whole list — buffer, and a borrowed
    //    node cannot escape its callback, so buffering clones.
    let mut ps: Vec<Node> = Vec::new();
    let _: ControlFlow<()> = children().link(tag("p")).run(&mut (), &doc, &mut |_, p| {
        ps.push(p.clone()); // the honest cost of materializing
        ControlFlow::Continue(())
    });
    let last = ps.last().map(|p| collect_text(p, children().link(text())));
    println!("last <p> text:    {last:?}  (buffered via clone)");
    assert_eq!(last, Some(vec!["b".to_string()]));

    println!("\nHXT's list arrows over affine_cat::cps: borrowed, single-pass,");
    println!("object-safe when erased; position predicates pay the clone that");
    println!("Haskell's GC'd [b] hides.");
}
