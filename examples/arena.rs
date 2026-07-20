//! The bracketed pattern over a hash-consed arena — the in-crate witness
//! for the `Holes` routing note ("handle IRs: hand-write `Recursive`").
//! A handle DENOTES its child, so it implements exactly the two traits a
//! handle honestly CAN — `Hole` (shape) and `HolesIn` (access through
//! the arena) — and none of the owning family (`Holes`/`HolesMove`/
//! `HolesWrap`), whose obligations are unrepresentable for it.
//! `Layer<'a, T>` borrows payloads from the arena, `unzip` is
//! shape-only, and [`Pair`] rides for free.
use affine_cat::cata::{FoldAlg, Hole, HolesIn, Recursive, ScopeGuard};
use core::ops::ControlFlow;

/// the handle: a child is an index; the nodes live in the arena
#[derive(Clone, Copy)]
pub struct Rel(pub u32);

pub enum RelNode {
    Scan(u32),
    Filter(Rel, u32),
    Union(Rel, Rel),
    /// a binder: its child folds one scope deeper
    Exists(Rel),
}

pub struct Arena(pub Vec<RelNode>);

impl Arena {
    fn node(&self, r: Rel) -> &RelNode {
        &self.0[r.0 as usize]
    }
}

// the shipped vocabulary: shape from `Hole`, ACCESS through the arena
// from `HolesIn` — the two halves a handle CAN honestly provide.
// (`Holes`/`HolesMove`/`HolesWrap` stay unimplemented and unimplementable.)
impl Hole<RelNode> for Rel {
    type Mapped<U> = U;
    fn unzip_with<P, A, B>(m: P, split: &mut dyn FnMut(P) -> (A, B)) -> (A, B) {
        split(m)
    }
}
impl HolesIn<RelNode, Arena> for Rel {
    fn map_ref_in<U>(&self, ar: &Arena, f: &mut dyn FnMut(&RelNode) -> U) -> U {
        f(ar.node(*self))
    }
    fn map_ref_until_in<B, U>(
        &self,
        ar: &Arena,
        f: &mut dyn FnMut(&RelNode) -> ControlFlow<B, U>,
    ) -> ControlFlow<B, U> {
        f(ar.node(*self))
    }
}

/// the borrowed view the fold walks: arena + root, `Copy`-cheap
#[derive(Clone, Copy)]
pub struct At<'ar> {
    ar: &'ar Arena,
    root: Rel,
}

/// the hand-written layer: payloads borrowed FROM THE ARENA
pub enum RelLayer<'a, T> {
    Scan(&'a u32),
    Filter(T, &'a u32),
    Union(T, T),
    Exists(T),
}

impl<'ar> Recursive for At<'ar> {
    type Layer<'a, T>
        = RelLayer<'a, T>
    where
        Self: 'a;
    // shape-only, arena-free — the honest half of the Hole story, which
    // is exactly the half a handle CAN provide
    fn unzip<'a, A, B>(l: RelLayer<'a, (A, B)>) -> (RelLayer<'a, A>, RelLayer<'a, B>)
    where
        Self: 'a, // the E0195 note on the trait: restate this bound
    {
        match l {
            RelLayer::Scan(t) => (RelLayer::Scan(t), RelLayer::Scan(t)),
            RelLayer::Filter((a, b), p) => (RelLayer::Filter(a, p), RelLayer::Filter(b, p)),
            RelLayer::Union((a1, b1), (a2, b2)) => {
                (RelLayer::Union(a1, a2), RelLayer::Union(b1, b2))
            }
            RelLayer::Exists((a, b)) => (RelLayer::Exists(a), RelLayer::Exists(b)),
        }
    }
}

/// the hand-written driver: ten lines, and the arena is just a parameter
fn cata<'ar, A>(at: At<'ar>, alg: &A) -> A::Out
where
    A: FoldAlg<At<'ar>, ()>,
{
    // access goes through the shipped trait: the handle reaches its
    // node via `map_ref_in(ar, ...)` — no ambient state, no `Holes`
    at.root.map_ref_in(at.ar, &mut |node| {
        let layer = match node {
            RelNode::Scan(t) => RelLayer::Scan(t),
            RelNode::Filter(r, p) => RelLayer::Filter(
                cata(
                    At {
                        ar: at.ar,
                        root: *r,
                    },
                    alg,
                ),
                p,
            ),
            RelNode::Union(a, b) => RelLayer::Union(
                cata(
                    At {
                        ar: at.ar,
                        root: *a,
                    },
                    alg,
                ),
                cata(
                    At {
                        ar: at.ar,
                        root: *b,
                    },
                    alg,
                ),
            ),
            RelNode::Exists(r) => RelLayer::Exists(cata(
                At {
                    ar: at.ar,
                    root: *r,
                },
                alg,
            )),
        };
        alg.reduce(&(), layer)
    })
}

/// the SCOPED driver: same shape, `ScopeGuard` bracketing the binder —
/// the other half of the routing note's claim, witnessed in-crate.
/// The env is a bare `Vec<u32>` via the blanket [`ScopedEnv`] impl.
fn cata_in<'ar, A>(at: At<'ar>, env: &mut Vec<u32>, alg: &A) -> A::Out
where
    A: FoldAlg<At<'ar>, Vec<u32>>,
{
    let layer = match at.ar.node(at.root) {
        RelNode::Scan(t) => RelLayer::Scan(t),
        RelNode::Filter(r, p) => RelLayer::Filter(
            cata_in(
                At {
                    ar: at.ar,
                    root: *r,
                },
                env,
                alg,
            ),
            p,
        ),
        RelNode::Union(a, b) => RelLayer::Union(
            cata_in(
                At {
                    ar: at.ar,
                    root: *a,
                },
                env,
                alg,
            ),
            cata_in(
                At {
                    ar: at.ar,
                    root: *b,
                },
                env,
                alg,
            ),
        ),
        RelNode::Exists(r) => RelLayer::Exists({
            // ORDER IS THE CONTRACT: snapshot FIRST, then mutate. The
            // first draft pushed before arming the guard — the snapshot
            // recorded the grown stack and the binding leaked (caught by
            // the balance assert below). `ScopedEnvWith::enter_with`
            // exists to package exactly this ordering atomically.
            let saved = affine_cat::cata::ScopedEnv::enter(env);
            env.push(0); // the binding enters INSIDE the frame
            let mut g = ScopeGuard::from_frame(&mut *env, saved);
            cata_in(
                At {
                    ar: at.ar,
                    root: *r,
                },
                g.env(),
                alg,
            )
        }),
    };
    alg.reduce(&*env, layer)
}

struct Count;
impl<'ar> FoldAlg<At<'ar>, ()> for Count {
    type Out = usize;
    fn reduce<'a>(&self, _: &(), l: RelLayer<'a, usize>) -> usize
    where
        At<'ar>: 'a,
    {
        match l {
            RelLayer::Scan(_) => 1,
            RelLayer::Filter(n, _) | RelLayer::Exists(n) => n + 1,
            RelLayer::Union(a, b) => a + b + 1,
        }
    }
}

struct Depth;
impl<'ar> FoldAlg<At<'ar>, ()> for Depth {
    type Out = usize;
    fn reduce<'a>(&self, _: &(), l: RelLayer<'a, usize>) -> usize
    where
        At<'ar>: 'a,
    {
        match l {
            RelLayer::Scan(_) => 1,
            RelLayer::Filter(d, _) | RelLayer::Exists(d) => d + 1,
            RelLayer::Union(a, b) => a.max(b) + 1,
        }
    }
}

/// binder depth at each Scan, via the env — reads the scope stack
struct MaxBinders;
impl<'ar> FoldAlg<At<'ar>, Vec<u32>> for MaxBinders {
    type Out = usize;
    fn reduce<'a>(&self, env: &Vec<u32>, l: RelLayer<'a, usize>) -> usize
    where
        At<'ar>: 'a,
    {
        match l {
            RelLayer::Scan(_) => env.len(),
            RelLayer::Filter(n, _) | RelLayer::Exists(n) => n,
            RelLayer::Union(a, b) => a.max(b),
        }
    }
}

fn main() {
    // hash-consed by hand: Scan shared by both Union arms
    let ar = Arena(vec![
        RelNode::Scan(0),               // 0
        RelNode::Filter(Rel(0), 7),     // 1  (shares node 0)
        RelNode::Union(Rel(1), Rel(0)), // 2 (shares node 0 again)
    ]);
    let at = At {
        ar: &ar,
        root: Rel(2),
    };

    // one pass, two algebras — Pair works because unzip is shape-only
    let (count, depth) = cata(at, &Count.pair(Depth));
    assert_eq!(count, 4, "shared node counted per PATH (the O(paths) doc)");
    assert_eq!(depth, 3);

    // the scoped half: exists[ union(filter(scan), exists[scan]) ]
    let ar2 = Arena(vec![
        RelNode::Scan(0),               // 0
        RelNode::Filter(Rel(0), 7),     // 1
        RelNode::Exists(Rel(0)),        // 2  (inner binder, shares 0)
        RelNode::Union(Rel(1), Rel(2)), // 3
        RelNode::Exists(Rel(3)),        // 4  (outer binder)
    ]);
    let mut env: Vec<u32> = vec![];
    let deepest = cata_in(
        At {
            ar: &ar2,
            root: Rel(4),
        },
        &mut env,
        &MaxBinders,
    );
    assert_eq!(deepest, 2, "inner Scan sees two binders, outer path one");
    assert!(env.is_empty(), "balanced — the guard, over an arena");

    println!(
        "arena cata: count={count} depth={depth} binders={deepest}  |  \
         owning family absent, HolesIn present  |  guard balanced"
    );
}
