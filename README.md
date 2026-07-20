# affine-cat

Category theory native to Rust's affine, monoidal reality: lawful
duplication, graded functors, box-free applicatives, Moore-machine wiring,
mutation-as-lens, and law-first recursion schemes (derive + Agda-mechanized
driver disciplines).

## The thesis

Rust's value semantics form an affine symmetric monoidal category, not a
cartesian closed one. That is not a limitation to paper over — it is a
structure to build in. Concretely:

- **Dropping is free** (weakening): any value may be discarded. The
  codiagonal is unconditional — a `match` moves a value into one branch,
  copying nothing.
- **Copying is not** (no free contraction): the diagonal `A -> (A, A)` is
  *gated*, and this crate makes the gate a trait. A bound like
  `A: Comonoid` claims "this algorithm needs the diagonal", not "this type
  is cheap". `Unaliased` is the strong form: the two halves never observe
  each other.

Every module places that toll exactly where its grade forces it, and
nowhere else. Combinators that don't copy carry no copy bounds; the one
combinator per grade that does (`DuplicateTo`, `DuplicateToMachine`,
`base::Pair`) wears the gate visibly; and the fold grade (`cata`) dodges
the toll entirely by lending layers by reference.

## Quick start

One pass over a byte stream, two answers, no `Clone`:

```rust
use affine_cat::base::{Count, Pair};
use affine_cat::data::{accumulate, ArrayWindows};

let text = b"mississippi";
let Pair(bigrams, count): Pair<Vec<[u8; 2]>, Count> =
    accumulate(&mut ArrayWindows::<2>, &text[..]);
assert_eq!(count.0, 10);
assert_eq!(bigrams[0], [b'm', b'i']);
```

Pipelines are zero-sized values that fuse by construction:

```rust
use affine_cat::base::{Embed, Piece};

let classify =
    Embed(|status: u16| status / 100).link(Embed(|class: u16| matches!(class, 4 | 5)));
assert!(classify.run(404));
assert_eq!(core::mem::size_of_val(&classify), 0); // fused away
```

A Moore machine denotes a function from input histories — and
`run_history` is that denotation, executable:

```rust
use affine_cat::machines::{run_history, Machine};

struct MaxSeen(u64);
impl Machine for MaxSeen {
    type In = u64;
    type Out = u64;
    fn out(&self) -> u64 {
        self.0
    }
    fn update(&mut self, x: u64) {
        self.0 = self.0.max(x)
    }
}
assert_eq!(run_history(&mut MaxSeen(0), [3, 9, 4]), 9);
```

Recursion schemes over your own trees, via derive — one traversal, two
algebras, paired for free because layers are lent, not copied:

```rust
use affine_cat::cata::{pair, FoldAlg};
use affine_cat_derive::Recursive;

#[derive(Recursive)]
enum Expr {
    Lit(i64),
    Add(Box<Expr>, Box<Expr>),
}

struct Eval;
impl FoldAlg<Expr, ()> for Eval {
    type Out = i64;
    fn reduce<'a>(&self, _: &(), l: ExprLayer<'a, i64>) -> i64
    where
        Expr: 'a,
    {
        match l {
            ExprLayer::Lit(n) => *n,
            ExprLayer::Add(a, b) => a + b,
        }
    }
}

struct Depth;
impl FoldAlg<Expr, ()> for Depth {
    type Out = usize;
    fn reduce<'a>(&self, _: &(), l: ExprLayer<'a, usize>) -> usize
    where
        Expr: 'a,
    {
        match l {
            ExprLayer::Lit(_) => 0,
            ExprLayer::Add(a, b) => a.max(b) + 1,
        }
    }
}

let e = Expr::Add(
    Box::new(Expr::Lit(2)),
    Box::new(Expr::Add(Box::new(Expr::Lit(3)), Box::new(Expr::Lit(4)))),
);
// one traversal, two algebras — no Clone bound anywhere
let (val, depth) = e.fold(&(), &pair(&Eval, &Depth));
assert_eq!((val, depth), (9, 2));
```

Every fenced block above is a test in `tests/readme.rs`, run verbatim on
every board.

## Module map

| Module | What it is |
|---|---|
| `base` | The affine core: `Comonoid`/`Unaliased` (the gated diagonal), the free pipeline category (`Piece`, `Link`, `DuplicateTo`, `ConsumeResult`, …), `Absorb` sinks, round-trip laws, `lens` |
| `cps` | The same pipeline, push-encoded: environment-threaded stages with early exit; the mutate-XOR-borrow law lives in the signature |
| `data` | Graded functors (`MapMut`/`MapOnce` — closure grade = comonoid requirement on captures), box-free `Zip`/`Pointed`, final-encoding `Visit` |
| `machines` | Moore (`Machine`) and Mealy (`Transducer`) with the embedding law-forced; products, pipes, feedback-as-trace, `Driven` sinks, `run_history` |
| `ringy` | The weight algebra: a `Semiring` tower with `&mut`-native primitives; `bool`, `Tropical`, `Viterbi`, `Gf2`, `Poly` |
| `weighted` | `Sum` (`⊕`) and `Prod` (`⊗`) over machines — `DuplicateToMachine` plus a semiring gate |
| `cata` | Recursion schemes: borrowed and consuming folds via `#[derive(Recursive)]`, scoped envs with Drop-guard balance, absorbing-carrier short-circuits, mutual recursion, codata thunks, arena access (`HolesIn`) |
| `affine-cat-derive` | `#[derive(Recursive)]` and `#[recursive_family]`; the type classifier folds `syn`'s AST with the crate's own `Recursor` |

## Law-first, receipts attached

Claims in this crate come with their witnesses, in three tiers:

- **Mechanized** (`agda/`, seven files, all `--safe`): driver disciplines
  for env-threaded folds — scope balance under absorption and panic,
  fold/machine agreement, pairing laws, two-sorted absorption. Three of
  the generated-code laws were *discovered* by the proofs, not merely
  checked.
- **Witnessed** (`tests/`, `examples/`): every design claim that types can
  express runs in CI; the ones types cannot express run as demonstrations
  in `examples/walls.rs`.
- **Measured** (`benches/`): performance claims are benchmarked before
  they justify design. `benches/dyn_fence.rs` is the standing example —
  it cancelled a planned migration by showing the `dyn` closure in the
  fold hot path is an inlining fence worth 2× on cheap algebras, not a
  cost.

`./ci.sh` is the executable board: tests, examples, crate-wide
zero-warning clippy, a test run **inside the packaged `.crate` artifact**
(what a user actually downloads — the 0.1.0 publish shipped a green board
and a broken download because the board only ever tested the repo), the
Agda corpus, intra-doc links, and the MSRV floor.

## Design conventions

- **Surface earns its place.** Machinery ships when a consumer names it;
  speculative tiers live in comments with restoration recipes (see the
  removed-tiers notes in `ringy` and the `dfa` epitaph in `lib.rs`).
- **Foreclosed alternatives are documented.** Most modules carry
  "Foreclosed" sections recording rejected designs and why — the map of
  where the walls are is part of the product.
- **Absences are priced.** When something is deliberately missing (a
  both-consuming pair, a `try` on the consuming fold path, `HolesMove`
  for shared pointers), the doc at the site says so and says why.
- **Weakening is free up to `Drop`.** "Any value may be dropped" is the
  affine typing rule; `Drop::drop` is user code that runs at the discard.
  The crate's laws quantify over what readouts observe (which drop
  effects cannot touch), and `cata::ScopeGuard` deliberately *spends* the
  effect — its panic-path balancing law lives in `Drop`. See the Walls
  section in the crate docs.

## MSRV and features

MSRV **1.80**, witnessed in both directions (builds on 1.80, fails on
1.79) for the **library**; the derive crate's floor floats with `syn`.
`no_std` + `alloc` by default; the `std` feature adds threaded
`par_update`, the `Hasher` adapter, the `HashMap` sink, and IP-address
`Unaliased` leaves.

## Status

`0.2.0`, pre-release, no downstream users yet: breaking changes are
possible and this is the cheapest they will ever be. The consumer feedback
loop is live — the `cata` module's current shape owes several corrections
to a downstream compiler front-end, credited in the docs where their
findings landed.
