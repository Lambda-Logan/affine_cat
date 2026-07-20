#![no_std]
#![warn(missing_docs)]
#![cfg_attr(docsrs, feature(doc_cfg))]
//! (no_std + alloc; the `std` feature adds threaded `par_update`, the
//! `Hasher` adapter, the `HashMap` sink, and the IP-address `Unaliased`
//! leaves.)
//!
//! # affine-cat
//!
//! Category theory native to Rust's actual category, not ported from Hask.
//!
//! Rust's types form (approximately) a symmetric monoidal category with
//! tensor `(A, B)`, unit `()`, **weakening for free** (any value may be
//! dropped) and **no free contraction** (no diagonal `A -> (A, A)`): an
//! *affine* category. Libraries that port CCC-shaped definitions leak the
//! mismatch as ad-hoc `Clone` bounds and boxed exponentials. This crate
//! instead makes the missing structure explicit and states the laws that
//! Rust's ownership discipline proves for you.
//!
//! Three principles:
//! 1. **Contraction is structure** ([`base::Comonoid`] for lawful
//!    duplication, [`base::Unaliased`] for *independent* duplication), never a
//!    std trait leaked into signatures.
//! 2. **Closure bounds are grades** (`FnOnce ⊇ FnMut ⊇ Fn`): each trait
//!    takes the weakest grade its instances truly need
//!    ([`data::MapOnce`] / [`data::MapMut`]).
//! 3. **Mutation is lawful under uniqueness**: `fn(&mut A)` ≅ `A -> A` as
//!    a function on values whenever the reference is unique — which `&mut`
//!    proves statically. Formal backing: the RustHorn / RustHornBelt /
//!    Creusot line models `&mut T` as a (current, final-prophesied) pair —
//!    the lens presentation — and translates Rust to pure functional
//!    programs on that basis.
//!
//! ## Module map
//! * [`base`] — shared kernel: duplication, independence, free pipeline
//!   morphisms ([`base::Link`], [`base::OnFirst`], [`base::DuplicateTo`]),
//!   lenses-by-reborrow.
//! * [`data`] — polynomials as *containers*: graded functors, lawful
//!   in-place, monoidal `Zip`, and both stream encodings with the
//!   final/initial boundary priced.
//! * [`machines`] — polynomials as *interfaces*: Moore primitive, Mealy
//!   adapters, `Par`/`Pipe`/`Feedback` wiring with laws by
//!   construction.
//!   (A Boolean recognizer algebra over `Machine<Out = bool>` is just the
//!   `S = bool` instance of [`weighted`] — union is `Sum`, intersection is
//!   `Prod` — so it is not a separate module.)
//! * [`cps`] — the push-encoded face of [`base::Piece`]: outputs handed to a
//!   continuation (borrowed, `0..n` per input) with an ambient mutable
//!   environment threaded through it. One generic fusing trait
//!   ([`cps::Piece`]) plus its erased object-safe view ([`cps::PieceDyn`]);
//!   the mutate-XOR-borrow discipline is enforced by the continuation's
//!   signature. Promoted from the XML-filter example when a second domain
//!   (compiler pass pipelines over an arena) wanted the same shape.
//! * [`ringy`] — the weight algebra beneath [`weighted`]: a tower from
//!   [`ringy::Semiring`] (the tier the shipped combinators demand) up to
//!   [`ringy::Ring`]; higher strata are documented requirements, gated
//!   into surface only with the operation that needs them. A Boolean
//!   recognizer is its [`bool`] instance.
//! * [`weighted`] — the two products over machines: [`weighted::Sum`]
//!   (`⊕`, union at `bool`) and [`weighted::Prod`] (`⊗`, intersection),
//!   both `DuplicateToMachine` plus a semiring gate.
//! * [`cata`] — recursion schemes over user-defined trees: borrowed and
//!   consuming folds via `#[derive(Recursive)]`, env-threading with
//!   Drop-guard scoping, absorbing-carrier short-circuits, mutual
//!   recursion, codata thunks, and arena access ([`cata::HolesIn`]).
//!   Law-first: driver disciplines are mechanized in `agda/` (`--safe`)
//!   or witnessed in `tests/witnesses.rs`; the unfixable walls run in
//!   `examples/walls.rs`.
//!
//! The two spines are the two roles of the polynomial-functor picture
//! (positions/directions vs interfaces/dynamics); the seam between them —
//! the composition product ⊳ — is a named wall, below.
//!
//! ## Walls — what this crate cannot say, and why
//! Stated up front because every language port makes concessions; the sin
//! is making them without a receipt.
//!
//! * **No HKT tower.** Expressibility is not the wall — brands
//!   (defunctionalized constructors) encode it, and even functor
//!   composition (⊳ on carriers) compiles on stable. The wall is solver
//!   economics: a concrete type has multiple brand decompositions and the
//!   trait solver cannot see brands at all, so every decomposition is
//!   user-annotated, at every use site. A tower's value is being cheap at
//!   use sites; inverted, it is worth less than std-style duplication
//!   (empirically: arrow-kt ran the experiment to completion and
//!   removed its `Kind` emulation). Independently: Rust would need the
//!   tower *graded* by closure multiplicity — two dimensions no mainstream
//!   system does well. ⊳-*objects* are recoverable later as an additive
//!   `brands` module; composition-product polymorphism is out of scope.
//! * **Zip does not exist over the visitor encoding.** Pairing two
//!   push-streams requires suspending a producer; internal iteration
//!   forfeits exactly that. Zip/gap-shaped combinators live on the
//!   initial side only. (Field observation: creature_feature issue #3.)
//! * **`Unaliased` for `&T` is unnameable on stable** (needs the private
//!   `Freeze`); reference impls are conservatively absent.
//! * **Affine cannot force protocol completion.** Dropping is always
//!   legal, so abandonment of a typestate protocol is statically
//!   invisible; any future `Protocol` module inherits this session-type
//!   wall.
//! * **Weakening is free only up to `Drop` effects.** "Any value may be
//!   dropped" is a *typing* rule; operationally `Drop::drop` is user code
//!   that runs at the discard, so weakening is unobservable only for
//!   types with trivial drop glue. The crate both spends and prices this:
//!   [`cata::ScopeGuard`] does its balancing work *in* `Drop` (the
//!   panic-path law depends on the effect firing), while the pipeline
//!   laws' "discarding is free" claims are semantic statements about
//!   values, exact for `Copy`-ish leaves and true-up-to-drop-effects in
//!   general. An affine category with observable weakening is where the
//!   theory honestly lands; the laws quantify over what `out`/`run`
//!   observe, which drop effects cannot touch.
//! * **In-place allocation reuse is behavior, not contract** — it rides
//!   on unstable std specialization internals; this crate states the
//!   value-level law and pins the reuse with a canary test only.
//!
//! ## Deferred — named, scoped, and additive
//! Every item here is a pure addition when taken up; none is blocked, and
//! none silently constrains today's API:
//! * **Tee/Wye** (demand-driven two-input machines): the initial-encoding
//!   fix to the visitor-zip wall — the machine's readout includes which
//!   input it wants next (readiness, in async terms; Kmett's `Tee`, in
//!   machines terms). The largest deferred design; unblocks gap-grams
//!   over machines.
//! * **Plan/builder surface** (v1.0): a macro compiling await/yield-style
//!   plans to the combinator types — the async/await arc and Kmett's
//!   `construct`, converging.
//! * **`traverse`**: concrete `try_map` family and/or brand-generic
//!   `traverse::<F, _, _>` (witnessed viable; pays per-call annotation).
//! * ~~`cata`/recursion schemes~~ — SHIPPED (see the module map above).
//!   Of historical note: the deferred sketch's `fold_with(alg: impl
//!   Piece<...>)` signature was rejected on port — a downstream compiler
//!   showed the env must reach the algebra, and the mechanization then
//!   showed it must reach it by `&` (the banana-as-signature story told
//!   in [`cata`]'s docs).
//! * **generic `lift_a2`/`zip_with`**: blocked only on Map-bound plumbing
//!   over `Zipped`.
//! * **`brands` module**: ⊳-objects (functor composition) on stable via
//!   defunctionalized constructors; opt-in, annotation-taxed.
//! * **`LendingMoore`**: GAT outputs; viable today at a `'static` +
//!   HRTB-ceremony tax (rust-lang/rust#87479); blanket-embeds the owned
//!   trait when added.
//! * **async-machine tier** (`Pin<&mut Self>` stepping): the
//!   address-sensitive fragment of [`machines::Machine`]. Futures are its
//!   motivating instance — a future is a machine whose `update` requires
//!   pinning (the reason `Future::poll` takes `Pin<&mut Self>`), so it
//!   cannot implement the `Unpin` machine trait and belongs here. Also
//!   captures `tower::Service` (output is a future). The current owned-`&mut`
//!   trait is the `Unpin` fragment; this is purely additive beside it.
//! * **`Protocol`** (typestate/dependent fragment): positions as
//!   typestates; inherits the session-type wall that affine Rust cannot
//!   force protocol completion.
//! * **Creusot/Pearlite annotations**: laws are kept in one greppable doc
//!   format so mechanization stays mechanical.
//!
//! ## Toolchain
//! MSRV **1.80** (`LazyCell` rims; all laws and tests witnessed there —
//! the recorded floor is the LIBRARY's; the derive's floats with `syn`).
//! `./ci.sh` is the executable board: tests, examples, clippy on the
//! contributed surface, the Agda corpus, intra-doc links, and the MSRV
//! floor, one script.

extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

pub mod base;
pub mod cata;
pub mod cps;
pub mod data;
pub mod machines;
// The `dfa` module (Boolean recognizer algebra: And/Or/Not/Xor/Diff over
// `Machine<Out = bool>`) was removed: for a fixed check, `&&`/`||` on plain
// predicates beat it, and for real matching the `regex` crate wins. Its one
// genuine idea — that a DFA is a Moore machine and the Boolean operations are
// readout logic over the product automaton — survives as the `S = bool`
// instance of `weighted` (`weighted::Sum` = union, `weighted::Prod` =
// intersection over `ringy::Semiring` weights).
pub mod ringy;
pub mod weighted;
