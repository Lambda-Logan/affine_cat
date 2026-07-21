//! # `machines` — polynomials as interfaces
//!
//! `&mut` state machines read as coalgebras: a Moore machine — readout
//! `S -> B`, update `S × A -> S` — is a lens `Sy^S -> By^A`, i.e. a
//! morphism of monomial polynomial functors (Niu–Spivak). Rust fuses the
//! get/put pair into methods on `&mut self`, and uniqueness is what makes
//! the mutation lawful (RustHorn's pair-of-current-and-final model).
//!
//! **Moore is the primitive; Mealy is the adapter** (decided): the readout
//! needs no input, so outputs are computable *before* inputs arrive, which
//! is exactly what makes feedback wiring well-defined — read phase, then
//! update phase. A Mealy primitive makes every feedback wire an algebraic
//! loop. (Corroborating instinct from prior art: creature_feature's
//! `Accumulates` — `accum_token(&mut State, Token)` + `finish` — is the
//! Moore shape; Mealy appears nowhere in that crate.)

// ================================ Moore ================================

/// The primitive: a Moore coalgebra. `out` is the readout `S -> B`,
/// `update` the dynamics `S × A -> S` — equivalently, a coalgebra of the
/// monomial `By^A`, i.e. a lens `Sy^S -> By^A`.
///
/// ```
/// use affine_cat::machines::{Machine, run_history};
/// struct Sum(u64);
/// impl Machine for Sum {
///     type In = u64;
///     type Out = u64;
///     fn out(&self) -> u64 { self.0 }
///     fn update(&mut self, x: u64) { self.0 += x; }
/// }
/// // A Moore machine denotes a function from input histories:
/// assert_eq!(run_history(&mut Sum(0), [1, 2, 3]), 6);
/// ```
///
/// # Laws
/// * **`out` is pure readout**: calling `out` any number of times, in any
///   interleaving with other `&self` access, returns equal values and
///   mutates nothing (`&self` enforces the second half; the first is the
///   impl's obligation).
/// * Composite machines built from [`Par`], [`Pipe`], [`Feedback`]
///   satisfy their stepping equations **by construction** — the free
///   structure is interpreted, not re-proven.
///
/// # Foreclosed primitives (each tested or sourced, none merely vibed)
/// * **Mealy as primitive** — feedback becomes an algebraic loop needing
///   an explicit register everywhere; Moore gets it free. Mealy remains
///   fully available: see [`Transducer`] and the blanket embedding.
/// * **GAT-lending signatures** (`type Out<'a>`) — witnessed working on
///   stable, at the price of mandatory `where Self: 'a` bounds and, via
///   the HRTB equality that sequential composition needs, a forced
///   `'static` on composed machines (the rust-lang/rust#87479
///   interaction). Reserved as an *additive* future trait
///   (`LendingMoore`), with the owned trait embedding into it blanketly.
/// * **Input-parameterized lending** (lifetime in the trait parameter,
///   creature_feature's pre-GAT technique) — dodges both taxes above, but
///   its cost is a quadratic impl surface across input carriers, paid in
///   macros; and its production validation is thin.
///
/// # Future directions
/// * `LendingMoore` (above); `Protocol` — the dependent/typestate
///   fragment, where positions are typestates and directions are
///   per-state input types. Standing wall inherited from session-type
///   theory: protocols classically need *linearity*, Rust is *affine* —
///   dropping is always allowed, so protocol **abandonment is statically
///   invisible** (`#[must_use]` is a lint, not a type). Any `Protocol`
///   design must carry that wall in its docs.
/// * async machines: an instance of the lending question plus an effect,
///   not a new primitive.
///
/// **Object-safe** with associated types fixed (`&mut dyn Machine<In=…,
/// Out=…>`): the trait has no generic methods. `MapMut`/`Zip`/`Visit`, by
/// contrast, are *not* object-safe (generic method + GAT) — runtime
/// polymorphism there needs an erasing wrapper.
///
/// # Unpin precondition (the boundary of the mutation law)
/// This is the **`Unpin` fragment** of the machine concept. The crate's
/// central law — mutation through a unique `&mut` is a pure function on
/// values (RustHorn's current/final prophecy pair) — assumes the state is
/// *not* address-sensitive: `update(&mut self)` is free to move the
/// interior, which a self-referential state (the shape compiler-generated
/// async state machines have) cannot tolerate. Every state here is
/// implicitly `Unpin`, which all concrete stack/heap data satisfies.
///
/// The address-sensitive case — stepping via `poll(Pin<&mut Self>, …)`,
/// which is exactly why `Future::poll` has that signature — is the
/// deferred async-machine tier, not a missing impl. Futures are the
/// motivating non-instance: a future is a machine whose `update` *requires*
/// `Pin`, so it lives in that tier rather than implementing this trait.
pub trait Machine {
    /// Input (direction) type.
    type In;
    /// Output (readout) type.
    type Out;
    /// Readout `S -> B`. Must not mutate; must be stable between updates.
    fn out(&self) -> Self::Out;
    /// Dynamics `S × A -> S`.
    fn update(&mut self, i: Self::In);

    // --- Provided wiring methods (the `Iterator` form: on the trait,
    // `where Self: Sized`, so `dyn Machine<In = _, Out = _>` is
    // unaffected). Building is lazy; nothing steps until `update`. ---

    /// Sequential wire: `self`'s readout feeds `n`'s update — build
    /// [`Pipe`]. Chains left-to-right: `a.pipe(b).pipe(c)`.
    fn pipe<N: Machine<In = Self::Out>>(self, n: N) -> Pipe<Self, N>
    where
        Self: Sized,
    {
        Pipe(self, n)
    }
    /// Parallel juxtaposition (the tensor `⊗`) — build [`Par`].
    fn par<N: Machine>(self, n: N) -> Par<Self, N>
    where
        Self: Sized,
    {
        Par(self, n)
    }
    /// Close the feedback wire — build [`Feedback`] (defined when
    /// `Self::In = (I, F)` and `Self::Out = (O, F)`).
    fn feedback(self) -> Feedback<Self>
    where
        Self: Sized,
    {
        Feedback(self)
    }
    /// The Moore product: both machines see every input — build
    /// [`DuplicateToMachine`] (pays [`crate::base::Unaliased`] at use).
    ///
    /// The `Unaliased` bill shapes pipelines over borrowed token groups:
    /// `&[T]` windows are not `Unaliased` (the `Freeze` wall, see
    /// [`crate::base::Unaliased`]), so the product cannot sit downstream
    /// of a borrowing windower. The discipline that recovers every such
    /// pipeline: put the diagonal **before** the borrow — duplicate the
    /// scalar tokens (all `Unaliased` leaves), window on each leg after.
    fn duplicate_to<N>(self, n: N) -> DuplicateToMachine<Self, N>
    where
        Self: Sized,
    {
        DuplicateToMachine(self, n)
    }
    /// Drive with a whole history and read out — the corepresentability
    /// eliminator as a method (std's `collect` position; also the free
    /// function [`run_history`]).
    fn run_history<I: IntoIterator<Item = Self::In>>(&mut self, history: I) -> Self::Out
    where
        Self: Sized,
    {
        for i in history {
            self.update(i);
        }
        self.out()
    }
    /// The **running readout**: lazily yield `out()` before any input and
    /// after every `update` — `history.len() + 1` items, the last equal
    /// to [`Machine::run_history`] over the same history (mechanized:
    /// `scan-last` in `MooreComonad.agda`).
    ///
    /// Comonadically, that sentence is the entire method: a Moore
    /// machine is a comonad (extract = `out`, duplicate = relabel each
    /// state by its own subtree — laws `counit-l`/`counit-r`/`coassoc`
    /// in `MooreComonad.agda`), and `scan` is the extract-image of the
    /// duplicate orbit (`dup-tracks`). The raw `duplicate` is *not*
    /// exposed: in Rust it would be a per-step machine clone — an
    /// allocation the signature does not admit to — so the crate ships
    /// the part of it that is useful and leaves the rest in the model.
    fn scan<I: IntoIterator<Item = Self::In>>(&mut self, history: I) -> Scan<'_, Self, I::IntoIter>
    where
        Self: Sized,
    {
        Scan {
            m: self,
            input: history.into_iter(),
            primed: false,
        }
    }
}

// ================================ Mealy ================================

/// The **Mealy machine** (transducer) interface: `step: S × A -> S × B`,
/// output may depend on the incoming input. This is the shape the
/// ecosystem already ships unlabelled — `Iterator::next(&mut self)`,
/// `tower::Service::call` — so it stays first-class here, as the
/// *transducer* face.
pub trait Transducer {
    /// Input type.
    type In;
    /// Output type.
    type Out;
    /// Step: consume an input, mutate state, produce an output.
    fn step(&mut self, i: Self::In) -> Self::Out;

    // --- Provided wiring methods (`where Self: Sized`; `dyn Transducer`
    // and the [`ByRef`] path are unaffected). ---

    /// Mealy→Moore: readout is the previous step's output — build
    /// [`Delay`] seeded with `initial`.
    fn delay(self, initial: Self::Out) -> Delay<Self>
    where
        Self: Sized,
    {
        Delay {
            m: self,
            last: initial,
        }
    }
    /// Step-and-discard sink — build [`Driven`] (an
    /// [`crate::base::Absorb`]).
    fn driven(self) -> Driven<Self>
    where
        Self: Sized,
    {
        Driven(self)
    }
    /// Contravariant input action (profunctor `lmap`) — build [`Premap`].
    fn premap<A, F: FnMut(A) -> Self::In>(self, f: F) -> Premap<A, F, Self>
    where
        Self: Sized,
    {
        Premap(f, self, core::marker::PhantomData)
    }
    /// Covariant output action (profunctor `rmap`) — build [`Postmap`].
    fn postmap<B, G: FnMut(Self::Out) -> B>(self, g: G) -> Postmap<Self, G>
    where
        Self: Sized,
    {
        Postmap(self, g)
    }
    /// Strong on the first component — build [`OnFirstTransducer`]. The
    /// passenger type `C` binds at the use site.
    fn on_first<C>(self) -> OnFirstTransducer<C, Self>
    where
        Self: Sized,
    {
        OnFirstTransducer(self, core::marker::PhantomData)
    }
    /// Strong on the second component — build [`OnSecondTransducer`].
    fn on_second<C>(self) -> OnSecondTransducer<C, Self>
    where
        Self: Sized,
    {
        OnSecondTransducer(self, core::marker::PhantomData)
    }
    /// Choice on `Ok` — build [`MapOkTransducer`].
    fn on_ok<E>(self) -> MapOkTransducer<E, Self>
    where
        Self: Sized,
    {
        MapOkTransducer(self, core::marker::PhantomData)
    }
    /// Choice on `Err` — build [`MapErrTransducer`].
    fn on_err<O>(self) -> MapErrTransducer<O, Self>
    where
        Self: Sized,
    {
        MapErrTransducer(self, core::marker::PhantomData)
    }
}

/// **Fanout at transducer grade** `⟨m, n⟩` — build [`DuplicateToTransducer`]:
/// both step on a copy of every input (pays [`crate::base::Unaliased`]).
/// A free function for the symmetric reading (the `std::iter::zip`
/// precedent; see [`crate::base::alongside`]).
pub fn duplicate_to_transducer<M, N>(m: M, n: N) -> DuplicateToTransducer<M, N>
where
    M: Transducer,
    N: Transducer<In = M::In>,
{
    DuplicateToTransducer(m, n)
}

/// **Fanin** `[m, n]` at transducer grade — build
/// [`ConsumeResultTransducer`]: case-analyse each `Result` input into one
/// of two stateful machines. Free function, symmetric reading.
pub fn consume_result_transducer<M, N>(m: M, n: N) -> ConsumeResultTransducer<M, N>
where
    M: Transducer,
    N: Transducer<Out = M::Out>,
{
    ConsumeResultTransducer(m, n)
}

/// A mutable borrow of a machine is a machine — wire without moving.
impl<M: Machine> Machine for &mut M {
    type In = M::In;
    type Out = M::Out;
    fn out(&self) -> M::Out {
        (**self).out()
    }
    fn update(&mut self, i: M::In) {
        (**self).update(i)
    }
}

// Note: `&mut M: Transducer` is left out — it would overlap the
// `Moore ⊂ Mealy` blanket (`&mut M` where `M: Machine` matches both). The
// `&mut M: Machine` impl above already yields a transducer via that
// embedding, so borrow-stepping is available without the conflicting impl.
/// The canonical embedding Moore ⊂ Mealy: `step = update; out`.
///
/// # Foreclosure
/// A blanket impl is semver-permanent and prevents any type from
/// implementing the primitive and a *different* `Transducer` by hand. Accepted
/// because the embedding is law-forced — any other `Transducer` on a Moore
/// carrier would violate one of the two structures — and because the
/// alternative (a wrapper type) taxes every call site forever to protect
/// a case the laws already exclude.
impl<M: Machine> Transducer for M {
    type In = M::In;
    type Out = M::Out;
    fn step(&mut self, i: Self::In) -> Self::Out {
        self.update(i);
        self.out()
    }
}

/// The classical **Mealy→Moore translation**: a transducer becomes a
/// machine whose readout is the *previous* step's output — the state is
/// enlarged by one register, the DSP/FRP *delay* (unit register, `z⁻¹`).
/// `Out: Clone` is **law-forced**, not incidental: `out` must be a
/// repeatable `&self` readout, so the register cannot be moved out of. An
/// exchange-based (`mem::replace`) delay is clone-free but forfeits
/// repeatable readout — i.e. it is not a Moore machine.
#[must_use = "a machine does nothing until stepped; an unstepped machine is usually a dropped computation"]
pub struct Delay<M: Transducer> {
    /// The wrapped transducer.
    m: M,
    /// The registered previous output (the delay register).
    pub last: M::Out,
}

impl<M: Transducer> Machine for Delay<M>
where
    M::Out: Clone,
{
    type In = M::In;
    type Out = M::Out;
    fn out(&self) -> M::Out {
        self.last.clone()
    }
    fn update(&mut self, i: M::In) {
        self.last = self.m.step(i);
    }
}

/// Adapts any [`core::hash::Hasher`] into a Moore [`Machine`]: `write` is
/// the update, `finish` the readout. `std`-gated because the common hasher
/// implementations live in `std`. Input is per-byte (`In = u8`); a
/// slice-input variant would need the borrowed-input tier.
///
/// This is the archetypal Moore machine — the standard library has shipped
/// one since 1.0 in `Hasher` (accumulate via `&mut self`, read via
/// `&self`), which is the shape [`crate::base::Absorb`] generalizes.
///
/// A blanket `impl<H: Hasher> Machine for H` is avoided: it
/// would foreclose every other `Machine` impl on any `Hasher` type. The
/// newtype is the coherent adapter.
#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
#[derive(Debug, Clone, Default)]
pub struct Hashing<H>(pub H);

#[cfg(feature = "std")]
impl<H: std::hash::Hasher> Machine for Hashing<H> {
    type In = u8;
    type Out = u64;
    fn out(&self) -> u64 {
        self.0.finish()
    }
    fn update(&mut self, b: u8) {
        self.0.write(&[b]);
    }
}

/// A data-driven Moore machine: the transition is a flat-array lookup rather
/// than a `match` or closure. This is the representation fast DFA engines use
/// (`next_state = transitions[state * stride + symbol]`, per the
/// aho-corasick / regex-automata design) — one array load per symbol instead
/// of a branchy dispatch the optimizer must lower.
///
/// It carries the crate's structural insight (it is an ordinary [`Machine`],
/// composes with every combinator, and `run_history` is its law harness)
/// while adopting the leaf-level representation that makes automata fast: the
/// *structure* stays categorical, the *state* becomes an index into a table.
///
/// The tables are borrowed (`&'t`), so the machine owns no automaton and
/// works in `no_std` — build the table once (offline, or from a compiler
/// pass), then run many cheap machines over it.
///
/// # Panics
/// Never, on well-formed tables: see the `SAFETY(panic-free)` note on
/// [`TableMachine::update`]. Malformed tables are **unrepresentable**: the
/// validating [`TableMachine::new`] is the only constructor (fields are
/// private),
/// so every constructed machine satisfies the shape invariant and `update`
/// cannot index out of bounds — a malformed-table panic class is excluded
/// by construction, not documented around.
#[derive(Debug, Clone, Copy)]
pub struct TableMachine<'t> {
    /// Row-major transition table, length `nstates * stride`.
    transitions: &'t [u32],
    /// Accepting flag per state, length `nstates`.
    accepting: &'t [bool],
    /// Alphabet size (row width). `256` for a full byte alphabet;
    /// smaller with an equivalence-class map applied to inputs first.
    stride: usize,
    /// Current state id.
    state: u32,
}

impl<'t> Machine for TableMachine<'t> {
    type In = u8;
    type Out = bool;
    fn out(&self) -> bool {
        self.accepting[self.state as usize]
    }
    fn update(&mut self, symbol: u8) {
        // SAFETY(panic-free): `new` validated the table shape — every
        // transition target `< nstates` and `transitions.len() == nstates *
        // stride` — so `state * stride + symbol < transitions.len()` when
        // `symbol < stride`; a `symbol >= stride` (caller fed a raw byte to
        // a compressed-alphabet table) still hits the bounds check, never UB.
        self.state = self.transitions[self.state as usize * self.stride + symbol as usize];
    }
}

impl<'t> TableMachine<'t> {
    /// Build a fresh machine at start state `0`, **validating** the table
    /// shape: `stride > 0`, at least one state, `transitions.len() ==
    /// accepting.len() * stride`, and every transition target a valid
    /// state id. Returns `None` on any violation — the malformed-table
    /// panic class cannot be built through this constructor.
    pub fn new(transitions: &'t [u32], accepting: &'t [bool], stride: usize) -> Option<Self> {
        let nstates = accepting.len();
        let shape_ok = stride > 0
            && nstates > 0
            && transitions.len() == nstates.checked_mul(stride)?
            && transitions.iter().all(|&t| (t as usize) < nstates);
        shape_ok.then_some(TableMachine {
            transitions,
            accepting,
            stride,
            state: 0,
        })
    }

    /// The current state id (read-only; the tables stay private).
    pub fn state(&self) -> u32 {
        self.state
    }
}

// Unbuilt `TableMachine` extensions (purely additive; the shipped machine is
// a correct, minimal fast-transition Moore DFA):
//
// * Premultiplication — the one with real payoff. Store targets already
//   scaled by `stride` at build time so `update` is `transitions[state +
//   symbol]` (one add) instead of `state * stride + symbol` (a multiply per
//   symbol). BurntSushi's aho-corasick/regex-automata hot loop. Add a
//   `premultiplied` constructor + a multiply-free `update`; verify by running
//   the same DFA and asserting identical results.
// * Alphabet compression — a `byte -> class` map shrinking `stride` from 256
//   to the number of distinct byte-classes (fewer, cache-friendlier rows).
//   Currently applied externally by the caller (see the test's `class` fn).
// * Table builder — construct the `&[u32]` slice from a set of
//   `(state, symbol, next)` transitions, instead of by hand. (Purely
//   convenience: `new` checks shape and rejects malformed tables, so
//   the builder would add ergonomics, not safety.)
// * `reset()` — return `state` to 0 for reuse. Minor: `new()` already does
//   this cheaply since the tables are borrowed.
// * Weighted output — generalize `Out = bool` (accepting flag) to `Out = S:
//   ringy::Semiring` via an `&'t [S]` readout table, making it a table-driven
//   *weighted* automaton tied to `weighted`.

// ================================ Wiring ================================

/// Parallel juxtaposition — the monoidal tensor ⊗. State is the product
/// of states; the update is two **disjoint field borrows**, so
/// non-interference between the juxtaposed systems is proved by borrowck
/// rather than assumed. Composite state size is exactly the sum of the
/// parts: the wiring adds zero bytes (witnessed).
/// Parallel composition (process-calculus `P | Q`) — the monoidal
/// **tensor ⊗** of machines.
#[must_use = "a machine does nothing until stepped; an unstepped machine is usually a dropped computation"]
#[derive(Debug, Clone, Copy, Default)]
pub struct Par<M, N>(M, N);

impl<M, N> Par<M, N> {
    /// Borrow the two components (they are stateful; after driving, the
    /// state *is* the result — std's `into_inner` convention).
    pub fn parts(&self) -> (&M, &N) {
        (&self.0, &self.1)
    }
    /// Take the two components back out.
    pub fn into_parts(self) -> (M, N) {
        (self.0, self.1)
    }
}

impl<M: Machine, N: Machine> Machine for Par<M, N> {
    type In = (M::In, N::In);
    type Out = (M::Out, N::Out);
    fn out(&self) -> Self::Out {
        (self.0.out(), self.1.out())
    }
    fn update(&mut self, (a, b): Self::In) {
        self.0.update(a);
        self.1.update(b);
    }
}

impl<M, N> Par<M, N> {
    /// Parallel update across threads (rayon's `par_` prefix convention): the split `&mut` borrows are
    /// `Send`-splittable, so this is `thread::scope` with **zero
    /// synchronization** — disjointness proved by the borrow checker,
    /// not by a lock. (`Send` polices the safety here; `base::Unaliased`
    /// polices *semantics* elsewhere — the two guards are distinct on
    /// purpose.)
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    pub fn par_update(&mut self, (a, b): (M::In, N::In))
    where
        M: Machine + Send,
        N: Machine + Send,
        M::In: Send,
        N::In: Send,
    {
        let Par(m, n) = self;
        std::thread::scope(|s| {
            s.spawn(move || m.update(a));
            s.spawn(move || n.update(b));
        });
    }
}

/// Sequential composition with an internal wire: `M`'s readout feeds
/// `N`'s update. Note it is **Moore-closed**: the composite's readout is
/// `N`'s readout — no input needed — so pipes nest inside feedback loops.
///
/// # Law
/// Associativity of piping holds by construction: `Pipe(Pipe(a,b),c)` and
/// A readout-fold as a [`Machine`]: an [`crate::base::Absorb`]
/// accumulator plus a **non-consuming** readout `Fn(&V) -> B`. This is
/// the Absorb spine's embedding into Moore — the direction opposite
/// [`Driven`], and the two compose as a definitional section–retraction
/// (mechanized: `build-tracks`/`retract` in `FoldMooreRetract.agda`):
/// [`Driven`] forgets exactly the readout, and the dynamics reached are
/// readout-independent. [`Hashing`] is this shape hand-rolled —
/// `Hasher::write` the absorb, `Hasher::finish` the readout.
///
/// The readout grade is `Fn(&V)` by design: callable at every step
/// (so [`Machine::scan`] works on any fold, free), reading through `&` —
/// the comonadic *extract*. The one-shot, state-consuming eliminator is
/// the other grade: [`crate::data::accumulate_finish`], `FnOnce(V)`. A
/// fold whose finish must move its state out is a lawful terminal fold
/// that is not a Moore object — the two forms are not interchangeable.
///
/// The input type `T` rides as a phantom because accumulators absorb at
/// several types (`String` absorbs both `char` and `&str`); the phantom
/// pins the machine's `In` where fields alone could not, keeping the
/// `Machine` impl coherent.
#[must_use = "a machine does nothing until stepped; an unstepped machine is usually a dropped computation"]
pub struct Readout<T, V, F> {
    acc: V,
    out: F,
    _in: core::marker::PhantomData<fn(T)>,
}

/// Free-function form of [`Readout`] — unbounded, inference-transparent
/// (cf. [`crate::cata::pair_owned`] for the pattern's rationale). `T`
/// (the input type) is usually inferred from the machine's use; annotate
/// `readout::<Token, _, _>(…)` when the accumulator absorbs at several
/// types.
pub fn readout<T, V, F>(acc: V, out: F) -> Readout<T, V, F> {
    Readout {
        acc,
        out,
        _in: core::marker::PhantomData,
    }
}

impl<T, V: core::fmt::Debug, F> core::fmt::Debug for Readout<T, V, F> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Readout")
            .field("acc", &self.acc)
            .finish_non_exhaustive()
    }
}

impl<T, V, F> Readout<T, V, F> {
    /// Borrow the accumulator.
    pub fn get(&self) -> &V {
        &self.acc
    }
    /// Take the accumulator back out (std's `into_inner` convention) —
    /// the readout is dropped, which is [`Driven`]'s forgetting made
    /// literal.
    pub fn into_inner(self) -> V {
        self.acc
    }
}

impl<T, B, V, F> Machine for Readout<T, V, F>
where
    V: crate::base::Absorb<T>,
    F: Fn(&V) -> B,
{
    type In = T;
    type Out = B;
    fn out(&self) -> B {
        (self.out)(&self.acc)
    }
    fn update(&mut self, i: T) {
        self.acc.absorb(i);
    }
}

/// Lazy running-readout iterator for [`Machine::scan`]. Yields the
/// initial readout first, then one readout per consumed input — length
/// `n + 1` over an `n`-item history. Borrows the machine (`&mut`), so
/// the machine remains usable, holding its final state, after the scan
/// is dropped or exhausted.
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[derive(Debug)]
pub struct Scan<'m, M, I> {
    m: &'m mut M,
    input: I,
    primed: bool,
}

impl<M: Machine, I: Iterator<Item = M::In>> Iterator for Scan<'_, M, I> {
    type Item = M::Out;
    fn next(&mut self) -> Option<M::Out> {
        if !self.primed {
            self.primed = true;
            return Some(self.m.out());
        }
        let i = self.input.next()?;
        self.m.update(i);
        Some(self.m.out())
    }
}

/// `Pipe(a,Pipe(b,c))` define literally the same update sequence.
#[must_use = "a machine does nothing until stepped; an unstepped machine is usually a dropped computation"]
#[derive(Debug, Clone, Copy, Default)]
pub struct Pipe<M, N>(M, N);

impl<M, N> Pipe<M, N> {
    /// Borrow the two components (they are stateful; after driving, the
    /// state *is* the result — std's `into_inner` convention).
    pub fn parts(&self) -> (&M, &N) {
        (&self.0, &self.1)
    }
    /// Take the two components back out.
    pub fn into_parts(self) -> (M, N) {
        (self.0, self.1)
    }
}

impl<M, N> Machine for Pipe<M, N>
where
    M: Machine,
    N: Machine<In = M::Out>,
{
    type In = M::In;
    type Out = N::Out;
    fn out(&self) -> Self::Out {
        self.1.out()
    }
    fn update(&mut self, i: M::In) {
        self.0.update(i);
        self.1.update(self.0.out());
    }
}

/// Feedback — the combinator that decided the Moore-vs-Mealy fork.
///
/// A machine with interface `In = (I, F)`, `Out = (O, F)` closes into a
/// machine `In = I`, `Out = O` by wiring the `F` output back to the `F`
/// input. Well-defined **because** the readout needs no input: the update
/// is read-phase (`out`), then update-phase — no register, no algebraic
/// loop. (Under a Mealy primitive this combinator is ill-defined without
/// an explicit [`Delay`]; that asymmetry is the fork's
/// resolution in one type.)
///
/// This is the **trace** of the traced monoidal category of machines:
/// [`Feedback`] on the tensor is `Tr`, [`Echo`] is its identity object,
/// and feeding back a wire of unit type recovers the untraced machine.
///
/// The dropped `O` half of the pre-read is affine weakening doing its
/// job: discarding is free.
///
/// # Cost
/// Each `update` calls the inner `out()` once for the read phase, then
/// again (via the composite's own `out`) if the caller reads back. In
/// nested wirings — `Feedback` around a `Pipe` around a `Feedback` — these
/// compose multiplicatively, so a deep loop nest re-reads inner readouts
/// per step. This is sound (readout is pure and repeatable by law) but is
/// the first place a profiler will point; memoizing a readout is a valid
/// local optimization precisely *because* the law guarantees stability.
#[must_use = "a machine does nothing until stepped; an unstepped machine is usually a dropped computation"]
#[derive(Debug, Clone, Copy, Default)]
pub struct Feedback<M>(M);

impl<M> Feedback<M> {
    /// Take the wrapped machine back out (std's `into_inner` convention).
    pub fn into_inner(self) -> M {
        self.0
    }
}

impl<I, O, F, M> Machine for Feedback<M>
where
    M: Machine<In = (I, F), Out = (O, F)>,
{
    type In = I;
    type Out = O;
    fn out(&self) -> O {
        self.0.out().0
    }
    fn update(&mut self, i: I) {
        let (_discard, fb) = self.0.out(); // read phase (weakening on _discard)
        self.0.update((i, fb)); // update phase
    }
}

/// The identity transducer: `In = Out`, output equals input, stateless —
/// the unit of transducer composition. (A Moore identity cannot be
/// stateless: a readout with no input needs a register, so the identity
/// lives on the transducer side, echoing creature_feature's `whole`;
/// wrap in [`Delay`] to enter Moore wiring.)
#[derive(Debug, Clone, Copy, Default)]
pub struct Echo<A>(core::marker::PhantomData<fn(A) -> A>);
/// Constructor for the identity transducer at type `A`.
pub fn echo<A>() -> Echo<A> {
    Echo(core::marker::PhantomData)
}
impl<A> Transducer for Echo<A> {
    type In = A;
    type Out = A;
    fn step(&mut self, a: A) -> A {
        a
    }
}

/// The constant Moore machine: readout is a fixed value, `update` ignores
/// its input. This is the **unit of the machine applicative** — the point
/// that upgrades [`DuplicateToTransducer`] from `Apply` to `Applicative`. History-
/// invariant by construction: `out()` is the same before and after any
/// sequence of updates. `B: Clone` because the fixed value is read out
/// repeatably from `&self`.
#[derive(Debug, Clone, Copy, Default)]
pub struct Const<A, B>(pub B, core::marker::PhantomData<fn(A)>);
/// Constructor for the constant machine that always reads out `b`.
pub fn constant<A, B: Clone>(b: B) -> Const<A, B> {
    Const(b, core::marker::PhantomData)
}
impl<A, B: Clone> Machine for Const<A, B> {
    type In = A;
    type Out = B;
    fn out(&self) -> B {
        self.0.clone()
    }
    fn update(&mut self, _i: A) {}
}

/// A pure function as a stateless [`Transducer`] (cf. `iter::from_fn`).
#[derive(Clone, Copy)]
pub struct FromFn<A, F>(pub F, core::marker::PhantomData<fn(A)>);
impl<A, F> core::fmt::Debug for FromFn<A, F> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("FromFn").finish_non_exhaustive()
    }
}

/// Constructor for [`FromFn`] (the `PhantomData` carries the otherwise
/// unconstrained input type — E0207 workaround, kept private).
pub fn from_fn<A, B, F: FnMut(A) -> B>(f: F) -> FromFn<A, F> {
    FromFn(f, core::marker::PhantomData)
}

impl<A, B, F: FnMut(A) -> B> Transducer for FromFn<A, F> {
    type In = A;
    type Out = B;
    fn step(&mut self, a: A) -> B {
        (self.0)(a)
    }
}

/// Corepresentability harness: a Moore machine denotes a function from
/// input *histories* — `Machine ≅ Fn(&[In]) -> Out` (Kmett's `machines`
/// polices exactly this as `index . tabulate ≡ id` on its Corepresentable
/// Moore instance). Two machines are equal iff they agree on all
/// histories, which makes this the crate's denotational law-checker:
/// property-test any machine against its reference fold.
pub fn run_history<M: Machine>(m: &mut M, history: impl IntoIterator<Item = M::In>) -> M::Out {
    for i in history {
        m.update(i);
    }
    m.out()
}

/// A machine as a pure sink: step and discard the output (weakening).
/// Implements the kernel's [`crate::base::Absorb`], drawing the boundary from
/// the machine side: an `Absorb` is a machine that keeps its counsel; a
/// machine is an `Absorb` plus a readout.
#[must_use = "a machine does nothing until stepped; an unstepped machine is usually a dropped computation"]
pub struct Driven<M>(
    /// The public field is the interface (the carrier exception, cf.
    /// [`crate::base::Pair`]): after driving, the wrapped machine *is*
    /// the result — `driven.0.out()` is how you read it back.
    pub M,
);

/// Borrow a transducer as a transducer — `Iterator::by_ref`, transposed.
/// A blanket `impl Transducer for &mut M` would overlap the Moore⊂Mealy
/// embedding (the specialization wall), but a CONCRETE wrapper raises no
/// coherence question at all: `ByRef` is not a `Machine`, so nothing
/// overlaps. Closes the composition gap where `Driven(&mut t)` could not
/// be built for a pure transducer: `Driven(ByRef(&mut t))` can.
pub struct ByRef<'a, M: ?Sized>(pub &'a mut M);
impl<M: Transducer + ?Sized> Transducer for ByRef<'_, M> {
    type In = M::In;
    type Out = M::Out;
    fn step(&mut self, a: M::In) -> M::Out {
        self.0.step(a)
    }
}
impl<M: Transducer> crate::base::Absorb<M::In> for Driven<M> {
    fn absorb(&mut self, t: M::In) {
        let _ = self.0.step(t); // dropped output = affine weakening
    }
}

/// Strong at transducer grade: act on the first component, carry the rest.
#[must_use = "a machine does nothing until stepped; an unstepped machine is usually a dropped computation"]
#[derive(Debug, Clone, Copy, Default)]
pub struct OnFirstTransducer<C, M>(M, core::marker::PhantomData<fn(C)>);
/// Constructor for [`OnFirstTransducer`].
pub fn on_first_transducer<C, M: Transducer>(m: M) -> OnFirstTransducer<C, M> {
    OnFirstTransducer(m, core::marker::PhantomData)
}
impl<C, M: Transducer> Transducer for OnFirstTransducer<C, M> {
    type In = (M::In, C);
    type Out = (M::Out, C);
    fn step(&mut self, (a, c): Self::In) -> Self::Out {
        (self.0.step(a), c)
    }
}

/// Strong on the second component (mirror of [`OnFirstTransducer`]).
#[must_use = "a machine does nothing until stepped; an unstepped machine is usually a dropped computation"]
#[derive(Debug, Clone, Copy, Default)]
pub struct OnSecondTransducer<C, M>(M, core::marker::PhantomData<fn(C)>);
/// Constructor for [`OnSecondTransducer`].
pub fn on_second_transducer<C, M: Transducer>(m: M) -> OnSecondTransducer<C, M> {
    OnSecondTransducer(m, core::marker::PhantomData)
}
impl<C, M: Transducer> Transducer for OnSecondTransducer<C, M> {
    type In = (C, M::In);
    type Out = (C, M::Out);
    fn step(&mut self, (c, a): Self::In) -> Self::Out {
        (c, self.0.step(a))
    }
}

/// Choice on the `Err` branch (mirror of [`MapOkTransducer`]): step on `Err`, pass
/// `Ok` through. No bound — a `match` moves into one arm.
#[must_use = "a machine does nothing until stepped; an unstepped machine is usually a dropped computation"]
#[derive(Debug, Clone, Copy, Default)]
pub struct MapErrTransducer<O, M>(M, core::marker::PhantomData<fn(O)>);
/// Constructor for [`MapErrTransducer`].
pub fn on_err_transducer<O, M: Transducer>(m: M) -> MapErrTransducer<O, M> {
    MapErrTransducer(m, core::marker::PhantomData)
}
impl<O, M: Transducer> Transducer for MapErrTransducer<O, M> {
    type In = Result<O, M::In>;
    type Out = Result<O, M::Out>;
    fn step(&mut self, r: Self::In) -> Self::Out {
        match r {
            Ok(o) => Ok(o),
            Err(a) => Err(self.0.step(a)),
        }
    }
}

/// A machine transformer — the shape of `tower::Layer`: map a machine to a
/// machine, i.e. an endofunctor on the category of machines (objects:
/// machines; the `Layer` composes them). Stack layers with [`ThenLayer`].
/// (Name note: unrelated to [`crate::cata::Recursive::Layer`], a pattern
/// functor — two established uses of the word, one crate; the module
/// path disambiguates.)
///
/// This lives on the machine spine, not the pipeline spine: a `Layer`
/// transforms *stateful* transducers, where `Piece` transforms pure
/// values. `Premap`/`Postmap`/`OnFirstTransducer` are the primitive layers;
/// user layers (retry, batch, instrument) implement this trait.
pub trait Layer<M> {
    /// The transformed machine type.
    type Wrapped;
    /// Wrap a machine, producing the transformed machine.
    fn layer(&self, inner: M) -> Self::Wrapped;

    /// Stack `b` outside `self` — build [`ThenLayer`]
    /// (`a.then(b).layer(m) == b.layer(a.layer(m))`).
    fn then<B>(self, b: B) -> ThenLayer<Self, B>
    where
        Self: Sized,
    {
        ThenLayer(self, b)
    }
}

/// The identity layer — the unit of [`ThenLayer`], making machine
/// transformers a monoid: `ThenLayer(IdLayer, l)` and `ThenLayer(l,
/// IdLayer)` both equal `l`.
#[derive(Debug, Clone, Copy, Default)]
pub struct IdLayer;
impl<M> Layer<M> for IdLayer {
    type Wrapped = M;
    fn layer(&self, inner: M) -> M {
        inner
    }
}

/// Compose two layers: `ThenLayer(a, b).layer(m) == b.layer(a.layer(m))`.
/// Associative with the identity layer (id) — the endofunctor category's
/// composition.
#[derive(Debug, Clone, Copy, Default)]
pub struct ThenLayer<A, B>(A, B);
impl<M, A: Layer<M>, B: Layer<A::Wrapped>> Layer<M> for ThenLayer<A, B> {
    type Wrapped = B::Wrapped;
    fn layer(&self, inner: M) -> Self::Wrapped {
        self.1.layer(self.0.layer(inner))
    }
}

/// The postmap layer: wrap a machine so its output is post-processed.
/// (A concrete `Layer` instance; premap/onfirst analogues follow the same
/// shape and are left to users so the crate ships the pattern, not every
/// point.)
#[derive(Clone, Copy, Default)]
pub struct PostmapLayer<G>(pub G);
impl<G> core::fmt::Debug for PostmapLayer<G> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("PostmapLayer").finish_non_exhaustive()
    }
}
impl<M: Transducer, G: FnMut(M::Out) -> B + Clone, B> Layer<M> for PostmapLayer<G> {
    type Wrapped = Postmap<M, G>;
    fn layer(&self, inner: M) -> Postmap<M, G> {
        Postmap(inner, self.0.clone())
    }
}

// ================= Transducer combinators (profunctor + choice) =================
// The pipeline combinators re-derived at the FnMut grade: same shapes,
// stateful carriers, `&mut` through split borrows, intermediates by value.

/// Contravariant action on the input: profunctor `lmap` / `contramap`.
#[must_use = "a machine does nothing until stepped; an unstepped machine is usually a dropped computation"]
#[derive(Clone, Copy)]
pub struct Premap<A, F, M>(F, M, core::marker::PhantomData<fn(A)>);
impl<A, F, M: core::fmt::Debug> core::fmt::Debug for Premap<A, F, M> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Premap")
            .field("m", &self.1)
            .finish_non_exhaustive()
    }
}
/// Constructor for [`Premap`] (`PhantomData` pins the input type: with no
/// trait parameters on `Transducer`, an impl cannot constrain `A` any
/// other way).
pub fn premap<A, F, M>(f: F, m: M) -> Premap<A, F, M>
where
    M: Transducer,
    F: FnMut(A) -> M::In,
{
    Premap(f, m, core::marker::PhantomData)
}
impl<A, M: Transducer, F: FnMut(A) -> M::In> Transducer for Premap<A, F, M> {
    type In = A;
    type Out = M::Out;
    fn step(&mut self, a: A) -> M::Out {
        self.1.step((self.0)(a))
    }
}

/// Covariant action on the output: profunctor `rmap`.
/// (`Premap` + `Postmap` together are `dimap`: machines are profunctors.)
#[must_use = "a machine does nothing until stepped; an unstepped machine is usually a dropped computation"]
#[derive(Clone, Copy, Default)]
pub struct Postmap<M, G>(M, G);
impl<M: core::fmt::Debug, G> core::fmt::Debug for Postmap<M, G> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Postmap")
            .field("m", &self.0)
            .finish_non_exhaustive()
    }
}
impl<B, M: Transducer, G: FnMut(M::Out) -> B> Transducer for Postmap<M, G> {
    type In = M::In;
    type Out = B;
    fn step(&mut self, i: M::In) -> B {
        (self.1)(self.0.step(i))
    }
}

/// ArrowChoice's `left` at transducer grade (the `…Transducer` suffix
/// distinguishes the stateful, `FnMut`-carrier version from the
/// pipeline-grade
/// [`crate::base::MapOk`], exactly as `Machine`/`Transducer` name the two
/// grades of the primitive).
///
/// Step on `Ok` inputs, pass `Err` through untouched.
/// Additive structure — **no duplication bound**: a `match` moves the value
/// into exactly one branch (the coproduct's adjunction is unconditional in
/// an affine category).
#[must_use = "a machine does nothing until stepped; an unstepped machine is usually a dropped computation"]
#[derive(Debug, Clone, Copy, Default)]
pub struct MapOkTransducer<E, M>(M, core::marker::PhantomData<fn(E)>);
/// Constructor for [`MapOkTransducer`].
pub fn on_ok_transducer<E, M: Transducer>(m: M) -> MapOkTransducer<E, M> {
    MapOkTransducer(m, core::marker::PhantomData)
}
impl<E, M: Transducer> Transducer for MapOkTransducer<E, M> {
    type In = Result<M::In, E>;
    type Out = Result<M::Out, E>;
    fn step(&mut self, r: Self::In) -> Self::Out {
        match r {
            Ok(a) => Ok(self.0.step(a)),
            Err(e) => Err(e),
        }
    }
}

/// ArrowChoice's fanin `|||`: case analysis into two stateful machines —
/// the coproduct's universal morphism at the FnMut grade. No bounds.
/// (The contravariant `Decidable`'s `choose` is `Premap` of a splitter
/// `A -> Result<B, C>` composed onto this — derived, not shipped.)
#[must_use = "a machine does nothing until stepped; an unstepped machine is usually a dropped computation"]
#[derive(Debug, Clone, Copy, Default)]
pub struct ConsumeResultTransducer<M, N>(M, N);

impl<M, N> ConsumeResultTransducer<M, N> {
    /// Borrow the two components (they are stateful; after driving, the
    /// state *is* the result — std's `into_inner` convention).
    pub fn parts(&self) -> (&M, &N) {
        (&self.0, &self.1)
    }
    /// Take the two components back out.
    pub fn into_parts(self) -> (M, N) {
        (self.0, self.1)
    }
}
impl<M: Transducer, N: Transducer<Out = M::Out>> Transducer for ConsumeResultTransducer<M, N> {
    type In = Result<M::In, N::In>;
    type Out = M::Out;
    fn step(&mut self, r: Self::In) -> M::Out {
        match r {
            Ok(a) => self.0.step(a),
            Err(b) => self.1.step(b),
        }
    }
}

/// The profunctor split `(***)`: decompose the input by value and route
/// each part to its own machine. **No duplication bound** — destructuring
/// moves fields, it never copies.
///
/// This subsumes contravariant `Divisible`'s `divide` (take output-less
/// sinks) as a special case, and is the affine repricing of the
/// contravariant applicative: sums are free ([`ConsumeResultTransducer`]), decompositions
/// are free (here), and only the true diagonal — both machines wanting
/// the *whole* value, [`DuplicateToTransducer`] — pays the [`crate::base::Unaliased`]
/// bound.
#[must_use = "a machine does nothing until stepped; an unstepped machine is usually a dropped computation"]
#[derive(Clone, Copy)]
pub struct AlongsideTransducer<A, D, S, T>(D, S, T, core::marker::PhantomData<fn(A)>);
impl<A, D, S: core::fmt::Debug, T: core::fmt::Debug> core::fmt::Debug
    for AlongsideTransducer<A, D, S, T>
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("AlongsideTransducer")
            .field("s", &self.1)
            .field("t", &self.2)
            .finish_non_exhaustive()
    }
}
/// Constructor for [`AlongsideTransducer`].
pub fn split_transducer<A, B, C, D, S, T>(d: D, s: S, t: T) -> AlongsideTransducer<A, D, S, T>
where
    D: FnMut(A) -> (B, C),
    S: Transducer<In = B>,
    T: Transducer<In = C>,
{
    AlongsideTransducer(d, s, t, core::marker::PhantomData)
}
impl<A, B, C, D, S, T> Transducer for AlongsideTransducer<A, D, S, T>
where
    D: FnMut(A) -> (B, C),
    S: Transducer<In = B>,
    T: Transducer<In = C>,
{
    type In = A;
    type Out = (S::Out, T::Out);
    fn step(&mut self, a: A) -> Self::Out {
        let (b, c) = (self.0)(a);
        (self.1.step(b), self.2.step(c))
    }
}

/// The **Moore-grade product** of two machines over a shared input: read out
/// *both* current states as a pair, and on `update` split the input into two
/// independent copies (sound because `In: Unaliased`) and advance both. This
/// is the product automaton — the Moore counterpart of [`DuplicateToTransducer`], which is
/// the Mealy (Transducer) version that produces its pair by *stepping*.
///
/// Every "run several Moore machines over one stream and combine their
/// readouts" combinator is this plus a readout function: the Boolean
/// recognizer operations are `DuplicateToMachine` composed with a boolean gate,
/// and [`crate::weighted`]'s `Sum`/`Prod` are it composed with a semiring
/// `⊕`/`⊗`.
#[must_use = "a machine does nothing until stepped; an unstepped machine is usually a dropped computation"]
#[derive(Debug, Clone, Copy, Default)]
pub struct DuplicateToMachine<A, B>(A, B);

impl<A, B> DuplicateToMachine<A, B> {
    /// Cross-module constructor for sibling wrappers ([`crate::weighted`]);
    /// public construction is [`Machine::duplicate_to`].
    pub(crate) const fn new(a: A, b: B) -> Self {
        DuplicateToMachine(a, b)
    }
    /// Borrow the two components.
    pub fn parts(&self) -> (&A, &B) {
        (&self.0, &self.1)
    }
    /// Take the two components back out.
    pub fn into_parts(self) -> (A, B) {
        (self.0, self.1)
    }
}

impl<I, A, B> Machine for DuplicateToMachine<A, B>
where
    I: crate::base::Unaliased,
    A: Machine<In = I>,
    B: Machine<In = I>,
{
    type In = I;
    type Out = (A::Out, B::Out);
    fn out(&self) -> (A::Out, B::Out) {
        (self.0.out(), self.1.out())
    }
    fn update(&mut self, i: I) {
        let (l, r) = crate::base::Comonoid::dup(i);
        self.0.update(l);
        self.1.update(r);
    }
}

/// The machine-level [`crate::base::DuplicateTo`]: shared-input fanout of two
/// machines — the Applicative zip of transducers (`Mealy`'s Applicative in
/// Kmett's `machines`; his `Monad` instance one rung up was *removed* there
/// as law-inconsistent, so the structure stops here by design). Both
/// machines see the entire input, so this is a true diagonal and pays
/// the [`crate::base::Unaliased`] bound.
#[must_use = "a machine does nothing until stepped; an unstepped machine is usually a dropped computation"]
#[derive(Debug, Clone, Copy, Default)]
pub struct DuplicateToTransducer<M, N>(M, N);

impl<M, N> DuplicateToTransducer<M, N> {
    /// Borrow the two components (they are stateful; after driving, the
    /// state *is* the result — std's `into_inner` convention).
    pub fn parts(&self) -> (&M, &N) {
        (&self.0, &self.1)
    }
    /// Take the two components back out.
    pub fn into_parts(self) -> (M, N) {
        (self.0, self.1)
    }
}
impl<M, N> Transducer for DuplicateToTransducer<M, N>
where
    M: Transducer,
    N: Transducer<In = M::In>,
    M::In: crate::base::Unaliased,
{
    type In = M::In;
    type Out = (M::Out, N::Out);
    fn step(&mut self, a: Self::In) -> Self::Out {
        let (a1, a2) = crate::base::Comonoid::dup(a);
        (self.0.step(a1), self.1.step(a2))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::{string::String, vec::Vec};

    struct Counter(u64);
    impl Machine for Counter {
        type In = u64;
        type Out = u64;
        fn out(&self) -> u64 {
            self.0
        }
        fn update(&mut self, i: u64) {
            self.0 += i;
        }
    }

    struct Mean {
        n: u64,
        sum: f64,
    }
    impl Machine for Mean {
        type In = f64;
        type Out = f64;
        fn out(&self) -> f64 {
            if self.n == 0 {
                0.0
            } else {
                self.sum / self.n as f64
            }
        }
        fn update(&mut self, x: f64) {
            self.n += 1;
            self.sum += x;
        }
    }

    #[test]
    fn machine_embeds_in_transducer_and_wiring_is_zero_cost() {
        // blanket embedding: a Moore machine steps as a Mealy machine
        let mut c = Counter(0);
        assert_eq!(c.step(5), 5); // update; out
        assert_eq!(c.step(3), 8);

        let sys = Par(Counter(0), Mean { n: 0, sum: 0.0 });
        assert_eq!(
            core::mem::size_of_val(&sys),
            core::mem::size_of::<Counter>() + core::mem::size_of::<Mean>()
        );
    }

    #[test]
    fn fanout_machine_moore_product() {
        // read both readouts as a pair; shared input duplicated to both
        let mut m = DuplicateToMachine(Counter(0), Counter(0));
        m.update(3);
        m.update(4);
        assert_eq!(m.out(), (7, 7)); // both counters saw the same input
    }

    #[cfg(feature = "std")]
    #[test]
    fn hasher_is_a_moore_machine() {
        use crate::machines::run_history;
        use std::collections::hash_map::DefaultHasher;
        // determinism: same history -> same readout (the corepresentable law)
        let a = run_history(&mut Hashing(DefaultHasher::new()), *b"abc");
        let b = run_history(&mut Hashing(DefaultHasher::new()), *b"abc");
        assert_eq!(a, b);
    }

    #[cfg(feature = "std")]
    #[test]
    fn par_parallel_update() {
        let mut t = Par(Counter(0), Counter(100));
        t.par_update((5, 7));
        assert_eq!(t.out(), (5, 107));
    }

    #[test]
    fn pipe_is_moore_closed_and_associative() {
        // counter |> lagged(double)
        let mk = || {
            Pipe(
                Counter(0),
                Delay {
                    m: from_fn(|x: u64| x * 2),
                    last: 0,
                },
            )
        };
        let (mut left, mut right) = (
            Pipe(
                mk(),
                Delay {
                    m: from_fn(|x: u64| x + 1),
                    last: 0,
                },
            ),
            Pipe(
                mk(),
                Delay {
                    m: from_fn(|x: u64| x + 1),
                    last: 0,
                },
            ),
        );
        for i in [3u64, 7, 11] {
            left.update(i);
            right.update(i);
            assert_eq!(left.out(), right.out());
        }
    }

    #[test]
    fn machine_and_layer_identities() {
        // Echo is the transducer identity
        assert_eq!(echo::<i32>().step(7), 7);
        // IdLayer is the unit of ThenLayer
        let l = PostmapLayer(|n: u64| n + 1);
        let mut viaid = ThenLayer(IdLayer, PostmapLayer(|n: u64| n + 1)).layer(Counter(0));
        let mut plain = l.layer(Counter(0));
        assert_eq!(viaid.step(5), plain.step(5));
    }

    #[test]
    fn layer_stacks() {
        // a machine-transformer stack: wrap a counter to *10 then +1
        let stack = ThenLayer(PostmapLayer(|n: u64| n * 10), PostmapLayer(|n: u64| n + 1));
        let mut m = stack.layer(Counter(0));
        assert_eq!(m.step(5), 51);
        assert_eq!(m.step(3), 81);
    }

    #[test]
    fn history_denotation_and_kernel_bridge() {
        // denotational equality: two wirings of the same pipeline agree on
        // histories (the corepresentable law harness in action):
        let mut left = Pipe(
            Counter(0),
            Delay {
                m: from_fn(|x: u64| x * 2),
                last: 0,
            },
        );
        let mut right = Pipe(
            Counter(0),
            Delay {
                m: from_fn(|x: u64| x * 2),
                last: 0,
            },
        );
        assert_eq!(
            run_history(&mut left, [1u64, 2, 3]),
            run_history(&mut right, [1u64, 2, 3])
        );

        // the bridge: a machine as a sink for the kernel's Absorb
        use crate::base::Absorb;
        let mut sink = Driven(Counter(0));
        for i in [5u64, 7] {
            sink.absorb(i);
        }
        assert_eq!(sink.0.out(), 12);
    }

    #[test]
    fn constant_machine_is_applicative_unit() {
        use crate::machines::{constant, run_history, DuplicateToTransducer};
        // history-invariant: pure(7) reads 7 regardless of inputs
        let mut p = constant::<u64, u64>(7);
        assert_eq!(run_history(&mut p, [1, 2, 3]), 7);
        // applicative unit law shape: DuplicateToTransducer(pure(c), m) carries c alongside m
        use crate::machines::Transducer;
        let mut both = DuplicateToTransducer(constant::<u64, &str>("k"), Counter(0));
        assert_eq!(both.step(5), ("k", 5));
    }

    #[test]
    fn strong_choice_completions_machine_grade() {
        use crate::machines::{on_err_transducer, on_second_transducer, Transducer};
        // OnSecondTransducer: act on second component
        let mut s = on_second_transducer::<bool, _>(Counter(0));
        assert_eq!(s.step((true, 5)), (true, 5));
        // MapErrTransducer: step on Err, pass Ok through
        let mut e = on_err_transducer::<u64, _>(Counter(0));
        assert_eq!(e.step(Ok(9)), Ok(9));
        assert_eq!(e.step(Err(3)), Err(3));
    }

    #[test]
    fn table_machine_runs_a_dfa() {
        use crate::machines::{run_history, TableMachine};
        // /ab*c/ over bytes, stride 4 via an equivalence map (a,b,c,other):
        // states 0=start 1=seen-a 2=accept 3=dead; symbols 0=a 1=b 2=c 3=other
        let t: [u32; 16] = [
            1, 3, 3, 3, // state 0: a->1 else dead
            3, 1, 2, 3, // state 1: b->1 c->2 else dead
            3, 3, 3, 3, // state 2: dead
            3, 3, 3, 3, // state 3: dead
        ];
        let acc = [false, false, true, false];
        let class = |b: u8| match b {
            b'a' => 0u8,
            b'b' => 1,
            b'c' => 2,
            _ => 3,
        };
        let matches = |s: &[u8]| {
            // `new` validates the table shape; this one is well-formed.
            let mut m = TableMachine::new(&t, &acc, 4).expect("well-formed table");
            run_history(&mut m, s.iter().map(|&b| class(b)))
        };
        assert!(matches(b"ac"));
        assert!(matches(b"abbbc"));
        assert!(!matches(b"ab"));
        assert!(!matches(b"axc"));
    }

    #[test]
    fn readout_fold_is_a_machine_and_driven_forgets_only_the_readout() {
        use crate::base::Absorb;
        // the readout grade: a Vec-fold with a length readout attached
        let mut m =
            readout::<u64, _, _>(alloc::vec::Vec::new(), |v: &alloc::vec::Vec<u64>| v.len());
        // streaming readout with no extra code — scan on a fold:
        let lens: alloc::vec::Vec<usize> = m.scan([7u64, 7, 7]).collect();
        assert_eq!(lens, alloc::vec![0, 1, 2, 3]);
        // the retraction, concretely (FoldMooreRetract.agda): Driven
        // forgets exactly the readout; the dynamics survive intact.
        let mut sink = Driven(readout::<u64, _, _>(
            alloc::vec::Vec::new(),
            |v: &alloc::vec::Vec<u64>| v.len(),
        ));
        sink.accumulate([1u64, 2, 3]);
        let recovered = sink.0.into_inner();
        assert_eq!(recovered, alloc::vec![1u64, 2, 3]); // == the plain fold
    }

    #[test]
    fn scan_last_agrees_with_run_history() {
        // the Rust mirror of `scan-last` (MooreComonad.agda): the final
        // scanned readout is the run_history readout, and the length is
        // history + 1 (initial readout included, as in the model).
        struct Tot(u64);
        impl Machine for Tot {
            type In = u64;
            type Out = u64;
            fn out(&self) -> u64 {
                self.0
            }
            fn update(&mut self, i: u64) {
                self.0 += i;
            }
        }
        let h = [3u64, 1, 4, 1, 5];
        let scanned: alloc::vec::Vec<u64> = Tot(0).scan(h).collect();
        assert_eq!(scanned, alloc::vec![0, 3, 4, 8, 9, 14]);
        assert_eq!(scanned.len(), h.len() + 1);
        assert_eq!(*scanned.last().unwrap(), Tot(0).run_history(h));
        // and the machine survives its scan, holding the final state:
        let mut m = Tot(0);
        m.scan(h).for_each(drop);
        assert_eq!(m.out(), 14);
    }

    #[test]
    fn table_machine_new_makes_malformed_tables_unrepresentable() {
        let acc = [false, true];
        assert!(TableMachine::new(&[1, 0, 1, 0], &acc, 2).is_some());
        assert!(TableMachine::new(&[1, 0, 1], &acc, 2).is_none()); // wrong length
        assert!(TableMachine::new(&[1, 0, 2, 0], &acc, 2).is_none()); // target >= nstates
        assert!(TableMachine::new(&[], &[], 2).is_none()); // zero states
        assert!(TableMachine::new(&[], &acc, 0).is_none()); // zero stride
    }

    #[test]
    fn transducer_combinators() {
        // dimap around a stateful counter:
        let mut m = Postmap(premap(|s: &str| s.len() as u64, Counter(0)), |n: u64| {
            n * 10
        });
        assert_eq!(m.step("abc"), 30);
        assert_eq!(m.step("d"), 40);

        // additive: choice + fanin, zero bounds, stateful both sides
        let mut r = ConsumeResultTransducer(Counter(0), premap(|x: f64| x as u64, Counter(100)));
        assert_eq!(r.step(Ok(5)), 5);
        assert_eq!(r.step(Err(7.0)), 107);

        // divisible-by-decomposition: split a pair by move, no dup bound —
        // works on non-Clone data:
        struct Absorb(Vec<String>); // non-Clone consumer state is fine
        impl Transducer for Absorb {
            type In = String;
            type Out = usize;
            fn step(&mut self, s: String) -> usize {
                self.0.push(s);
                self.0.len()
            }
        }
        let mut sp = split_transducer(
            |(n, s): (u64, String)| (n, s),
            Counter(0),
            Absorb(Vec::new()),
        );
        assert_eq!(sp.step((3, "x".into())), (3, 1));

        // shared-input fanout: the true diagonal, gated on Unaliased
        let mut b = DuplicateToTransducer(Counter(0), Counter(1000));
        assert_eq!(b.step(5), (5, 1005));
    }

    #[test]
    fn feedback_closes_a_loop_without_a_register() {
        // Accumulator via feedback: In = (i, fb), Out = (o, fb') where the
        // fed-back wire carries the running total.
        struct Acc(u64);
        impl Machine for Acc {
            type In = (u64, u64); // (input, feedback)
            type Out = (u64, u64); // (output, feedback')
            fn out(&self) -> (u64, u64) {
                (self.0, self.0)
            }
            fn update(&mut self, (i, fb): (u64, u64)) {
                // uses the fed-back previous total, not just its own state,
                // to demonstrate a genuine loop:
                self.0 = fb + i;
            }
        }
        let mut looped = Feedback(Acc(0));
        looped.update(5);
        looped.update(7);
        looped.update(1);
        assert_eq!(looped.out(), 13);
    }
}
