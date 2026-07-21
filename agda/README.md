# Proof corpus

Twelve files, all `--safe`, no postulates, termination/positivity (and,
where coinductive, guardedness) checking on. Checked against Agda 2.6.3 /
stdlib 1.7.3. **Each module is checked under its own option set** — a
flat `--safe` sweep would reject the coinductive and cubical members —
and `ci.sh` encodes exactly this table:

```
agda --safe FoldEnv.agda Hylo.agda AbsorbEnv.agda Order.agda \
            Machine.agda TwoAbsorb.agda ScopedAbsorb.agda \
            GapClock.agda FinishPair.agda
agda --safe --without-K                Comonoid.agda
agda --safe --without-K --guardedness  FoldMooreRetract.agda
agda --safe --cubical  --guardedness   MooreComonad.agda
```

Cubical is confined to `MooreComonad`: its obligations are
equalities *between coinductive machines*, which need coinductive
extensionality (copattern the proof into a path); every other module's
obligations are equalities between values, and plain `--safe` carries
them. (`Order` imports `AbsorbEnv`; the rest are self-contained; run
from this directory.)

## Index: theorem → Rust artifact

| File | Theorems | What it licenses in the crate |
|---|---|---|
| `FoldEnv` | `blind`, `agreeV/R`, `balV/R`, `bananaV/R`, `collapseV/R`, `WSV`/`safeV` | The two-phase fold API over the letter's env-in-algebra signature: `blind` is the rejection theorem (a bottom-up algebra cannot see binders — for **every** algebra, definitionally); `agree` pins the exponential-carrier workaround; `safeV` is well-scoped resolution. |
| `Hylo` | `absorb-sound` (T-A), `banana`, `pair-annihilates` (T-C, note the forced `∧`), `pair-short` (T-D), `reflection` (T-H), `copy-and-analyze` | `FoldAlg::absorbing` short-circuit soundness; `Pair`'s absorption is the conjunction; `Rebuild`'s reflection law; deforestation shape. |
| `AbsorbEnv` | `naive-leaks` (a concrete refutation), `balG`, `brkAb`, `agree` | Why `#[recursive(scope)]` uses a Drop-guard: skipping restore on Break corrupts the env (`naive-leaks`); the guard restores on every exit (`brkAb`), and absorption under scoping still agrees (`agree`). |
| `Order` | `order-perm` (unconditional), `order-observable` | Both tails of "order is contract": bracketed driver-owned motion makes plain-fold sibling order unobservable for **all** algebras; absorption re-introduces observability (exhibited two-absorber term). |
| `Machine` | `key`, `machine≡fold` (T-M) | The FoldMachine in `cata.rs` tests — the bracketed (`Open/Leaf/Close`), depth-carrying machine, i.e. the **scoped** fold defunctionalized; the readout condition follows from the statement. (Second statement: the first version proved a postfix env-free machine — green, and not the shipped one. Rim-audit correction.) |
| `TwoAbsorb` | `agreeV/R` (T-X) | `try_fold2` / the either-bubble design. The proof, not the design, produced the law: **bubble-form annihilation** — cross-sort bubbles require promotes acting as sections on absorbed values. In the generated `…Absorb` trait docs. |
| `ScopedAbsorb` | `balV/R` (B2X), `agreeV/R` (T2X) | `try_fold_in2`: the composition of guarded scoping and cross-sort bubbles, with **value-dependent frames** (`scope_prev` via `enter_with`; plain `scope` is the constant instance). Adds the third discovered law: annihilation must be **env-uniform** — a bubble transits scopes on the way out. |
| `GapClock` | `delay-reads-back` (T-D), `gap-pair` (T-G) | The clock theorem scoping the Tee wall: gap-grams are a *shift* of one stream (delay register + Moore product, one pass, no suspended producer), so Tee is deferred for variable-rate legs only. Cited by the `lib.rs` Tee note and the zip-wall boundary note in `data.rs`. |
| `FinishPair` | `split` (T-S), `finish-split` (T-F) | `data::accumulate_finish`: the finish eliminator imposes **no law** beyond pairing — `finish-split` is one `cong` past `split` — which is why the Rust surface takes a bare `FnOnce(State) -> A`, not a trait. |
| `Comonoid` | `del-unique`, `dup-unique`, counit/coassoc/cocomm for the diagonal | `base::Unaliased` as *the* comonoid structure: the counit laws force the diagonal, so copyability is a property, never a design choice. The complementary half — `Copy` does not imply the law — is a fact about Rust's semantics, witnessed in Rust (`copy_diagonal_on_shared_cell_breaks_the_independence_law` in `base.rs`), not here. |
| `MooreComonad` | `counit-l`/`counit-r`/`coassoc` (the comonad laws), `dup-tracks`, `scan-last` | `Machine` as the (cofree-comonoid) comonad: extract = `out`, and `Machine::scan` is the extract-image of the duplicate orbit. The raw `duplicate` is refused in Rust (per-step clone); this module holds the real map. The one cubical member. |
| `FoldMooreRetract` | `build-tracks` (T-BUILD), `retract` (T-RETRACT) | The `Driven` / `machines::readout` pair as a **definitional** section–retraction: building a machine from a readout-fold preserves dynamics and readout definitionally, and `Driven` forgets exactly the readout. |

## Where the checking stops (no oracle past this line)

* **Transport:** the models use owned strict payloads; the shipped Rust
  lends payloads by reference (`Layer<'a>`). No theorem depends on the
  payload, so the transport is shape-preserving — asserted, not
  re-proved (header note in `FoldEnv`).
* **Rims:** green files prove the proofs, not that each statement encodes
  the intended Rust claim. That correspondence was audited by hand (and
  the audit found and fixed the `Machine` drift above); it is a recurring
  human spend, not a checked artifact.
* **The universal property:** `Comonoid` and `MooreComonad` mechanize
  the equational content of the frame (comonoid laws + uniqueness; the
  comonad laws) in concrete `Set` models. *Freeness/cofreeness* — the
  "free semicartesian SMC" reading itself — needs an abstract-category
  setting this corpus does not carry; it is a permanent boundary of the
  corpus, stated here, not a backlog item.
* **Division of witness labor:** operational facts about Rust are
  witnessed in Rust, not modeled here — the `&Cell` counterexample (the
  `Copy` ⊉ lawful-Δ half of the `Unaliased` story) and the dyn-fence
  performance claims are tests and benches; that division is the point.
