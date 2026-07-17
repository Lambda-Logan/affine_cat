# Proof corpus

Seven files, all `--safe`, no postulates, termination and positivity
checking on. Checked against Agda 2.6.3 / stdlib 1.7.3:

```
agda --safe FoldEnv.agda Hylo.agda AbsorbEnv.agda Order.agda \
            Machine.agda TwoAbsorb.agda ScopedAbsorb.agda
```

(`Order` imports `AbsorbEnv`; `Machine`, `TwoAbsorb`, `ScopedAbsorb` are
self-contained; run from this directory.)

## Index: theorem → Rust artifact

| File | Theorems | What it licenses in the crate |
|---|---|---|
| `FoldEnv` | `blind`, `agreeV/R`, `balV/R`, `bananaV/R`, `collapseV/R`, `WSV`/`safeV` | The two-phase fold API over the letter's env-in-algebra signature: `blind` is the rejection theorem (a bottom-up algebra cannot see binders — for **every** algebra, definitionally); `agree` pins the exponential-carrier workaround; `safeV` is well-scoped resolution. |
| `Hylo` | `absorb-sound` (T-A), `banana`, `pair-annihilates` (T-C, note the forced `∧`), `pair-short` (T-D), `reflection` (T-H), `copy-and-analyze` | `FoldAlg::absorbing` short-circuit soundness; `Pair`'s absorption is the conjunction; `Rebuild`'s reflection law; deforestation shape. |
| `AbsorbEnv` | `naive-leaks` (a concrete refutation), `balG`, `brkAb`, `agree` | Why `#[recursive(scope)]` uses a Drop-guard: skipping restore on Break corrupts the env (`naive-leaks`); the guard restores on every exit (`brkAb`), and absorption under scoping still agrees (`agree`). |
| `Order` | `order-perm` (unconditional), `order-observable` | Both tails of "order is contract": bracketed driver-owned motion makes plain-fold sibling order unobservable for **all** algebras; absorption re-introduces observability (exhibited two-absorber term). |
| `Machine` | `key`, `machine≡fold` (T-M) | The FoldMachine in `cata.rs` tests — the bracketed (`Open/Leaf/Close`), depth-carrying machine, i.e. the **scoped** fold defunctionalized; the readout condition falls out of the statement. (Second statement: the first version proved a postfix env-free machine — green, and not the shipped one. Rim-audit correction.) |
| `TwoAbsorb` | `agreeV/R` (T-X) | `try_fold2` / the either-bubble design. The proof, not the design, produced the law: **bubble-form annihilation** — cross-sort bubbles require promotes acting as sections on absorbed values. In the generated `…Absorb` trait docs. |
| `ScopedAbsorb` | `balV/R` (B2X), `agreeV/R` (T2X) | `try_fold_in2`: the composition of guarded scoping and cross-sort bubbles, with **value-dependent frames** (`scope_prev` via `enter_with`; plain `scope` is the constant instance). Adds the third discovered law: annihilation must be **env-uniform** — a bubble transits scopes on the way out. |

## Standing seams (no oracle; the honest floor)

* **Transport:** the models use owned strict payloads; the shipped Rust
  lends payloads by reference (`Layer<'a>`). No theorem is
  payload-load-bearing, so the transport is shape-preserving — asserted,
  not re-proved (header note in `FoldEnv`).
* **Rims:** green files prove the proofs, not that each statement encodes
  the intended Rust claim. That correspondence was audited by hand (and
  the audit found and fixed the `Machine` drift above); it is a recurring
  human spend, not a checked artifact.
