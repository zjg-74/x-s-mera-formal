# X‑S‑MERA Formalization (Lean4)

Formal pressure-testing for the X‑S‑MERA cognitive framework, focused on **interface gap, reward hacking, reactive action, and temporal latent value**.

**Status: work in progress, not a verification artefact.** All modules now compile (`lake build` passes, Lean 4.35), and the exhaustive finite-domain scan runs and prints its counterexample table. Compilation only checks that the definitions are internally consistent; it does not make the axioms true or the claims "verified" or "proved". The axiom system is still partly vacuous and three modules are placeholders. See `docs/工程使用边界.md` for what this repository may and may not be used to claim.

This repository contains the formal model, typeclass hierarchy, temporal bridge, grey boundary case analysis, an exhaustive finite-domain scan (pure `IO`, no Plausible dependency), and two planned variants of the core isolation axiom (weak AX3 / strong AX3*).

> Companion to the paper 《完整的界面，残缺的接口：教育评价中的需求预格式化及其制度位置》
> (*A Complete Interface, an Incomplete Port: Demand Pre-formatting in Educational Evaluation*)

## Dependency

- Lean 4 (tested with 4.35.0)
- Lake build system
- `Std` (Lean standard library; provides the `Nat` instances). No Mathlib, no Plausible — the exhaustive scan is a plain `IO` loop, so `lake build` needs no network.

## Build & Run

```bash
lake update
lake build
```

The exhaustive scan is a plain `IO` module, so there is no `lean_exe` target: `lean_exe` has no
`srcDir` field, so an executable root cannot point into `LeanSrc/`. Run the scan directly:

```bash
lake env lean LeanSrc/XS_MERA_InterfaceGap_PlausibleTest.lean
```

The `#eval main` at the end of that file executes the scan and prints the conflict table. (A
root-level `Main.lean` could also be added later — see the commented block in `lakefile.lean`.)

## Module dependency order (critical)

1. `XS_MERA_Core.lean` — GAPS B1/B2 foundational axioms
2. `XS_MERA_InterfaceGap.lean` — base interface gap & AX1–AX4 (weak AX3)
3. `XS_MERA_InterfaceGap_ModelClass.lean` — A1: typeclass + static reference model
4. `XS_MERA_InterfaceGap_TemporalBridge.lean` — A2: B2 temporal bridge, TB1–TB3
5. `XS_MERA_InterfaceGap_PlausibleTest.lean` — A3: baseline random search
6. `XS_MERA_InterfaceGap_GreyCase.lean` — B: grey boundary `pGrey`, indirect reward hacking
7. `XS_MERA_InterfaceGap_A3Star.lean` — D: strengthened AX3* and safe model
8. `XS_MERA_Appendix_AxiomRisk.lean` — C: axiom risk catalogue, for paper appendix

## Key theoretical distinction

- **Weak AX3 (default)**: `ReactiveAction p → ¬ rewardHack p`
  Only forbids direct self-signal hijacking; permits indirect latent perturbation (`pGrey`).
- **Strong AX3***: `ReactiveAction p → ¬ (rewardHack p ∨ rewardHackIndirect p)`
  Forbids both direct and indirect reward hacking; stricter, higher justificatory burden.

## Output

Delivered:

- Definitions and hypothesis bundles for the static model, the temporal bridge, and the expansion-conflict test
- An exhaustive scan over a finite practice/signal domain (18 projection × order classes); see `XS_MERA_InterfaceGap_PlausibleTest.lean`
- Side-by-side comparison of axiom variants for discussion in the paper

Done (2026-11):

- A compiled build passes (`lake build`, Lean 4.35). Structural fixes were required: `import`s moved to
  the top of each file, `import Std` added for the `Nat` instances, and the `ℕ` notation replaced by
  `Nat` (the `ℕ` symbol is unreliable without Mathlib).
- The exhaustive scan runs: `lake env lean LeanSrc/XS_MERA_InterfaceGap_PlausibleTest.lean` prints
  the 9-projection × 2-order conflict table.

Planned, not yet written:

- Replacement of the vacuous axioms (`GAPS_axioms`, `B1B2_bridge_axioms`) and of the near-vacuous weak `AX3`
- `GreyCase`: an explicit witness `pGrey` demonstrating the boundary of the weak axiom
- `ModelClass`: a static benchmark model satisfying all four weak axioms
- `A3Star`: the strong-axiom variant and its cost

## License

MIT

---

## Repository status

| Module | Status |
|---|---|
| `XS_MERA_Core.lean` | Definitions written. **Compiled** (`lake build`, 2026-11-04). |
| `XS_MERA_InterfaceGap.lean` | Definitions and AX1–AX4 written. **Compiled**; no `sorry` (the broken expansion theorem was removed, see below). |
| `XS_MERA_InterfaceGap_TemporalBridge.lean` | TB1–TB3 as hypothesis bundles, 6 theorems + 1 counter-model. **Compiled.** |
| `XS_MERA_InterfaceGap_PlausibleTest.lean` | A3: `Conflict` / `LiftExists`, 3 theorems + 4 toy-model results + exhaustive 18-case scan. **Compiled; scan runs.** |
| `XS_MERA_Appendix_AxiomRisk.lean` | Complete (documentation module). |
| the other three modules | Placeholders (module docstring only) |

A3 replaced the theorem it was supposed to test. The old statement
`Thm_ExpandingImageDoesNotEliminateCommensurationPressure` concluded `∃ p, JudgementGap π' …`,
where `JudgementGap` does not mention `π'` at all — so "expanding the image" had no bearing on the
conclusion, and the statement was neither true nor provable (it also carried a `sorry`). It is now
gone, replaced by a pair-level formulation: `Conflict` (a visible pair whose index order contradicts
professional preference), `conflict_blocks_lift` (such a pair admits no compatible total order), and
`Thm_ExpansionPreservesConflict` (widening the image while leaving the order on old pairs unchanged
preserves the conflict). The formal counterpart of "multimodality widens the interface's breadth, not
its direction" is exactly that theorem — with the qualification that reordering *can* remove the
conflict, which is the statement's boundary, not its refutation.

A3 deliberately runs an exhaustive scan instead of a Plausible random search: on two practices and
two signal values, nine projections × two orders is complete, whereas sampling can only miss
counterexamples. `import Plausible` and the lakefile dependency are kept; the hookup point is in the
module's `NOTE`.

A2 (`TemporalBridge`) departed from the `axiom` style used in `Core`/`InterfaceGap`: TB1–TB3 are
`Prop`-valued hypothesis bundles (`SliceRepresentable`, `SlowValueLatent`, `InstantVerdictRecorded`)
that each theorem takes as an explicit argument, so a reader can see which premise carries which
conclusion — and which conclusion collapses when a premise is removed. This is deliberate: empty or
definitional axioms are the easiest thing for a referee to dismiss.

Wording derived from this module (Chinese) is in [`docs/A2-第五节时序措辞.md`](docs/A2-第五节时序措辞.md):
five sentences in §5 that the model forbids or forces, two optional insertions, and four statements
that must not be written.

Two things a reader should know before citing this repository:

1. **The modules compile** (`lake build` passes on Lean 4.35, after structural fixes). Compilation
   checks internal consistency of the definitions; it does not assert that the axioms are true.
   Earlier the modules were written without a toolchain on the author's machine.
2. **The axiom system is currently vacuous.** `AX1` and `AX4` are definitional truths (hence
   stated as theorems, not axioms), `AX2` holds only because `Hazard` is a conjunct of
   `DemandPreformatted`, and `AX3` is trivially true because `ReactiveAction` implies
   `π p = none` while `rewardHack` requires `π p ≠ none`. The intended contrast between weak
   `AX3` and `AX3*` therefore does not yet have a model. See `NOTE` at the end of
   `XS_MERA_InterfaceGap.lean` for the two candidate repairs.

This repository is intended as a formal companion to the argument, not as evidence for it:
Lean proves "axioms ⇒ theorems", never "axioms are true".

## Design note: no Mathlib

The real numbers and the `Set` type live in Mathlib, whose first build takes hours. To keep
`lake build` feasible for a referee, values are typed over an abstract `R` with `[LT R]` and
sets are written as predicates `P → Prop`. Instantiating `R := ℝ` later is a one-line change.
