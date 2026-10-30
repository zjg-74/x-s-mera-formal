# X‑S‑MERA Formalization (Lean4)

Formal pressure-testing for the X‑S‑MERA cognitive framework, focused on **interface gap, reward hacking, reactive action, and temporal latent value**.

This repository contains the formal model, typeclass hierarchy, temporal bridge, grey boundary case analysis, Plausible property-based random testing, and two variants of the core isolation axiom (weak AX3 / strong AX3*).

> Companion to the journal paper: Quantification alienation and reward hijacking in instructional evaluation

## Dependency

- Lean 4 (nightly / stable compatible with Plausible)
- Lake build system
- Plausible: property-based testing (Lean4 alternative to QuickChick)

## Build & Run

```bash
lake update
lake build
lake run xsmera_test
```

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

- Proofs for the static benchmark model
- Plausible randomized search for counterexamples
- Explicit witness `pGrey` demonstrating the boundary of the weak axiom
- Side-by-side comparison of axiom variants for discussion in the paper

## License

MIT

---

## Repository status

| Module | Status |
|---|---|
| `XS_MERA_Core.lean` | Definitions written. Not compiled. |
| `XS_MERA_InterfaceGap.lean` | Definitions and AX1–AX4 written. **Not compiled**; one `sorry`. |
| `XS_MERA_Appendix_AxiomRisk.lean` | Complete (documentation module). |
| the other five modules | Placeholders (module docstring only) |

Two things a reader should know before citing this repository:

1. **Nothing here has been type-checked.** The modules were written without a Lean toolchain
   on the author's machine; they follow Lean 4 rules but have not been through `lake build`.
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
