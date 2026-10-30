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

`XS_MERA_Appendix_AxiomRisk.lean` is complete. The seven other modules are present as
**placeholders** (module docstring only) so that the directory tree and `lakefile.lean` match
the intended layout; no proof content has been committed for them yet. Until they are filled in,
`lake build` succeeds but proves nothing beyond the appendix, and `lake run xsmera_test` has no
`main` to run.
