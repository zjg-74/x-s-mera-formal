-- LeanSrc/XS_MERA_Appendix_AxiomRisk.lean
-- C：Axiom Risk Catalogue (paper appendix)
-- Not executable proof; structured documentation for the manuscript
-- ================================================================
/-
# Axiom Catalogue, Semantic Boundaries, Risks & Tradeoffs

## Base axioms (XS_MERA_InterfaceGap AX1–AX4)

AX1: π(p) = none ↔ ¬ InImage(p)
  Risk: definitional; breaks if π becomes probabilistic rather than Option-valued.

AX2: DemandPreformatted → Hazard
  Risk: one-way implication; Hazard is binary toggle here, not continuous.

AX3 (weak, default): ReactiveAction p → ¬ rewardHack p
  Risk: central pivot. Only blocks direct self-signal hacking.
  Does NOT rule out indirect latent perturbation (pGrey witness).

AX4: InterfaceCut p → InstitutionalCut p
  Risk: low, set inclusion; static D_inst, not dynamic.

## Temporal bridge TB1–TB3

TB1: π only samples initial slice, not future trajectory valuation
TB2: Slow-value valuation resides in LatentState
TB3: Hazard enforces instant summary; settlement rejects delayed latent value
  Risk: TB3 is a governance assumption, not technical.
  If settlement cycles are extended, temporal gap vanishes.

## Two AX3 variants

| Version | Scope | Allows pGrey | Defensive burden |
| ---- | ---- | ---- | ---- |
| Weak AX3 | Only direct hacking | Yes | Low |
| AX3* | Direct + indirect perturbation hacking | No | High |

## Plausible test summary

1. Weak AX3: No counterexample for direct hacking; pGrey is a valid witness for indirect hacking.
2. AX3*: pGrey becomes a counterexample; extra temporal constraints required for consistency.
3. Expanded π' test: JudgementGap persists even after including slow-value practices into observation.

## Open extensions for future work

1. Continuous Hazard weight instead of boolean
2. Probabilistic observation channel π
3. Dynamic PreferP updated by feedback loops
4. Time‑varying institutional set D_inst
-/
