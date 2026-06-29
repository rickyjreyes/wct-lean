# Lean Paper Equation Coverage Map

**Status:** First-pass Lean coverage audit / review draft  
**Date:** 2026-06-28  
**Repository:** `rickyjreyes/wct-lean`  

This file answers a narrower question than the general paper-to-registry map:

> Are the major equations from the WCT papers represented in Lean?

This document does **not** change canonical equations, physical claims, paper text, or SymPy status. It only maps paper families to the current Lean formalization state.

---

## Core distinction

The WCT corpus has three different coverage layers:

| Layer | Meaning |
|---|---|
| Canonical registry coverage | Equation exists as a stable WCT object in `geometry_of_resonance`. |
| SymPy coverage | Equation has symbolic/dimensional/limit/checker coverage in `wct-sympy`. |
| Lean coverage | Equation has a kernel-checked declaration, definition, counterexample, or explicit formal TODO in `wct-lean`. |

This file is only about the third layer: **Lean**.

---

## Current Lean status from `FORMAL_COVERAGE_INDEX.md`

The canonical WCT registry contains 142 objects.

Current maintained Lean direct/supporting mappings cover 18 canonical IDs:

```text
E1A E1B E2 E3 E5 E6 E7 E9 E13 E14 E17 E18 E58 E78 CM9 CM12 CM13 CM16
```

Current maintained Lean index says the other 124 registry objects do **not** have direct completed Lean mappings.

Important rule:

```text
A SymPy PASS is not a Lean proof.
A Lean theorem is not empirical validation.
```

---

# Status labels

| Status | Meaning |
|---|---|
| `LEAN_COVERED_CORE` | Major equation family has direct or supporting Lean declarations. |
| `LEAN_PARTIAL` | Some core equations are represented, but key paper-level equations are not formalized. |
| `LEAN_NOT_COVERED` | No clear direct Lean mapping exists for the major paper equations. |
| `LEAN_DEFINITION_ONLY` | Lean representation is definitional, not theorem-level closure. |
| `LEAN_TODO_OPEN` | Lean includes or implies a TODO/open obligation, but no completed proof. |
| `NOT_LEAN_TARGET` | Mostly narrative, empirical, audit, architecture, or protocol paper; should be mapped as claims/experiments rather than formal theorem objects unless equations are extracted. |

---

# Paper-by-paper Lean map

## 1. The Geometry of Resonance

**Lean status:** `LEAN_PARTIAL`

**Lean-covered / supporting IDs:**

```text
E17
E18
```

**Major gaps:**

```text
M2
M6A
M6B
M7
E19-E23
E49
E51-E56
E81-E82
```

**Conclusion:** The core operator/energy pieces have partial Lean support, but the full Geometry paper is not Lean-complete.

---

## 2. Phase-Flux Field (PFF)

**Lean status:** `LEAN_PARTIAL`

**Lean-covered / supporting IDs:**

```text
E9
E13
E14
E58
```

**Major gaps:**

```text
M3
E10
E11
E12
E15
E16
E57
E59-E64
```

**Conclusion:** PFF has meaningful Lean footholds, but not full Lean coverage.

---

## 3. Rest Energy from Density-Weighted Loop Curvature

**Lean status:** `LEAN_PARTIAL`

**Lean-covered / supporting IDs:**

```text
E1A
E1B
E2
E3
E5
E6
E7
```

**Major gaps:**

```text
M1
E4
E8
full variational derivation of locking solution
mislock bounds
uniqueness/existence of locked solutions
```

**Conclusion:** This is one of the best-covered Lean branches, but it is still conditional and not fully formalized.

---

## 4. Hard Upper Bound on Spatial Dimensionality

**Lean status:** `LEAN_NOT_COVERED / LEAN_PARTIAL ONLY INDIRECTLY`

**Lean-covered / supporting IDs:**

```text
None clearly listed among the 18 maintained direct/supporting mappings.
```

**Registry IDs needing Lean work:**

```text
M4
E24-E27
E65-E70
TOP1-TOP9
```

**Conclusion:** The dimensionality paper is registry/SymPy represented, but not yet directly Lean-covered in the maintained 18-ID index.

---

## 5. Structure and Derivation of Physical Constants

**Lean status:** `LEAN_PARTIAL / MOSTLY_NOT_COVERED`

**Lean-covered / supporting IDs:**

```text
E6
E7
possibly Koide files adjacent to the constants/mass branch
```

**Major gaps:**

```text
parameter-origin derivations
xi / sigma / beta / theta / gamma origin
harmonic mass maps
physical constants tables
G-scale relation, if central
fitted-vs-derived classification
```

**Conclusion:** Lean covers only the abstract mass-curvature dimensional skeleton. The constants derivation paper is not Lean-complete.

---

## 6. Self-Emergent Fourier Cymatics

**Lean status:** `LEAN_PARTIAL`

**Lean-covered / supporting IDs:**

```text
E13
E14
E58
```

**Major gaps:**

```text
E12
E15
E16
E29-E34
E57
E59-E64
E81
simulation-specific convergence/entropy claims
finite-support selection proof
```

**Conclusion:** Lean covers selected algebraic/spectral components, not the full cymatics argument.

---

## 7. Emergence of Effective Mass

**Lean status:** `LEAN_PARTIAL`

**Lean-covered / supporting IDs:**

```text
E1A
E1B
E5
E6
E7
```

**Major gaps:**

```text
E19
E49
CLE1-CLE10
solenoidal topology examples
helix/circle worked examples
ppm-scale cavity prediction equations
```

**Conclusion:** The basic mass-curvature chain has Lean support, but most effective-mass and topology-specific claims remain outside completed Lean coverage.

---

## 8. Logarithmic Curvature Flow / Lepton Mass Spectrum

**Lean status:** `LEAN_NOT_COVERED / PARTIAL VIA KOIDE ADJACENT FILES`

**Lean-covered / supporting IDs from current 18-ID list:**

```text
None of G1, EX, EY, EZ, FA are listed as direct/supporting Lean mappings.
```

**Known adjacent Lean files:**

```text
WCTLean/Koide.lean
WCTLean/Models/KoideDerivation.lean
```

**Major gaps:**

```text
EX logarithmic field representation
EY log-curvature evolution
EZ Cole-Hopf reduction
FA filament-localization condition
lepton filament spectrum equations
```

**Conclusion:** Log/Cole-Hopf equations are in the registry/SymPy layer, but not in the maintained Lean coverage list. Koide-related Lean work exists separately.

---

## 9. Koide Mass Relation

**Lean status:** `LEAN_PARTIAL / ADJACENT FORMALIZATION PRESENT`

**Known Lean files:**

```text
WCTLean/Koide.lean
WCTLean/Models/KoideDerivation.lean
```

**Issue:**

Koide has Lean files, but the canonical 142-ID coverage index does not clearly expose Koide as a stable registry ID family.

**Recommended fix:**

```text
Create explicit KOIDE or KM registry IDs, then map those IDs to Lean declarations.
```

**Conclusion:** Lean work exists, but ID/provenance integration is incomplete.

---

## 10. Water Cavity Experiment

**Lean status:** `LEAN_NOT_COVERED / NOT_LEAN_TARGET`

**Potentially related registry IDs:**

```text
E45-E48
E50
E52-E56
E81
```

**Lean-covered IDs:**

```text
None clearly direct in the maintained 18-ID list.
```

**Conclusion:** Mostly experimental/protocol. Lean could formalize Q/power-balance algebra, but empirical claims are not Lean targets.

---

## 11. Photodiode Protocol Ledger

**Lean status:** `NOT_LEAN_TARGET / LEAN_NOT_COVERED`

**Conclusion:** This should be mapped to experiment/prediction objects. Lean is not the main validation layer unless specific threshold inequalities are extracted.

---

## 12. Cymatics repeat entry

Same as paper 6.

---

## 13. JUNO Ghost-Mode Neutrinos

**Lean status:** `LEAN_NOT_COVERED / PARTIAL REGISTRY ONLY`

**Potential registry IDs:**

```text
G1
CM12
CM13
```

**Lean-covered IDs:**

```text
CM12
CM13
```

**Conclusion:** Lean only has definitional support for nearby spectrum metrics.

---

## 14. LHCb C9(q^2) Anomaly

**Lean status:** `LEAN_NOT_COVERED`

**Conclusion:** No clear Lean coverage.

---

## 15. B0 -> K* Open-Data Spectra

**Lean status:** `LEAN_NOT_COVERED`

**Conclusion:** No clear Lean coverage.

---

## 16. NIST Atomic Line List

**Lean status:** `LEAN_NOT_COVERED / NOT_LEAN_TARGET`

**Conclusion:** Data-analysis/statistical validation branch, not currently Lean-covered.

---

## 17. Discrete WCC and Classical Complexity

**Lean status:** `LEAN_NOT_COVERED / PARTIAL ONLY IF E78 ADJACENT`

**Lean-covered / adjacent IDs:**

```text
E78 TODO-adjacent proposition only
```

**Major gaps:**

```text
M5
E35-E40
E71-E76
Turing simulation maps
encoding and cost models
P/NP relationship statements
```

**Conclusion:** WCC complexity is mostly not Lean-covered.

---

## 18. P vs NP in Curvature-Bounded Wave Computation

**Lean status:** `LEAN_NOT_COVERED`

**Conclusion:** Not Lean-covered as a proof-level branch.

---

## 19. Classical P vs NP Ill-Posed Critique

**Lean status:** `NOT_LEAN_TARGET / LEAN_NOT_COVERED`

**Conclusion:** Mostly philosophical/formal critique. Could be mapped as definitions/claims, but not currently Lean-covered.

---

## 20. WaveLock One-Way Function

**Lean status:** `LEAN_NOT_COVERED`

**Potentially related registry IDs:**

```text
M7
E17-E18
E35-E40
E71-E76
```

**Lean-covered nearby IDs:**

```text
E17
E18
```

**Conclusion:** Only generic curvature/energy pieces have Lean support. WaveLock itself is not Lean-covered.

---

## 21. Resonance-Confinement Architecture / Safe Superintelligence

**Lean status:** `NOT_LEAN_TARGET / LEAN_NOT_COVERED`

**Potentially related IDs:**

```text
M5
E35-E40
E71-E80
```

**Lean-covered adjacent IDs:**

```text
E78 TODO-adjacent only
```

**Conclusion:** Mostly architecture/protocol. Should be claim/concept mapped before Lean formalization.

---

## 22. Recursive AI Drift Prediction Audit

**Lean status:** `NOT_LEAN_TARGET`

**Conclusion:** Prediction audit / historical validation note. Not a Lean equation-formalization target unless specific scoring logic is extracted.

---

## 23. Nuclear Fusion Tokamak with Self-Sustaining Resonance

**Lean status:** `LEAN_NOT_COVERED`

**Potentially related registry IDs:**

```text
E45-E48
E50
E52-E56
```

**Lean-covered IDs:**

```text
None clearly direct in the maintained 18-ID list.
```

**Conclusion:** Fusion-control branch is not Lean-covered yet. It would need an applied-control object family before formalization.

---

# Highest-value Lean expansion targets

## Tier 1 — make current core branches much stronger

```text
M1 / E4 / E8: full locking solution and weighted identity family
M2 / E17: full complex modulus-squared curvature operator
E13/E14: full generalized Euler-Lagrange / gradient-flow theorem
E18: full functional chain rule and coercivity route
M4 / E24 / E65-E70: Sobolev dimensional threshold and corrected high-regularity route
EX / EY / EZ: log transform and Cole-Hopf reduction
CLE1-CLE10: curvature-locking/electron sector
```

## Tier 2 — integrate existing adjacent Lean work

```text
Koide.lean -> explicit canonical KOIDE IDs
KoideDerivation.lean -> declaration-to-paper map
CM12/CM13/CM16 -> maintain as definitions, not physical validation
```

## Tier 3 — applied branches needing object families before Lean

```text
WaveLock -> WL object family
Fusion control -> FUSION object family
JUNO/C9/B0/NIST -> PHENO object family
RCA/AI drift -> RCA/AI-AUDIT claim/protocol objects
```

---

# Current conclusion

```text
Does Lean include all major equations from all papers?
No.

Does Lean account for the 142-object registry?
Yes, through FORMAL_COVERAGE_INDEX.md.

How much has direct/supporting maintained Lean coverage?
18 of 142 canonical IDs.

Is the core mass/phase/energy spine partially Lean-supported?
Yes.

Is full paper-level Lean coverage complete?
No.
```

Best next action:

```text
Prioritize Lean expansion on the core mathematical spine first:
Rest Energy + PFF + Geometry + Dimensionality + Log/Cole-Hopf + CLE/Koide.
```
