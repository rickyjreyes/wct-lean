# Lean Paper Equation Coverage Map

**Status:** First-pass Lean coverage audit / review draft  
**Date:** 2026-06-28  
**Repository:** `rickyjreyes/wct-lean`  

This file answers a narrow question:

> Are the major equations from the WCT papers represented in Lean?

This document does **not** change canonical equations, physical claims, paper text, SymPy status, or Lean theorem status. It only maps paper families to the current Lean formalization state.

---

## Current maintained Lean coverage

The canonical WCT registry contains 142 objects.

Current maintained Lean direct/supporting mappings cover 18 canonical IDs:

```text
E1A E1B E2 E3 E5 E6 E7 E9 E13 E14 E17 E18 E58 E78 CM9 CM12 CM13 CM16
```

The maintained index says the other 124 registry objects do **not** have direct completed Lean mappings.

Important rule:

```text
A SymPy PASS is not a Lean proof.
A Lean theorem is not empirical validation.
```

---

## Summary answer

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

---

## Paper-level Lean status

| Paper / branch | Lean status | Current Lean IDs / notes |
|---|---|---|
| Geometry of Resonance | PARTIAL | E17, E18 only; M2/M6/M7 and many descendants not complete |
| Phase-Flux Field | PARTIAL | E9, E13, E14, E58 |
| Rest Energy / Loop Curvature | PARTIAL / strongest | E1A, E1B, E2, E3, E5, E6, E7; missing M1/E4/E8/full variational closure |
| Hard Dimensionality Bound | NOT COVERED directly | M4, E24-E27, E65-E70, TOP1-TOP9 need Lean work |
| Physical Constants | MOSTLY NOT COVERED | E6/E7 skeleton only; parameter derivations not complete |
| Fourier Cymatics | PARTIAL | E13, E14, E58; entropy/support/convergence not complete |
| Effective Mass | PARTIAL | E1A/E1B/E5/E6/E7; CLE/E19/E49 not complete |
| Log Curvature Flow | NOT COVERED in maintained index | G1, EX, EY, EZ, FA not direct Lean mappings |
| Koide Mass Relation | PARTIAL / adjacent | Koide.lean and KoideDerivation.lean exist, but canonical ID integration incomplete |
| Water cavity | NOT COVERED / empirical | could formalize Q/power algebra later |
| Photodiode ledger | NOT LEAN TARGET yet | needs prediction/experiment object mapping first |
| JUNO ghost-mode | PARTIAL definitions only | CM12/CM13 definitions; G1 and smearing not complete |
| LHCb C9 | NOT COVERED | needs object extraction |
| B0 -> K* spectra | NOT COVERED | needs object extraction |
| NIST Atomic Line List | NOT COVERED / data-analysis | needs object extraction |
| WCC / P-NP equivalence | MOSTLY NOT COVERED | E78 adjacent TODO only; M5/E35-E40/E71-E76 not complete |
| WCC model separation | NOT COVERED | needs formal computational model |
| P vs NP critique | NOT LEAN TARGET yet | claim mapping before Lean |
| WaveLock | NOT COVERED | only nearby E17/E18 generic pieces |
| RCA / safe superintelligence | NOT LEAN TARGET yet | concept/protocol mapping first |
| AI drift audit | NOT LEAN TARGET | prediction audit, not equation formalization |
| Fusion tokamak control | NOT COVERED | handoff gate/control equations need extraction |

---

## Best next Lean targets

```text
M1 / E4 / E8: full locking solution and weighted identity family
M2 / E17: full complex modulus-squared curvature operator
E13/E14: full generalized Euler-Lagrange / gradient-flow theorem
E18: full functional chain rule and coercivity route
M4 / E24 / E65-E70: Sobolev dimensional threshold and corrected high-regularity route
EX / EY / EZ: log transform and Cole-Hopf reduction
CLE1-CLE10: curvature-locking/electron sector
Koide files -> explicit canonical KOIDE IDs and declaration map
```

---

## Conclusion

Lean is a serious formal scaffold, but it does **not** include all major equations from all papers yet. The correct next step is to expand Lean coverage from the 18 maintained IDs toward the core mathematical spine first.
