# WCT Lean Formal Coverage Index

This index separates **canonical registration**, **equation-specific typed support**, **kernel-proved content**, and **physical validation**.

## Canonical navigation

- [Corrected 142-object equation registry](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/WCT_FULL_EQUATION_LIST_CORRECTED.md)
- [Master equation architecture](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/WCT_MASTER_EQUATIONS_UPDATED.md)
- [Complete SymPy classification](https://github.com/rickyjreyes/wct-sympy/blob/main/VERIFICATION_INDEX.md)
- [Lean theorem inventory](THEOREMS.md)
- [SymPy-to-Lean map](SYMPY_MAP.md)
- [Public research-corpus map](https://rickyjreyes.github.io/research-corpus/)

The canonical registry defines equation text, symbols, assumptions, and scientific boundaries. Lean claims only what its declarations encode and what the kernel accepts under displayed hypotheses.

## Layer 1 — Compiled canonical registration: 142 / 142

`WCTLean/Registry.lean` compiles every canonical ID:

| Family | Count |
|---|---:|
| Master systems | 9 |
| Canonical equations | 83 |
| Curvature-locked electron equations | 10 |
| Auxiliary equations | 5 |
| Cosmology equations | 20 |
| Topology equations | 9 |
| Correction equations | 6 |
| **Total** | **142** |

Lean proves registry length, family partition, status partition, uniqueness, and completeness through:

```lean
masterIds_length
canonicalIds_length
electronIds_length
auxiliaryIds_length
cosmologyIds_length
topologyIds_length
correctionIds_length
allEquationIds_length
allEquationIds_nodup
statusPartition_length
statusPartition_nodup
statusPartition_complete
every_registered_id_has_status
every_registered_id_has_family
canonicalRegistry_length
```

The effective symbolic-audit partition is:

| Status | Count |
|---|---:|
| `PASS` | 59 |
| `CONDITIONAL` | 27 |
| `DEFINITION` | 26 |
| `OPEN` | 30 |
| **Total** | **142** |

These are inherited symbolic-audit classifications, not Lean theorem counts.

## Layer 2 — Non-registry typed Lean support: 62 IDs

The following IDs have a maintained equation-specific definition, proposition, theorem, counterexample, or analytic contract beyond registry metadata:

```text
M1 M2 M3 M4 M5 M6A M6B M7
E1A E1B E2 E3 E4 E5 E6 E7 E8 E9 E10 E11
E12 E13 E14 E17 E18 E20
E24 E25 E26 E27 E28 E29 E33 E36
E45 E47 E49 E51 E53
E57 E58 E59 E61 E62 E64
E65 E66 E67 E68 E69 E70
E78 E81
G1 EX EY EZ FA
CM9 CM12 CM13 CM16
```

The new non-shallow mapping batch adds twelve IDs:

```text
M4 M5 M6B
E10 E11 E29 E36
G1 EX EY EZ FA
```

### Direct algebraic, order-theoretic, or finite-dynamical theorem support

```text
M1 M2 M3 M4 M5 M6B M7
E2 E3 E4 E5 E8 E9 E10 E11
E12 E13 E14 E17 E18 E20 E28 E29 E33 E36
E45 E47 E49 E51 E53
E57 E58 E59 E61 E62 E64 E81
G1 EX EY EZ FA
CM9
```

This category includes conditional theorems, finite analogues, scalar reductions, and exact algebraic bridges. It does not imply full PDE, variational, continuum, or physical closure.

### Dimensional support

```text
E1A E1B E6 E7
```

### Definitions or model skeletons

```text
M6A E25 E27 E65 CM12 CM13 CM16
```

### Explicit analytic contracts or predicates

```text
M4 E24 E26 E66 E67 E68 E69 E70
```

The contracts expose missing Sobolev, regularity, interpolation, and stability hypotheses rather than assuming them silently.

### Counterexample or unresolved proposition support

```text
E17 E78
```

E17 includes both the historical scalar-denominator counterexample and the corrected complex denominator theorem. E78 remains a proposition/TODO rather than a completed Fisher-information theorem.

## New non-shallow mappings

### M4 — dimensional threshold

`h2Subcritical_iff_le_three` proves the integer arithmetic equivalence

```text
n < 4  ↔  n ≤ 3
```

while `SobolevCurvatureContract` keeps the actual embedding and curvature-boundedness obligations explicit.

### M5 and E36 — bounded averaged dynamics

`averagedUpdate_norm_le` proves norm nonincrease for convex mixing with a norm-nonexpansive local average. `averagedUpdate_preserves_normBound` proves forward invariance of the encoded bounded resource ball. `averagedUpdate_fixed_of_average_fixed` proves preservation of fixed points.

These are finite-dimensional update theorems, not complexity-class equivalences.

### M6B — nonlinear curvature operator

`thetaComplex_canonical_formula` proves that the typed complex operator is exactly

```text
(-Δψ · conjugate ψ) / (|ψ|² + ε² exp(-2 α |ψ|²))
```

after reassociation. `thetaComplex_denominator_ne_zero` supplies the positive-`ε` denominator condition.

This does not prove uniqueness of the nonlinear closure or PDE well-posedness.

### E10 and E11 — quantization closure

`radialShellQuantized_add` and `windingQuantized_add` prove closure under addition of phase integrals and integer indices. `radialShellQuantized_iff_windingQuantized` proves that the two predicates implement the same integer quantization law once the observable is fixed.

### E29 — entropy-pruning bound

Lean proves:

```text
0 ≤ K exp(-ΔH)
ΔH ≥ 0  →  K exp(-ΔH) ≤ K
ΔH₁ ≤ ΔH₂  →  K exp(-ΔH₂) ≤ K exp(-ΔH₁)
```

for nonnegative mode count `K`.

### G1 — bounded log-periodic ghost mode

`abs_ghostMode_le` proves that the modulation magnitude is bounded by the absolute amplitude.

### EX, EY, EZ, and FA — logarithmic-flow bridge

`exp_logField_eq` proves inversion of the logarithmic field on the positive sector. `coleHopf_residual_factorization` and `diffusionResidual_zero_iff_logCurvatureResidual_zero` prove the exact algebraic residual bridge under displayed temporal and Laplacian chain-rule hypotheses. `filamentLocalizationCondition_iff_mismatch_zero` characterizes localization as zero scalar mismatch.

These results do not supply the missing function-space chain rule or PDE regularity theorem.

## Layer 3 — Registry-only coverage: 80 IDs

The remaining 80 IDs compile with family and status metadata but do not yet have a maintained equation-specific typed declaration that captures substantive mathematical content.

Registry-only does **not** mean false. It means the object is inventoried and classified, but its formula or claim has not yet been represented beyond metadata in the maintained Lean library.

## Major compiled modules

| Module | Principal coverage |
|---|---|
| `WCTLean/Registry.lean` | all 142 IDs, families, effective statuses, completeness proofs |
| `WCTLean/Models/ComplexCurvature.lean` | M2, M6B, E17 corrected complex quotient and denominator safety |
| `WCTLean/Models/Locking.lean` | M1, E3, E4, E8 finite locking algebra |
| `WCTLean/Models/BandPass.lean` | M3, M7, E12, E57, E61, E64 finite-band algebra |
| `WCTLean/Models/PhaseFlux.lean` | E9, E10, E11 phase flux and additive quantization closure |
| `WCTLean/Models/AlgebraicChecks.lean` | E20, E28, E29, E33, E45, E47, E49, E51, E53, E59, E62, E81 |
| `WCTLean/Models/CompactDynamics.lean` | M5, E36 fixed points, norm nonincrease, bounded-set invariance |
| `WCTLean/Models/LogFlow.lean` | EX, EY, EZ, FA logarithmic and diffusion residual bridge |
| `WCTLean/Models/GhostModes.lean` | G1 bounded ghost-mode modulation and smearing definitions |
| `WCTLean/Contracts/Analytic.lean` | M4, E24–E27, E65–E70 analytic boundaries/contracts |
| `WCTLean/DerivedAudit.lean` | E5, E9, E13/E14, E18, E58, CM9, CM12, CM13, CM16 |
| `WCTLean/ResolvedAudit.lean` | E2, E3, E9, historical E17 counterexample |
| `WCTLean/Models/KoideDerivation.lean` | spin-dependent Koide algebra outside the canonical-ID count |
| `WCTLean/Models/Collider.lean` | collider log-coordinate and winding definitions |

## Status discipline

| Label | Meaning |
|---|---|
| `PROVED` | Lean accepts a theorem under its displayed hypotheses |
| `COUNTEREXAMPLE` | Lean proves a concrete failure of an unrestricted or historical claim |
| `CONDITIONAL` | named assumptions are required |
| `DEFINITION` | an object is introduced but no substantive property is proved |
| `CONTRACT` | an analytical requirement is represented explicitly as a hypothesis-bearing interface |
| `REGISTRY-ONLY` | ID, family, and status compile, but no equation-specific typed support is maintained |
| `TODO` / `OPEN` | no completed theorem closes the obligation |

A SymPy `PASS` must never be reported as a Lean proof. A Lean theorem must never be reported as empirical validation.

## Reproducibility

CI runs:

```bash
lake update
lake exe cache get
python scripts/audit_formal_sources.py
lake build
```

The audit rejects `sorry` and `admit`, verifies the public import closure, hashes every Lean source file, and confirms the pinned dependency graph remains unchanged.
