# WCT Lean Formal Coverage Index

This index distinguishes **canonical registration** from **typed Lean support** and **kernel-proved content**.

## Canonical navigation

- [Corrected 142-object equation registry](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/WCT_FULL_EQUATION_LIST_CORRECTED.md)
- [Master equation architecture](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/WCT_MASTER_EQUATIONS_UPDATED.md)
- [Complete SymPy classification](https://github.com/rickyjreyes/wct-sympy/blob/main/VERIFICATION_INDEX.md)
- [Lean theorem inventory](THEOREMS.md)
- [SymPy-to-Lean map](SYMPY_MAP.md)
- [Public research-corpus map](https://rickyjreyes.github.io/research-corpus/)

The canonical equation registry defines equation text, symbols, assumptions, and scientific boundaries. Lean claims only what its declarations encode and what the kernel accepts under displayed hypotheses.

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

Lean proves:

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

The effective status partition is compiled as:

| Symbolic-audit status | Count |
|---|---:|
| `PASS` | 59 |
| `CONDITIONAL` | 27 |
| `DEFINITION` | 26 |
| `OPEN` | 30 |
| **Total** | **142** |

These are inherited symbolic-audit classifications. They are not Lean theorem counts.

## Layer 2 — Non-registry typed Lean support: 50 IDs

The following IDs have a maintained Lean definition, proposition, theorem, counterexample, or analytic contract beyond registry metadata:

```text
M1 M2 M3 M6A M7
E1A E1B E2 E3 E4 E5 E6 E7 E8 E9
E12 E13 E14 E17 E18 E20
E24 E25 E26 E27 E28 E33
E45 E47 E49 E51 E53
E57 E58 E59 E61 E62 E64
E65 E66 E67 E68 E69 E70
E78 E81
CM9 CM12 CM13 CM16
```

### Direct algebraic or order-theoretic theorem support

```text
M1 M2 M3 M7
E2 E3 E4 E5 E8 E9
E12 E13 E14 E17 E18 E20 E28 E33
E45 E47 E49 E51 E53
E57 E58 E59 E61 E62 E64 E81
CM9
```

This category includes conditional theorems and finite analogues. It does not imply full PDE, variational, or physical closure.

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
E24 E26 E66 E67 E68 E69 E70
```

The contracts expose missing Sobolev, regularity, interpolation, and stability hypotheses rather than assuming them silently.

### Counterexample or unresolved proposition support

```text
E17 E78
```

E17 includes both the historical scalar-denominator counterexample and the corrected complex denominator theorem. E78 remains an adjacent proposition/TODO rather than a completed Fisher-information theorem.

## Layer 3 — Registry-only coverage: 92 IDs

The remaining 92 IDs are compiled with family and status metadata but do not yet have a maintained equation-specific typed declaration that captures their substantive mathematical content.

Registry-only does **not** mean false. It means the ID is inventoried and classified, but its formula or claim has not yet been closed in Lean.

## Major compiled modules

| Module | Principal coverage |
|---|---|
| `WCTLean/Registry.lean` | all 142 IDs, families, effective statuses, completeness proofs |
| `WCTLean/Models/ComplexCurvature.lean` | corrected M2/E17 complex regularizer and global denominator positivity |
| `WCTLean/Models/Locking.lean` | M1, E3, E4, E8 finite locking algebra |
| `WCTLean/Models/BandPass.lean` | M3, M7, E12, E57, E61, E64 finite-band algebra |
| `WCTLean/Models/AlgebraicChecks.lean` | E20, E28, E33, E45, E47, E49, E51, E53, E59, E62, E81 |
| `WCTLean/Contracts/Analytic.lean` | E24–E27 and E65–E70 analytic boundaries/contracts |
| `WCTLean/DerivedAudit.lean` | E5, E9, E13/E14, E18, E58, CM9, CM12, CM13, CM16 |
| `WCTLean/ResolvedAudit.lean` | E2, E3, E9, historical E17 counterexample |
| `WCTLean/Models/KoideDerivation.lean` | spin-dependent Koide algebra outside the canonical-ID count |
| `WCTLean/Models/GhostModes.lean` | bounded ghost-mode and smearing definitions |
| `WCTLean/Models/Collider.lean` | collider log-coordinate and winding definitions |
| `WCTLean/Models/CompactDynamics.lean` | contractive-update norm bound |

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
