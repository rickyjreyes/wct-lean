# Frozen D4 formalization boundary

Source: geometry_of_resonance PR36 head `31f322c94d2ef32b20acea741884514806025c85`, merge `5a4c58a4206005ad9d46ee2951069186490b01f1`.

The exact dyadic threshold comparison is fully instantiated. Scalar square completion, dilation minimization, virial and improved-D algebra, Sobolev-cap consequences, amplitude comparison, passage through minimizing sequences, quantitative energy-per-mass gap, and all-split binding are formal implications with explicit hypotheses. The frozen `I2` specialization uses actual whole-plane Lebesgue integral expressions over an explicitly supplied H² carrier and weak Laplacian.

The package also derives an attained infimum from a translated convergent minimizing subsequence. Compactness is requested at the one target mass, not all masses. A separate conservation/trapping argument yields all-time control for same-mass initial data in an arbitrary state space. It imposes no radial or D4 perturbation restriction. It does not yet instantiate the H² distance to the full minimizing set or cover nearby masses.

`BindingSequenceInputs` does not assume binding. `VariationalCompactnessInputs` does not assume a minimizer. Neither is claimed to have been instantiated for the source PDE. Definitions, typed inputs, conditional theorems, fully instantiated arithmetic and open analysis are enumerated in THEOREMS.md and FORMAL_COVERAGE_INDEX.md.

OPEN: actual Sobolev infrastructure; Fourier estimate; functional dilation/change of variables and integral identities; negative and adjusted minimizing sequences; exclusion of vanishing/dichotomy; compactness modulo translations; Euler–Lagrange regularity; global H² evolution and the full minimizing-set orbital-stability application. Issues #20/#21 remain open. No periodic-root identification or S004 completion follows.

## Reproduction

Lean `leanprover/lean4:v4.23.0`; Mathlib locked by lake-manifest.json.

```bash
lake update
lake exe cache get
python3 scripts/audit_formal_sources.py
lake build
lake env lean scripts/d4_axiom_audit.lean
```

A preliminary local module check succeeded before workspace maintenance removed the runtime. Full hosted CI and its diagnostics are the durable verification record. The old draft head had compile errors; those failures are retained in CI history. Final build status is recorded separately in `docs/evidence/d4_phase_vi/verification.json`.
