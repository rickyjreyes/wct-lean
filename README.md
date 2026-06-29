# wct-lean

[![Lean](https://github.com/rickyjreyes/wct-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/rickyjreyes/wct-lean/actions/workflows/lean.yml)

**Author:** Richard J. Reyes  
**Language:** Lean 4.23.0 + Mathlib 4.23.0  
**Role:** Kernel-checked formal support and complete canonical inventory for Wave Confinement Theory

`wct-lean` separates four different things that must not be conflated:

1. **canonical registration** — an equation ID is present in the compiled Lean registry;
2. **typed representation** — Lean contains a definition, proposition, contract, or counterexample for the equation;
3. **kernel proof** — Lean accepts a theorem under its displayed hypotheses;
4. **physical validation** — an empirical claim is supported by experiment or observation.

Only item 3 is a Lean proof. This repository does not prove WCT as a complete physical theory, establish the full nonlinear PDE program, or convert a symbolic `PASS` into empirical validation.

## Current state

The public root now compiles a **142-object canonical registry**:

$$
9\ \text{master}
+83\ \text{canonical}
+10\ \text{electron}
+5\ \text{auxiliary}
+20\ \text{cosmology}
+9\ \text{topology}
+6\ \text{correction}
=142.
$$

Lean proves that:

- the registry has length `142`;
- all IDs are unique;
- every registered ID has exactly one family;
- every registered ID has an effective audit status;
- the status partition is complete and duplicate-free;
- the compiled status counts are

$$
59\ \mathrm{PASS}
+27\ \mathrm{CONDITIONAL}
+26\ \mathrm{DEFINITION}
+30\ \mathrm{OPEN}
=142.
$$

These status counts reproduce the corrected symbolic audit. They are **not Lean theorem counts**.

The maintained source audit rejects `sorry` and `admit`, verifies the public import closure, records SHA-256 hashes for every Lean source file, and checks the pinned dependency graph.

## Canonical sources

- [Complete Lean coverage index](FORMAL_COVERAGE_INDEX.md)
- [Exact theorem inventory](THEOREMS.md)
- [Corrected 142-object equation registry](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/WCT_FULL_EQUATION_LIST_CORRECTED.md)
- [Audited master-equation architecture](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/WCT_MASTER_EQUATIONS_UPDATED.md)
- [Complete SymPy audit](https://github.com/rickyjreyes/wct-sympy/blob/main/VERIFICATION_INDEX.md)
- [Public research-corpus map](https://rickyjreyes.github.io/research-corpus/)

The `geometry_of_resonance` registry remains the source of equation text, notation, and scientific boundaries. `wct-lean` is the kernel-checked formal layer.

## Maintained compiled root

`WCTLean/Main.lean` imports the complete maintained library:

```text
WCTLean/
├── Registry.lean
├── Dimension.lean
├── Curvature.lean
├── Energy.lean
├── Koide.lean
├── Fourier.lean
├── ResolvedAudit.lean
├── DerivedAudit.lean
├── Contracts/
│   └── Analytic.lean
└── Models/
    ├── CurvatureOperator.lean
    ├── ComplexCurvature.lean
    ├── PhaseFlux.lean
    ├── RestDensity.lean
    ├── Locking.lean
    ├── BandPass.lean
    ├── AlgebraicChecks.lean
    ├── LogFlow.lean
    ├── GhostModes.lean
    ├── Collider.lean
    ├── KoideDerivation.lean
    ├── UnifiedOperator.lean
    └── CompactDynamics.lean
```

## Major formal additions

### Complete canonical registry

`WCTLean/Registry.lean` gives every canonical object a compiled ID, family, and effective symbolic-audit status. The following are kernel-checked:

```lean
allEquationIds_length
allEquationIds_nodup
statusPartition_length
statusPartition_nodup
statusPartition_complete
every_registered_id_has_status
every_registered_id_has_family
canonicalRegistry_length
```

Registration records coverage and status; it does not prove the equation represented by an ID.

### Corrected complex curvature denominator — M2 / E17

The corrected denominator is

$$
D_\varepsilon(\psi)
=
|\psi|^2+\varepsilon^2e^{-2\alpha|\psi|^2}.
$$

For `ε > 0`, Lean proves

$$
D_\varepsilon(\psi)>0
$$

for every complex `ψ`, including nodes. This formally replaces the historical scalar denominator that admits zeros.

Key declarations:

```lean
complexRegularizerDenominator_positive
complexRegularizerDenominator_ne_zero
complexRegularizerDenominator_at_zero
complexRegularizedReciprocal_at_zero
```

### Curvature-phase locking — M1 / E3 / E4 / E8

Lean formalizes the finite locking action, its nonnegativity, the E4 integration constant, the winding-closure algebra, and the corrected weighted E8 identity.

Key declarations:

```lean
alphaLock_closure
pointwiseLocked_weighted
correctedWeightedLockIdentity
finiteLockingAction_nonnegative
finiteLockingAction_zero
```

These are finite algebraic theorems. Curve-integral existence and variational regularity remain separate analytical obligations.

### Finite-band selector — M3 / M7 / E12 / E57 / E61 / E64

For

$$
-b(k^2-k_\star^2)^2,
\qquad b\ge0,
$$

Lean proves nonpositive off-shell contribution, strict damping away from the shell when `b > 0`, zero shell penalty, the completed-square form of the quartic growth law, and positivity of the corrected selected wavelength.

Key declarations:

```lean
finiteBandPenalty_nonpositive
finiteBandPenalty_strict_off_shell
swiftHohenbergLinearSymbol_le_mu
swiftHohenbergLinearSymbol_at_shell
quarticGrowthSymbol_completedSquare
selectedWavelength_positive
```

### Canonical algebraic checks

`WCTLean/Models/AlgebraicChecks.lean` contains kernel proofs supporting:

- E20 cavity-sector positive semidefiniteness;
- E28 corrected alpha-drop implication;
- E33 corrected entropy/support direction;
- E45 quality-factor positivity;
- E47 stationary power balance;
- E49 effective-mass gap identity;
- E51 curvature-gradient commutator;
- E53 curvature-pressure nonnegativity;
- E59 projection idempotence;
- E62 spectral-energy fraction bounds.

### Analytic contracts

`WCTLean/Contracts/Analytic.lean` distinguishes arithmetic consequences from unproved functional analysis. It formalizes the integer threshold

$$
n<4\iff n\le3,
$$

and packages Sobolev embedding, curvature boundedness, Gagliardo-Nirenberg, localized-energy, and dimensional-stability assumptions as explicit contracts rather than hidden premises.

## Support layers

The repository currently has non-registry typed support for 50 canonical IDs:

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

The strength varies by ID: theorem, conditional theorem, counterexample, definition, analytic contract, or TODO proposition. See [FORMAL_COVERAGE_INDEX.md](FORMAL_COVERAGE_INDEX.md) and [THEOREMS.md](THEOREMS.md) for the exact boundary.

## Build and reproducibility

```bash
lake update
lake exe cache get
python scripts/audit_formal_sources.py
lake build
```

GitHub Actions performs the same sequence on every pull request and push to `main`. CI also verifies that `lake-manifest.json`, `lean-toolchain`, and `lakefile.lean` remain unchanged after dependency resolution.

## Remaining mathematical closure

The registry is complete; the research program is not. The highest-value unresolved formal work is:

1. exact functional variation of the full WCT action, including denominator derivatives and higher-order terms;
2. admissible function spaces and boundary conditions;
3. local and global well-posedness for the full nonlinear evolution;
4. existence, localization, finite-energy, decay, and non-box-induced confinement;
5. linearized spectrum and orbital or Lyapunov stability under nonsymmetric perturbations;
6. control of the regularized quotient as `ε → 0`;
7. full Fourier orthogonality and spectral projection on function spaces;
8. curve-integral locking on manifolds;
9. theorem-level bridges from confined solutions to physical mass, force, gauge, gravity, cosmology, and experiments.

## Scientific boundary

A green Lean build means the encoded declarations are syntactically valid, type-correct, and accepted by the Lean kernel under their explicit hypotheses. It does not establish that the hypotheses hold in nature or that WCT is empirically correct.
