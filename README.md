# wct-lean

[![Lean](https://github.com/rickyjreyes/wct-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/rickyjreyes/wct-lean/actions/workflows/lean.yml)

**Author:** Richard J. Reyes  
**Language:** Lean 4.23.0 + Mathlib 4.23.0  
**Role:** Kernel-checked formal support and complete canonical inventory for Wave Confinement Theory

`wct-lean` separates four layers:

1. **canonical registration** — an equation ID occurs in the compiled registry;
2. **typed representation** — Lean contains an equation-specific definition, proposition, contract, or counterexample;
3. **kernel proof** — Lean accepts a theorem under its displayed hypotheses;
4. **physical validation** — an empirical claim is supported by experiment or observation.

Only layer 3 is a Lean proof. This repository does not prove WCT as a complete physical theory, establish the full nonlinear PDE program, or turn a symbolic `PASS` into empirical validation.

## Current state

The public root compiles all 142 canonical objects:

```text
9 master systems
83 canonical equations
10 curvature-locked electron equations
5 auxiliary equations
20 cosmology equations
9 topology equations
6 correction equations
142 total
```

Lean proves registry length, uniqueness, family assignment, status assignment, and partition completeness.

The inherited symbolic-audit partition is:

```text
59 PASS
27 CONDITIONAL
26 DEFINITION
30 OPEN
142 total
```

These are symbolic classifications, not Lean theorem counts.

## Typed Lean support

The maintained library now has non-registry equation-specific support for **62 of 142 IDs**:

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

The remaining **80 IDs** are registry-only. Registry-only means inventoried and classified, not false.

The support strength varies by object:

- exact algebraic theorem;
- finite-dimensional analogue;
- dimensional theorem;
- conditional theorem;
- analytic contract;
- definition;
- counterexample;
- unresolved proposition.

See [`FORMAL_COVERAGE_INDEX.md`](FORMAL_COVERAGE_INDEX.md) for the complete partition and [`THEOREMS.md`](THEOREMS.md) for the declaration-level inventory.

## Newly closed algebraic results

`WCTLean/Models/ClosedResults.lean` now kernel-checks the following narrow results:

- strict positivity of the corrected modulus-squared reciprocal denominator for `ε > 0`;
- the pure-gauge no-go result for a single smooth Abelian scalar phase when mixed derivatives commute;
- equivalence between exact loop locking and zero winding mismatch;
- algebraic decomposition of the winding-corrected conditional mass law;
- the exact logarithmic-frequency/discrete-scale relation `log(exp(2π/k)) = 2π/k`;
- positivity of the associated scaling ratio.

These results close algebraic obligations only. They do not prove existence or stability of a full WCT confined mode, establish a universal physical mass law, derive a non-Abelian gauge theory, quantize WCT, or complete gravitational backreaction.

## Non-shallow mapping batch

The current expansion adds substantive support for twelve previously registry-only IDs.

### M4 — dimensional threshold

Lean proves

```text
n < 4 ↔ n ≤ 3
```

for natural-number spatial dimension. The actual Sobolev embedding and curvature-boundedness statements remain explicit contract fields rather than hidden assumptions.

### M5 and E36 — bounded averaged dynamics

For

```text
T(x) = (1-λ)x + λ A(x),    0 ≤ λ ≤ 1,
```

Lean proves:

- fixed points of `A` remain fixed under `T`;
- if `‖A(x)‖ ≤ ‖x‖`, then `‖T(x)‖ ≤ ‖x‖`;
- an encoded norm-bounded resource ball is forward invariant.

These are finite-dimensional update theorems, not complexity-class results.

### M6B — nonlinear curvature operator

Lean represents

```text
N_curv(ψ) = (-Δψ · conjugate ψ) /
            (|ψ|² + ε² exp(-2 α |ψ|²))
```

and proves exact equality with the typed `thetaComplex` definition together with denominator nonvanishing for `ε > 0`.

This does not prove uniqueness of the nonlinear closure, local existence, or global PDE regularity.

### E10 and E11 — quantization closure

Lean proves that radial shell quantization and winding quantization are closed under addition of phase integrals and integer indices. It also proves that both predicates instantiate the same integer quantization law once the geometric observable is fixed.

### E29 — entropy-pruning bound

For nonnegative mode count `K`, Lean proves:

```text
0 ≤ K exp(-ΔH)
ΔH ≥ 0  →  K exp(-ΔH) ≤ K
ΔH₁ ≤ ΔH₂  →  K exp(-ΔH₂) ≤ K exp(-ΔH₁)
```

This does not derive `ΔH` from the full field dynamics.

### G1 — bounded ghost mode

Lean proves the global scalar bound

```text
|A cos(k log(E/E₀)+φ)| ≤ |A|.
```

No empirical fit or physical-origin claim is encoded.

### EX, EY, EZ, and FA — logarithmic-flow bridge

Lean proves:

- `exp(log ψ) = ψ` on the positive real sector;
- the diffusion residual factors as the field times the logarithmic residual under displayed temporal and Laplacian chain-rule hypotheses;
- the two residuals vanish simultaneously on a nonzero field sector;
- the filament-localization condition is equivalent to zero scalar mismatch.

These are exact algebraic bridges. The required function-space differentiability and PDE theorems remain open.

## Maintained compiled root

`WCTLean/Main.lean` imports:

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
    ├── CompactDynamics.lean
    └── ClosedResults.lean
```

## Canonical sources

- [Complete Lean coverage index](FORMAL_COVERAGE_INDEX.md)
- [Exact theorem inventory](THEOREMS.md)
- [SymPy-to-Lean map](SYMPY_MAP.md)
- [Corrected 142-object equation registry](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/WCT_FULL_EQUATION_LIST_CORRECTED.md)
- [Audited master-equation architecture](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/WCT_MASTER_EQUATIONS_UPDATED.md)
- [Complete SymPy audit](https://github.com/rickyjreyes/wct-sympy/blob/main/VERIFICATION_INDEX.md)
- [Public research-corpus map](https://rickyjreyes.github.io/research-corpus/)

The `geometry_of_resonance` registry remains the source of equation text, notation, and scientific boundaries. `wct-lean` is the kernel-checked formal layer.

## Build and reproducibility

```bash
lake update
lake exe cache get
python scripts/audit_formal_sources.py
lake build
```

The maintained source audit rejects `sorry` and `admit`, verifies public import closure, emits SHA-256 hashes for every Lean source file, and confirms the pinned dependency graph remains unchanged.

## Remaining mathematical closure

The highest-value unresolved work is:

1. exact functional variation of the full WCT action, including denominator derivatives and higher-order terms;
2. admissible function spaces and boundary conditions;
3. local and global well-posedness for the full nonlinear evolution;
4. existence, localization, finite energy, decay, and non-box-induced confinement;
5. linearized spectrum and orbital or Lyapunov stability under nonsymmetric perturbations;
6. control of the regularized quotient as `ε → 0`;
7. full Fourier orthogonality and spectral projection on function spaces;
8. curve-integral locking on manifolds;
9. theorem-level bridges from confined solutions to physical mass, force, gauge, gravity, cosmology, and experiments.

## Scientific boundary

A green Lean build means the encoded declarations are syntactically valid, type-correct, and accepted by the Lean kernel under explicit hypotheses. It does not establish that the hypotheses hold in nature or that WCT is empirically correct.
