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

Layer 3 is the kernel-checked proof layer. The broader WCT program links this formal layer to separate nonlinear-PDE, computational, and empirical evidence tracks.

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
68 PASS
18 CONDITIONAL
26 DEFINITION
30 OPEN
142 total
```

These are symbolic classifications, with Lean theorem coverage tracked separately below.

## Typed Lean support

The maintained library now has non-registry equation-specific support for **80 of 142 IDs**:

```text
M1 M2 M3 M4 M5 M6A M6B M7
E1A E1B E2 E3 E4 E5 E6 E7 E8 E9 E10 E11
E12 E13 E14 E16 E17 E18 E19 E20 E22
E24 E25 E26 E27 E28 E29 E32 E33 E36 E37 E38 E41
E45 E47 E49 E50 E51 E53
E57 E58 E59 E61 E62 E64
E65 E66 E67 E68 E69 E70 E72
E78 E81
CLE4 CLE5 CLE8 CLE9 CLE10
G1 EX EY EZ FA
CM9 CM11 CM12 CM13 CM16
TOP3 TOP7 CORR2
```

The remaining **62 IDs** are registry-only, preserving complete inventory and classification coverage while equation-specific formalization continues.

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

The latest merged expansion adds 18 IDs beyond the original 62-ID baseline, including exact or conditional support for `E16`, `E19`, `E22`, `E32`, `E37`, `E38`, `E41`, `E50`, `E72`, `CLE4`, `CLE5`, `CLE8`, `CLE9`, `CLE10`, `CM11`, `TOP3`, `TOP7`, and `CORR2`. These entries span exact results, conditional results, constraints, and diagnostics with their strength recorded individually.

## Newly closed algebraic results

`WCTLean/Models/ClosedResults.lean` now kernel-checks the following narrow results:

- strict positivity of the corrected modulus-squared reciprocal denominator for `ε > 0`;
- the pure-gauge no-go result for a single smooth Abelian scalar phase when mixed derivatives commute;
- equivalence between exact loop locking and zero winding mismatch;
- algebraic decomposition of the winding-corrected conditional mass law;
- the exact logarithmic-frequency/discrete-scale relation `log(exp(2π/k)) = 2π/k`;
- positivity of the associated scaling ratio.

These results close named algebraic obligations. Existence and stability of confined modes, universal physical mass laws, non-Abelian gauge structure, quantization, and gravitational backreaction are maintained as separate formal and physical workstreams.

## Non-shallow mapping batch

The current expansion adds substantive support for twelve previously registry-only IDs.

### M4 — dimensional threshold

Lean proves

```text
n < 4 ↔ n ≤ 3
```

for natural-number spatial dimension. The Sobolev embedding and curvature-boundedness statements remain explicit contract fields for direct formalization.

### M5 and E36 — bounded averaged dynamics

For

```text
T(x) = (1-λ)x + λ A(x),    0 ≤ λ ≤ 1,
```

Lean proves:

- fixed points of `A` remain fixed under `T`;
- if `‖A(x)‖ ≤ ‖x‖`, then `‖T(x)‖ ≤ ‖x‖`;
- an encoded norm-bounded resource ball is forward invariant.

These are finite-dimensional update theorems; complexity-class analysis is maintained as a separate layer.

### M6B — nonlinear curvature operator

Lean represents

```text
N_curv(ψ) = (-Δψ · conjugate ψ) /
            (|ψ|² + ε² exp(-2 α |ψ|²))
```

and proves exact equality with the typed `thetaComplex` definition together with denominator nonvanishing for `ε > 0`.

Uniqueness of the nonlinear closure, local existence, and global PDE regularity remain explicit PDE-analysis targets.

### E10 and E11 — quantization closure

Lean proves that radial shell quantization and winding quantization are closed under addition of phase integrals and integer indices. It also proves that both predicates instantiate the same integer quantization law once the geometric observable is fixed.

### E29 — entropy-pruning bound

For nonnegative mode count `K`, Lean proves:

```text
0 ≤ K exp(-ΔH)
ΔH ≥ 0  →  K exp(-ΔH) ≤ K
ΔH₁ ≤ ΔH₂  →  K exp(-ΔH₂) ≤ K exp(-ΔH₁)
```

Derivation of `ΔH` from the full field dynamics is tracked as a separate analytical obligation.

### G1 — bounded ghost mode

Lean proves the global scalar bound

```text
|A cos(k log(E/E₀)+φ)| ≤ |A|.
```

This declaration encodes the exact scalar bound; empirical fitting and physical-origin analysis are tracked in the corresponding phenomenology work.

### EX, EY, EZ, and FA — logarithmic-flow bridge

Lean proves:

- `exp(log ψ) = ψ` on the positive real sector;
- the diffusion residual factors as the field times the logarithmic residual under displayed temporal and Laplacian chain-rule hypotheses;
- the two residuals vanish simultaneously on a nonzero field sector;
- the filament-localization condition is equivalent to zero scalar mismatch.

These are exact algebraic bridges. Function-space differentiability and PDE closure remain named targets for the analytical layer.

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

The `geometry_of_resonance` registry remains the source of equation text, notation, and claim scope. `wct-lean` is the kernel-checked formal layer.

## Build and reproducibility

```bash
lake update
lake exe cache get
python scripts/audit_formal_sources.py
lake build
```

The maintained source audit rejects `sorry` and `admit`, verifies public import closure, emits SHA-256 hashes for every Lean source file, and confirms the pinned dependency graph remains unchanged.

## Next mathematical closure targets

The highest-value open work is:

1. exact functional variation of the full WCT action, including denominator derivatives and higher-order terms;
2. admissible function spaces and boundary conditions;
3. local and global well-posedness for the full nonlinear evolution;
4. existence, localization, finite energy, decay, and non-box-induced confinement;
5. linearized spectrum and orbital or Lyapunov stability under nonsymmetric perturbations;
6. control of the regularized quotient as `ε → 0`;
7. full Fourier orthogonality and spectral projection on function spaces;
8. curve-integral locking on manifolds;
9. theorem-level bridges from confined solutions to physical mass, force, gauge, gravity, cosmology, and experiments.

## Build meaning

A green Lean build means the encoded declarations are syntactically valid, type-correct, and accepted by the Lean kernel under explicit hypotheses. Empirical support and physical interpretation are tracked in the corresponding WCT experimental and phenomenological layers.