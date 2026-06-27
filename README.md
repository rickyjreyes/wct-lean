# wct-lean

[![Lean](https://github.com/rickyjreyes/wct-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/rickyjreyes/wct-lean/actions/workflows/lean.yml)

**Author:** Richard J. Reyes  
**Language:** Lean 4 + Mathlib  
**Role:** Kernel-checked formal support for the Wave Confinement Theory equation audit

`wct-lean` formalizes narrow mathematical obligations associated with Wave Confinement Theory. A declaration is called proved only when the Lean kernel accepts it under the hypotheses displayed in its theorem statement.

It does **not** prove WCT as a physical theory, establish the complete nonlinear PDE program, validate experiments, or convert every `wct-sympy` `PASS` into an unconditional theorem.

## Repository roles

| Repository | Role |
|---|---|
| `wct-lean` | Kernel-checked definitions, lemmas, counterexamples, and conditional theorems |
| `wct-sympy` | Symbolic algebra, dimensions, limits, residuals, and executable counterexamples |
| `geometry_of_resonance` | Canonical master equations and equation registry |

## Maintained compiled root

`WCTLean/Main.lean` imports:

```text
WCTLean/
├── Dimension.lean
├── Curvature.lean
├── Energy.lean
├── Koide.lean
├── Fourier.lean
├── ResolvedAudit.lean
├── DerivedAudit.lean
└── Models/
    ├── CurvatureOperator.lean
    ├── PhaseFlux.lean
    └── RestDensity.lean
```

## Derived audit batch 1

### E5 — Effective-wavenumber chain

Define

$$
k_{\mathrm{eff}}=\frac{2\pi|n|}{L_s}.
$$

Under exact closure

$$
\oint_\Gamma\sigma\,ds=2\pi|n|
$$

and constant positive weight, Lean proves the algebraic chain

$$
k_{\mathrm{eff}}
=
\frac{1}{L_s}\oint_\Gamma\sigma\,ds
=
\langle\sigma\rangle_w.
$$

Declarations:

```lean
effectiveWavenumber_eq_loopAverage
constantWeightedAverage_eq_loopAverage
resolved_e5_effectiveWavenumber_chain
```

This is conditional on exact closure and constant weight. It does not prove that the full field dynamics reaches that state.

### E9 — Polar phase current

For the pointwise polar product

$$
\overline\psi\,\partial_x\psi
=
\frac12\partial_xu+i\,u\partial_x\theta,
$$

Lean proves

$$
\operatorname{Im}(\overline\psi\,\partial_x\psi)
=u\partial_x\theta.
$$

Declarations:

```lean
polarCurrentProduct_im
phaseCurrent_of_polar_factorization
```

The second theorem exposes the polar derivative factorization as a hypothesis rather than hiding an unformalized differentiability argument.

### E13/E14 — One-mode band-pass symbol

Lean proves the exact polynomial reduction

$$
rA-a(-k^2A)-b(k^4A)
=
(r+ak^2-bk^4)A.
$$

Declaration:

```lean
bandpass_oneMode_symbol
```

This verifies the one-mode operator symbol. It is not yet the generalized Euler-Lagrange theorem for the full functional.

### E18 — Positivity and gradient-flow sign

Lean proves

$$
c_1G+c_2C\ge0
$$

from

$$
c_1,c_2,G,C\ge0.
$$

It also proves

$$
\dot E=-V,
\qquad
V\ge0
\quad\Longrightarrow\quad
\dot E\le0.
$$

Declarations:

```lean
resolved_e18_energy_nonnegative
resolved_e18_gradientFlow_descent
```

The full functional chain rule remains an explicit analytical obligation.

### E58 — Band-selective Green kernel

For

$$
G(k)=\frac{1}{r+a(k^2-k_*^2)^2},
\qquad
r>0,\ a\ge0,
$$

Lean proves

$$
0<G(k)\le\frac1r,
$$

and

$$
G(k_*)=\frac1r.
$$

Declarations:

```lean
bandGreenDenominator_pos
bandGreenDenominator_ge_offset
bandGreenKernel_pos
bandGreenKernel_le_inverseOffset
bandGreenKernel_at_shell
```

### CM9 — First-order/second-order equivalence

Lean proves that the photon and baryon second-order oscillator equations are algebraically equivalent to their first-order acceleration forms after velocity rate is identified with acceleration.

Declarations:

```lean
photonSecondOrder_iff_firstOrder
baryonSecondOrder_iff_firstOrder
```

### CM12, CM13, CM16 — Definitions

Lean now defines:

```lean
dimensionlessPowerSpectrum
peakPowerRatio21
peakPowerRatio31
peakScaleRatio21
peakScaleRatio31
horizonWavenumber
```

These are definitions, not theorem-level physical validations.

## Earlier resolved obligations

### E2 — Weighted-average denominator

Lean proves

$$
0<\sum_i\rho_i
\quad\Longrightarrow\quad
\sum_i\rho_i\ne0.
$$

Declaration: `densityWeightedAverage_denominator_ne_zero`.

### E3 — Locking mismatch

For

$$
\mathcal M=\sum_i\rho_i(\partial_s\varphi_i-\sigma_i)^2,
$$

Lean proves nonnegativity for nonnegative weights and zero mismatch under exact finite locking.

Declarations: `lockingMismatch_nonnegative`, `lockingMismatch_zero`.

### E9 — Conservation residual

Lean proves

$$
\partial_tu+\nabla\cdot\mathbf S=0
\quad\Longleftrightarrow\quad
\partial_tu=-\nabla\cdot\mathbf S.
$$

Declaration: `conservationResidual_zero_iff`.

### E17 — Historical scalar denominator

For

$$
D(\psi,\varepsilon,\alpha)
=
\psi+\varepsilon e^{-\alpha\psi^2},
$$

Lean proves

$$
D(-1,1,0)=0,
$$

and separately proves positivity on the restricted sector

$$
\psi\ge0,
\qquad
\varepsilon>0.
$$

Declarations:

```lean
regularizedDenominator_counterexample
regularizedDenominator_positive
regularizedDenominator_ne_zero
resolved_e17_counterexample
```

The complete modulus-squared complex regularizer remains a separate formalization target.

## Status discipline

| Label | Meaning |
|---|---|
| `PROVED` | Lean accepts the theorem under displayed hypotheses |
| `COUNTEREXAMPLE` | Lean proves a concrete contradiction to an unrestricted claim |
| `CONDITIONAL` | The theorem requires named assumptions |
| `DEFINITION` | The declaration introduces an object but proves no property |
| `TODO` / `OPEN` | No completed Lean theorem closes the obligation |

## Relation to the symbolic registry

The current `wct-sympy` registry reports

$$
59\ \mathrm{PASS}
+27\ \mathrm{CONDITIONAL}
+26\ \mathrm{DEFINITION}
+30\ \mathrm{OPEN}
=142.
$$

These are symbolic-audit classifications, not Lean-proof counts.

The formal path is

$$
\text{paper equation}
\rightarrow
\text{canonical ID}
\rightarrow
\text{SymPy audit}
\rightarrow
\text{Lean theorem, definition, or counterexample}
\rightarrow
\text{CI}.
$$

## Remaining high-value obligations

1. Complete the modulus-squared complex curvature operator.
2. Formalize the full polar differentiation theorem for `psi = sqrt(u) exp(i theta)`.
3. Prove the E13/E14 generalized Euler-Lagrange derivative.
4. Prove the E18 functional chain rule and coercivity conditions.
5. Prove the CM11 time-dependent diffusion ODE solution.
6. Complete Fourier orthogonality.
7. Extend finite locking to curve integrals and functional analysis.
8. Formalize entropy/support inequalities.
9. Develop PDE existence, regularity, uniqueness, and stability results without hidden assumptions.

## Build

```bash
lake build
```

GitHub Actions runs the Lean build on every push and pull request.

## Documentation

- [`THEOREMS.md`](./THEOREMS.md)
- [`SYMPY_MAP.md`](./SYMPY_MAP.md)
- [`WCTLean/DerivedAudit.lean`](./WCTLean/DerivedAudit.lean)
- [`WCTLean/ResolvedAudit.lean`](./WCTLean/ResolvedAudit.lean)
- [`WCTLean/Main.lean`](./WCTLean/Main.lean)

## Scientific boundary

The repository provides machine-checkable separation among proved algebraic support, counterexamples, conditional theorems, definitions, and unresolved analytical or empirical claims. It does not establish the empirical truth or physical completeness of WCT.
