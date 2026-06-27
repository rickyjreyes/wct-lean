# wct-lean

[![Lean](https://github.com/rickyjreyes/wct-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/rickyjreyes/wct-lean/actions/workflows/lean.yml)

**Author:** Richard J. Reyes  
**Language:** Lean 4 + Mathlib  
**Role:** Kernel-checked formal support for the Wave Confinement Theory equation audit

`wct-lean` formalizes narrow mathematical obligations associated with Wave Confinement Theory (WCT). It contains definitions, theorems, explicit assumptions, and counterexamples that can be checked by the Lean kernel.

It does **not** prove WCT as a physical theory, establish the full WCT PDE program, validate experimental claims, or convert every symbolic `PASS` in `wct-sympy` into a Lean theorem.

## Repository roles

| Repository | Role |
|---|---|
| [`wct-lean`](https://github.com/rickyjreyes/wct-lean) | Kernel-checked definitions, lemmas, counterexamples, and conditional theorems |
| [`wct-sympy`](https://github.com/rickyjreyes/wct-sympy) | Symbolic algebra, dimensional checks, limits, numerical residuals, and executable counterexamples |
| [`geometry_of_resonance`](https://github.com/rickyjreyes/geometry_of_resonance) | Canonical master equations and the corrected 142-object equation registry |

A SymPy `PASS` is not a Lean proof. In this repository, **proved** means accepted by Lean under the assumptions visible in the theorem statement.

## Current compiled scope

`WCTLean/Main.lean` imports the maintained root library:

```text
WCTLean/
├── Dimension.lean
├── Curvature.lean
├── Energy.lean
├── Koide.lean
├── Fourier.lean
├── ResolvedAudit.lean
└── Models/
    ├── CurvatureOperator.lean
    ├── PhaseFlux.lean
    └── RestDensity.lean
```

The root smoke theorem checks the dimensional identity

$$[\hbar/c\cdot k]=M.$$

## Resolved equation-audit obligations

### E2 — Weighted-average denominator

For a finite density family, Lean proves

$$0<\sum_i\rho_i\quad\Longrightarrow\quad\sum_i\rho_i\ne0.$$

Declaration:

```lean
densityWeightedAverage_denominator_ne_zero
```

The real-valued weighted average is declared `noncomputable`, as required for real division in Lean.

### E3 — Locking mismatch

For

$$\mathcal M=\sum_i\rho_i\bigl(\partial_s\varphi_i-\sigma_i\bigr)^2,$$

Lean proves

$$\rho_i\ge0\ \forall i\quad\Longrightarrow\quad\mathcal M\ge0.$$

It also proves exact locking gives zero mismatch.

Declarations:

```lean
lockingMismatch_nonnegative
lockingMismatch_zero
```

### E9 — Conservation residual

For the local residual

$$R_{\mathrm{cons}}=\partial_tu+\nabla\cdot\mathbf S,$$

Lean proves the exact algebraic equivalence

$$R_{\mathrm{cons}}=0\quad\Longleftrightarrow\quad\partial_tu=-\nabla\cdot\mathbf S.$$

Declaration:

```lean
conservationResidual_zero_iff
```

This does not prove that a chosen WCT evolution satisfies the conservation law; it proves the stated residual equivalence.

### E17 — Historical scalar denominator

For the historical scalar denominator

$$D(\psi,\varepsilon,\alpha)=\psi+\varepsilon e^{-\alpha\psi^2},$$

Lean proves the exact counterexample

$$D(-1,1,0)=0.$$

Therefore the unrestricted nonvanishing claim is false.

Lean also proves the corrected admissible sector

$$\psi\ge0\ \land\ \varepsilon>0\quad\Longrightarrow\quad D(\psi,\varepsilon,\alpha)>0,$$

and hence

$$D(\psi,\varepsilon,\alpha)\ne0.$$

Declarations:

```lean
regularizedDenominator_counterexample
regularizedDenominator_positive
regularizedDenominator_ne_zero
resolved_e17_counterexample
```

The canonical equation registry now uses the modulus-squared complex regularizer

$$R_\varepsilon(\psi)=\frac{\overline\psi}{|\psi|^2+\varepsilon^2e^{-2\alpha|\psi|^2}},$$

whose denominator is strictly positive for $\varepsilon>0$. Formalizing this complete complex-valued operator is a separate Lean target; the current E17 module records the historical scalar failure and its conditional repair.

## Other compiled theorem families

### Dimensional algebra

The library formalizes integer-exponent dimensions in mass, length, and time and proves identities including:

```lean
hbar_div_c_mul_k_is_mass
sqrt_inverse_length_squared
sqrt_kappa_sq_dim
weighted_average_preserves_dimension
```

### Energy positivity

The library proves elementary nonnegativity lemmas used as support for energy constructions:

```lean
square_nonnegative
norm_sq_nonnegative
positive_coeff_square_nonnegative
sum_two_nonnegative
positive_quadratic_energy_nonnegative
```

These establish positivity of the encoded finite expressions. They do not prove coercivity, global existence, or Lyapunov descent for the full WCT functional.

### Koide support

The library checks denominator positivity and related algebraic identities under explicit positive-mass assumptions. It does not prove that WCT dynamically derives the measured lepton masses.

### Fourier support

The library includes a product-to-sum theorem and explicit unfinished orthogonality scaffolding. Open work remains marked as `TODO` rather than represented as a completed proof.

## Status discipline

| Label | Meaning |
|---|---|
| `PROVED` | Lean kernel accepts the theorem under its displayed hypotheses |
| `COUNTEREXAMPLE` | Lean proves a concrete input contradicting an unrestricted claim |
| `CONDITIONAL` | Lean proves the conclusion only after named assumptions are supplied |
| `DEFINITION` | The declaration introduces an object but proves no property |
| `TODO` / `OPEN` | No completed Lean theorem currently closes the obligation |

A successful build proves only that the imported Lean declarations type-check. It does not establish empirical truth, physical completeness, PDE well-posedness, or experimental agreement.

## Build

```bash
lake build
```

GitHub Actions runs the Lean build on every push and pull request.

## Documentation

- [`THEOREMS.md`](./THEOREMS.md) — theorem inventory and interpretation
- [`SYMPY_MAP.md`](./SYMPY_MAP.md) — mapping between symbolic audit checks and Lean declarations
- [`WCTLean/Main.lean`](./WCTLean/Main.lean) — maintained root import
- [`WCTLean/ResolvedAudit.lean`](./WCTLean/ResolvedAudit.lean) — compiled equation-audit resolutions
- [`WCT_FULL_EQUATION_LIST_CORRECTED.md`](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/WCT_FULL_EQUATION_LIST_CORRECTED.md) — corrected 142-object equation registry
- [`WCT_MASTER_EQUATIONS_UPDATED.md`](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/WCT_MASTER_EQUATIONS_UPDATED.md) — audited master-equation architecture

## Relationship to the 142-object audit

The current symbolic registry contains

$$51\ \mathrm{PASS}+32\ \mathrm{CONDITIONAL}+23\ \mathrm{DEFINITION}+36\ \mathrm{OPEN}=142.$$

Those are `wct-sympy` audit classifications. They are not counts of Lean proofs. The long-term formal path is

$$\text{paper equation}\rightarrow\text{canonical ID}\rightarrow\text{SymPy audit}\rightarrow\text{Lean theorem or counterexample}\rightarrow\text{CI}.$$

## Remaining high-value obligations

1. Formalize the canonical modulus-squared complex curvature operator.
2. Complete Fourier orthogonality under explicit frequency hypotheses.
3. Extend finite-sum locking results to integral and functional-analytic settings.
4. Separate $L^2$ curvature control from higher-regularity $L^\infty$ control.
5. Formalize corrected Shannon entropy/support inequalities.
6. Prove finite-band selector properties for the Swift–Hohenberg sector.
7. Develop PDE existence, regularity, coercivity, and stability results without hiding assumptions.

## Legacy contract

The repository also contains the earlier `MyProject/` abstract $\Theta$-contract. It should be read as a legacy axiomatic specification, not as proof that a physical WCT operator satisfies those axioms. The maintained concrete equation formalization is under `WCTLean/`.

## Scientific scope

This repository is a formal audit layer. Its strongest present contribution is not a proof of the full theory, but a machine-checkable separation among:

- algebraically proved support results;
- explicit counterexamples;
- conditional theorems;
- definitions;
- unresolved analytical and empirical claims.

That separation is the standard by which future WCT formalization should be evaluated.
