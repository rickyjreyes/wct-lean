# SYMPY_MAP

This file maps the nearby `wct-sympy` symbolic-audit checks to the Lean
theorems in `WCTLean/` that formalize a corresponding dimensional or
domain-safety statement.

The Lean side covers **structural** claims: dimensions match, denominators
are positive, energies are nonnegative. It does **not** restate numerical
equalities that `wct-sympy` checks by symbolic substitution.

## D1_10 — `m = ℏ/c · k_eff`

- **`wct-sympy` audit check:** dimensional consistency of the closure
  `m = (ℏ / c) · k_eff`.
- **Lean theorem:** `hbar_div_c_mul_k_is_mass`
  (`WCTLean/Dimension.lean`).
- **Meaning:** dimensional mass closure — `(actionDim / velocityDim) ·
  inverseLengthDim = massDim`, i.e. `(1, 2, -1) − (0, 1, -1) + (0, -1, 0) =
  (1, 0, 0)`.

## CURV1 — `σ = √(κ² + τ²)`

- **`wct-sympy` audit check:** the combined curvature magnitude carries
  inverse-length dimension.
- **Lean theorems:**
  - `sqrt_inverse_length_squared` (`WCTLean/Curvature.lean`)
  - `sqrt_kappa_sq_dim` (`WCTLean/Curvature.lean`)
  - Supporting: `kappa_sq_dim`, `tau_sq_dim`.
- **Meaning:** curvature magnitude has inverse-length dimension. At the
  integer-exponent level `sqrtDim(L⁻²) = some L⁻¹`, and the same holds when
  the input is presented as `κ²`.

## Koide domain / numeric audit

- **`wct-sympy` audit check:** the Koide expression
  `K(mₑ, m_μ, m_τ) = (mₑ + m_μ + m_τ) / (√mₑ + √m_μ + √m_τ)²` is evaluated
  numerically and compared to `2/3`.
- **Lean theorems:**
  - `koide_denominator_positive` (`WCTLean/Koide.lean`)
  - `koide_well_defined` (`WCTLean/Koide.lean`)
  - `koide_positive` (`WCTLean/Koide.lean`)
  - Supporting: `koide_sqrt_sum_pos`, `koide_numerator_positive`.
- **Meaning:** the Koide expression is domain-safe for positive lepton
  masses — the denominator is strictly positive (so division is justified),
  and the whole expression is positive.
- **Note:** Lean does **not** prove the numerical Koide equality
  `K = 2/3`. That comparison is left to the symbolic / numeric audit.

## Energy positivity skeleton

- **`wct-sympy` audit check:** quadratic-energy structural sanity — a
  quadratic form with nonnegative coefficients should be nonnegative.
- **Lean theorem:** `positive_quadratic_energy_nonnegative`
  (`WCTLean/Energy.lean`).
- **Meaning:** positive coefficients give nonnegative quadratic energy,
  `0 ≤ a, 0 ≤ b ⇒ 0 ≤ a · x² + b · y²`. Supporting positivity blocks
  (`square_nonnegative`, `norm_sq_nonnegative`,
  `positive_coeff_square_nonnegative`, `sum_two_nonnegative`) live in the
  same file.
