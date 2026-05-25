# THEOREMS

This file enumerates every current `WCTLean` theorem and definition with its
file, meaning, intended WCT role, and proof status.

The scope here is narrow: dimensional algebra, positivity skeletons, Koide
domain safety, and Fourier scaffolding. Nothing here proves WCT.

## Dimension (`WCTLean/Dimension.lean`)

| theorem / definition | file | meaning | WCT role | status |
| --- | --- | --- | --- | --- |
| `hbar_div_c_mul_k_is_mass` | `WCTLean/Dimension.lean` | `[ℏ/c · k] = M` at the integer-exponent (M, L, T) level | Dimensional closure of the headline mass identity | proven (`decide`) |
| `weightedSum_dim` | `WCTLean/Dimension.lean` | The constructor `weightedSum d xs ws` produces a `Tagged` whose `dim` field is exactly `d` | A weighted average operator preserves a declared dimension tag by construction | proven (`rfl`) |
| `weighted_average_preserves_dimension` | `WCTLean/Dimension.lean` | A weighted sum asserted at `inverseLengthDim` carries `inverseLengthDim` | Curvature-like weighted averages stay at `L⁻¹` | proven (`rfl`) |

## Curvature (`WCTLean/Curvature.lean`)

| theorem / definition | file | meaning | WCT role | status |
| --- | --- | --- | --- | --- |
| `kappa_sq_dim` | `WCTLean/Curvature.lean` | `[κ²] = L⁻²` | Curvature squared is inverse-area | proven (`decide`) |
| `tau_sq_dim` | `WCTLean/Curvature.lean` | `[τ²] = L⁻²` | Torsion squared is inverse-area | proven (`decide`) |
| `sqrt_inverse_length_squared` | `WCTLean/Curvature.lean` | `sqrtDim(L⁻²) = some L⁻¹` | Dimensional square-root sends `L⁻²` to `L⁻¹` | proven (`decide`) |
| `sqrt_kappa_sq_dim` | `WCTLean/Curvature.lean` | `sqrtDim(κ²) = some L⁻¹` | Curvature magnitude has inverse-length dimension | proven (`decide`) |

## Energy (`WCTLean/Energy.lean`)

| theorem / definition | file | meaning | WCT role | status |
| --- | --- | --- | --- | --- |
| `square_nonnegative` | `WCTLean/Energy.lean` | `0 ≤ x²` for any real `x` | Building block for positivity of quadratic terms | proven (`sq_nonneg`) |
| `norm_sq_nonnegative` | `WCTLean/Energy.lean` | `0 ≤ x · x` | Norm-square form of the positivity block | proven (`mul_self_nonneg`) |
| `positive_coeff_square_nonnegative` | `WCTLean/Energy.lean` | `0 ≤ a ⇒ 0 ≤ a · x²` | Positive-coefficient square is nonnegative | proven |
| `sum_two_nonnegative` | `WCTLean/Energy.lean` | `0 ≤ x, 0 ≤ y ⇒ 0 ≤ x + y` | Closure of nonnegativity under sum | proven (`add_nonneg`) |
| `positive_quadratic_energy_nonnegative` | `WCTLean/Energy.lean` | `0 ≤ a, 0 ≤ b ⇒ 0 ≤ a·x² + b·y²` | Toy WCT energy skeleton is nonnegative for positive coefficients | proven |

## Koide (`WCTLean/Koide.lean`)

| theorem / definition | file | meaning | WCT role | status |
| --- | --- | --- | --- | --- |
| `koide_sqrt_sum_pos` | `WCTLean/Koide.lean` | `0 < √mₑ + √m_μ + √m_τ` when all masses are positive | Domain safety: the square-root sum is strictly positive | proven |
| `koide_denominator_positive` | `WCTLean/Koide.lean` | `0 < (√mₑ + √m_μ + √m_τ)²` for positive masses | Domain safety: the Koide denominator is strictly positive | proven |
| `koide_numerator_positive` | `WCTLean/Koide.lean` | `0 < mₑ + m_μ + m_τ` for positive masses | Domain safety: the Koide numerator is strictly positive | proven |
| `koide_well_defined` | `WCTLean/Koide.lean` | The Koide denominator is nonzero for positive masses | Justifies use of division in `koide` | proven |
| `koide_positive` | `WCTLean/Koide.lean` | `0 < koide mₑ m_μ m_τ` for positive masses | Koide expression is positive on its physical domain. Does **not** prove the numerical `K = 2/3` value | proven |

## Fourier (`WCTLean/Fourier.lean`)

| theorem / definition | file | meaning | WCT role | status |
| --- | --- | --- | --- | --- |
| `two_cos_mul_cos` | `WCTLean/Fourier.lean` | `2 · cos a · cos b = cos(a - b) + cos(a + b)` | Pointwise product-to-sum identity used in orthogonality proofs | proven |
| `cos_orthogonality_TODO` | `WCTLean/Fourier.lean` | The proposition `∀ n m : ℤ, n ≠ m → ∫ x in 0..2π, cos(n x) · cos(m x) = 0` | Records the orthogonality statement as a `Prop` placeholder | **stated proposition / TODO, not proven** |

## Main (`WCTLean/Main.lean`)

| theorem / definition | file | meaning | WCT role | status |
| --- | --- | --- | --- | --- |
| `wctlean_smoke` | `WCTLean/Main.lean` | Restates `hbar_div_c_mul_k_is_mass` as a single library entry point | Build-time smoke test that the headline dimensional identity is reachable from the library root | proven (delegates to `hbar_div_c_mul_k_is_mass`) |

## Outstanding TODOs

- `cos_orthogonality_TODO` — stated as a `Prop`; proof requires Mathlib's
  `intervalIntegral` and `Real.cos` integration machinery and has not been
  attempted yet.
