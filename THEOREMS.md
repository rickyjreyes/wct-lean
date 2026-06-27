# THEOREMS

This file inventories the maintained `WCTLean` declarations and distinguishes kernel proofs from assumptions, definitions, and unresolved analytical work.

Nothing here proves WCT as a physical theory.

## Derived audit batch 1 (`WCTLean/DerivedAudit.lean`)

| declaration | equation | kernel-checked content | boundary |
|---|---|---|---|
| `effectiveWavenumber_eq_loopAverage` | E5 | exact loop closure identifies winding wavenumber with integrated curvature divided by loop length | assumes the closure equality |
| `constantWeightedAverage_eq_loopAverage` | E5 | a nonzero constant weight cancels from the weighted average | finite algebraic reduction, not an integral theorem |
| `resolved_e5_effectiveWavenumber_chain` | E5 | combines exact closure and positive constant weight into the complete algebraic chain | does not prove a field dynamically reaches exact lock |
| `polarCurrentProduct_im` | E9 | the imaginary part of `du/2 + i u dtheta` is `u dtheta` | pointwise algebraic identity |
| `phaseCurrent_of_polar_factorization` | E9 | a supplied polar factorization implies the phase-current formula | the derivative factorization is an explicit hypothesis |
| `bandpass_oneMode_symbol` | E13/E14 | the one-mode real-space operator reduces to `r + a k² - b k⁴` | not the full variational derivative theorem |
| `resolved_e18_energy_nonnegative` | E18 | nonnegative coefficients and nonnegative energy terms imply nonnegative total energy | finite algebraic positivity |
| `resolved_e18_gradientFlow_descent` | E18 | if the energy rate equals minus a nonnegative squared norm, the rate is nonpositive | chain-rule identity is an explicit hypothesis |
| `bandGreenDenominator_pos` | E58 | positive offset and nonnegative shell coefficient give a positive denominator | exact real-algebra theorem |
| `bandGreenDenominator_ge_offset` | E58 | the denominator is at least the positive offset | exact real-algebra theorem |
| `bandGreenKernel_pos` | E58 | the kernel is positive | exact real-algebra theorem |
| `bandGreenKernel_le_inverseOffset` | E58 | `G(k) ≤ 1/r` for `r>0`, `a≥0` | exact real-order theorem |
| `bandGreenKernel_at_shell` | E58 | `G(k*) = 1/r` | exact shell substitution theorem |
| `photonSecondOrder_iff_firstOrder` | CM9 | photon second-order and first-order acceleration forms are equivalent | coefficient convention is fixed by the definitions |
| `baryonSecondOrder_iff_firstOrder` | CM9 | baryon second-order and first-order acceleration forms are equivalent | coefficient convention is fixed by the definitions |
| `dimensionlessPowerSpectrum` | CM12 | introduces the dimensionless power-spectrum observable | definition |
| `peakPowerRatio21`, `peakPowerRatio31` | CM13 | introduce peak-power ratios | definitions |
| `peakScaleRatio21`, `peakScaleRatio31` | CM13 | introduce peak-scale ratios | definitions |
| `horizonWavenumber` | CM16 | introduces `2π/R_hor` from a supplied radius | definition; the horizon integral is not formalized here |

## Resolved equation audit (`WCTLean/ResolvedAudit.lean`)

| declaration | equation | content | status |
|---|---|---|---|
| `resolved_e17_counterexample` | E17 | historical scalar denominator vanishes at `(-1,1,0)` | counterexample proved |
| `conservationResidual_zero_iff` | E9 | zero residual iff time derivative equals minus flux divergence | proved algebraic equivalence |
| `densityWeightedAverage_denominator_ne_zero` | E2 | positive total density implies nonzero denominator | proved |
| `lockingMismatch_nonnegative` | E3 | nonnegative weights make the finite mismatch nonnegative | proved |
| `lockingMismatch_zero` | E3 | exact finite locking makes mismatch zero | proved |

## Dimension (`WCTLean/Dimension.lean`)

| declaration | content | status |
|---|---|---|
| `hbar_div_c_mul_k_is_mass` | `[ℏ/c · k] = M` at integer-exponent dimension level | proved |
| `weightedSum_dim` | declared dimension tag is preserved by construction | proved |
| `weighted_average_preserves_dimension` | curvature-like weighted average carries inverse-length dimension | proved |

## Curvature (`WCTLean/Curvature.lean`)

| declaration | content | status |
|---|---|---|
| `kappa_sq_dim` | `[κ²] = L⁻²` | proved |
| `tau_sq_dim` | `[τ²] = L⁻²` | proved |
| `sqrt_inverse_length_squared` | square root of `L⁻²` is `L⁻¹` in the encoded dimension algebra | proved |
| `sqrt_kappa_sq_dim` | curvature magnitude has inverse-length dimension | proved |

## Energy (`WCTLean/Energy.lean`)

| declaration | content | status |
|---|---|---|
| `square_nonnegative` | `0 ≤ x²` | proved |
| `norm_sq_nonnegative` | `0 ≤ x*x` | proved |
| `positive_coeff_square_nonnegative` | nonnegative coefficient times square is nonnegative | proved |
| `sum_two_nonnegative` | sum of nonnegative terms is nonnegative | proved |
| `positive_quadratic_energy_nonnegative` | two-term quadratic energy is nonnegative | proved |

## Koide (`WCTLean/Koide.lean`)

| declaration | content | status |
|---|---|---|
| `koide_sqrt_sum_pos` | square-root mass sum is positive for positive masses | proved |
| `koide_denominator_positive` | Koide denominator is positive | proved |
| `koide_numerator_positive` | Koide numerator is positive | proved |
| `koide_well_defined` | Koide denominator is nonzero | proved |
| `koide_positive` | Koide expression is positive on the positive-mass domain | proved; does not establish `K=2/3` |

## Fourier (`WCTLean/Fourier.lean`)

| declaration | content | status |
|---|---|---|
| `two_cos_mul_cos` | pointwise product-to-sum identity | proved |
| `cos_orthogonality_TODO` | distinct-mode cosine orthogonality proposition | TODO, not proved |

## Main (`WCTLean/Main.lean`)

| declaration | content | status |
|---|---|---|
| `wctlean_smoke` | root-level access to the dimensional mass identity | proved |

## Remaining analytical boundary

The following are not closed by this theorem batch:

- full polar differentiation for `psi = sqrt(u) exp(i theta)` in a function space;
- generalized Euler-Lagrange derivation of E13/E14;
- functional chain rule for the complete E18 curvature energy;
- time-dependent diffusivity ODE proof for CM11;
- integral locking on curves and manifolds;
- PDE existence, uniqueness, regularity, coercivity, and stability;
- empirical calibration or experimental validation.
