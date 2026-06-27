# SYMPY_MAP

This file maps executable `wct-sympy` checks to corresponding `WCTLean` declarations.

A SymPy `PASS` is not automatically a Lean proof. The relationship column distinguishes exact algebraic counterparts from conditional cores and adjacent support lemmas.

| SymPy ID | Lean declaration | relationship | meaning |
|---|---|---|---|
| `E5` | `effectiveWavenumber_eq_loopAverage` | conditional exact counterpart | exact closure implies winding wavenumber equals integrated curvature divided by loop length |
| `E5` | `constantWeightedAverage_eq_loopAverage` | conditional exact counterpart | constant nonzero weight cancels from the weighted average |
| `E5` | `resolved_e5_effectiveWavenumber_chain` | conditional exact counterpart | combines closure and positive constant weight into the full algebraic chain |
| `E9` | `polarCurrentProduct_im` | algebraic core | imaginary part of the polar current product is `u*dtheta` |
| `E9` | `phaseCurrent_of_polar_factorization` | conditional counterpart | assumes the polar derivative factorization, then proves the phase-current identity |
| `E9` | `conservationResidual_zero_iff` | adjacent theorem | proves the local continuity residual equivalence |
| `E13` | `bandpass_oneMode_symbol` | spectral algebra core | one Fourier mode gives the growth symbol `r + a k² - b k⁴` |
| `E14` | `bandpass_oneMode_symbol` | adjacent theorem | supports the operator-symbol correspondence but does not prove the functional derivative |
| `E18` | `resolved_e18_energy_nonnegative` | conditional exact counterpart | nonnegative coefficients and terms imply nonnegative encoded energy |
| `E18` | `resolved_e18_gradientFlow_descent` | conditional core | assumes the chain-rule rate identity and proves nonpositive descent |
| `E58` | `bandGreenDenominator_pos` | exact counterpart | positive offset prevents a denominator zero |
| `E58` | `bandGreenDenominator_ge_offset` | exact counterpart | denominator is bounded below by `r` |
| `E58` | `bandGreenKernel_pos` | exact counterpart | Green kernel is positive |
| `E58` | `bandGreenKernel_le_inverseOffset` | exact counterpart | Green kernel is at most `1/r` |
| `E58` | `bandGreenKernel_at_shell` | exact counterpart | the upper bound is attained at the selected shell |
| `CM9` | `photonSecondOrder_iff_firstOrder` | exact algebraic counterpart | photon second-order and first-order acceleration forms are equivalent |
| `CM9` | `baryonSecondOrder_iff_firstOrder` | exact algebraic counterpart | baryon second-order and first-order acceleration forms are equivalent |
| `CM11` | none | TODO | full time-dependent Gaussian damping requires a formal ODE solution theorem |
| `CM12` | `dimensionlessPowerSpectrum` | definition | dimensionless power-spectrum observable |
| `CM13` | `peakPowerRatio21`, `peakPowerRatio31`, `peakScaleRatio21`, `peakScaleRatio31` | definitions | peak-height and peak-scale ratios |
| `CM16` | `horizonWavenumber` | partial definition | defines `2π/R_hor`; the horizon-radius integral is not yet encoded |
| `CM18` | none | TODO definition | closure-set enumeration has not yet been encoded as a Lean finite set |

## Existing structural mappings

| Symbolic family | Lean declaration | relationship |
|---|---|---|
| `m = (ℏ/c) k_eff` | `hbar_div_c_mul_k_is_mass` | dimensional support only |
| `sigma = sqrt(kappa² + tau²)` | `sqrt_inverse_length_squared`, `sqrt_kappa_sq_dim` | dimensional support only |
| Koide expression | `koide_denominator_positive`, `koide_well_defined`, `koide_positive` | domain safety only; does not prove `K=2/3` |
| finite locking mismatch | `lockingMismatch_nonnegative`, `lockingMismatch_zero` | finite algebraic support |
| historical E17 denominator | `resolved_e17_counterexample`, `regularizedDenominator_positive` | counterexample plus restricted-domain repair |

## Formalization boundary

The following SymPy results remain outside exact Lean coverage:

- generalized Euler-Lagrange calculus for E13/E14;
- the complete complex curvature operator;
- functional-analytic Lyapunov descent for E18;
- time-dependent CM11 ODE integration;
- continuum loop integrals and Sobolev/PDE results;
- empirical or numerical validation.
