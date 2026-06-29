# SYMPY_MAP

This file maps canonical WCT IDs and executable `wct-sympy` checks to maintained `WCTLean` declarations.

A SymPy `PASS` is not automatically a Lean proof. The relationship column distinguishes exact algebraic counterparts, dimensional support, finite analogues, definitions, analytic contracts, counterexamples, and unresolved propositions.

## Non-shallow canonical mapping batch

| Canonical ID | Lean declarations | Relationship | Formal boundary |
|---|---|---|---|
| `M4` | `h2SubcriticalDimension`, `h2Subcritical_iff_le_three`, `SobolevCurvatureContract` | arithmetic theorem plus analytic contract | proves `n < 4 ↔ n ≤ 3`; does not prove the Sobolev embedding itself |
| `M5` | `averagedUpdate_norm_le`, `InNormBound`, `averagedUpdate_preserves_normBound`, `BandLimitedInvariantSet` | finite bounded-dynamics support | proves norm-bound invariance under displayed nonexpansiveness assumptions; not a complexity theorem |
| `M6B` | `thetaComplex`, `thetaComplex_canonical_formula`, `thetaComplex_denominator_ne_zero` | exact typed operator form plus denominator safety | does not prove uniqueness of the nonlinear closure or PDE well-posedness |
| `E10` | `RadialShellQuantized`, `radialShellQuantized_add` | exact quantization predicate plus additive closure | no dynamical shell-selection theorem |
| `E11` | `WindingQuantized`, `windingQuantized_add` | exact quantization predicate plus additive closure | no topological existence theorem for field defects |
| `E29` | `entropyPrunedUpperBound`, `entropyPrunedUpperBound_nonnegative`, `entropyPrunedUpperBound_le_modeCount`, `entropyPrunedUpperBound_antitone` | exact scalar bound and monotonicity | does not derive the entropy drop from a PDE |
| `E36` | `averagedUpdate`, `averagedUpdate_fixed_of_average_fixed`, `averagedUpdate_norm_le` | concrete finite-dimensional update model | narrower than the full neighborhood-dependent WCC update |
| `G1` | `ghostMode`, `abs_ghostMode_le` | exact modulation definition plus global amplitude bound | no data fit or physical origin theorem |
| `EX` | `logField`, `exp_logField_eq` | logarithmic representation with positive-domain inverse theorem | restricted to positive real field values |
| `EY` | `logCurvatureResidual`, `coleHopf_residual_factorization`, `diffusionResidual_zero_iff_logCurvatureResidual_zero` | exact residual bridge under chain-rule hypotheses | function-space differentiability remains external |
| `EZ` | `diffusionResidual`, `coleHopf_residual_factorization`, `diffusionResidual_zero_iff_logCurvatureResidual_zero` | exact Cole–Hopf residual equivalence | does not prove existence or regularity of PDE solutions |
| `FA` | `FilamentLocalizationCondition`, `filamentLocalizationMismatch`, `filamentLocalizationCondition_iff_mismatch_zero` | exact scalar equivalence | no filament-existence or localization theorem |

`radialShellQuantized_iff_windingQuantized` also proves that E10 and E11 instantiate the same integer quantization law once the geometric observable is fixed.

## Derived audit mappings

| Canonical ID | Lean declaration | Relationship | Meaning |
|---|---|---|---|
| `E5` | `effectiveWavenumber_eq_loopAverage` | conditional exact counterpart | exact closure identifies winding wavenumber with integrated curvature divided by loop length |
| `E5` | `constantWeightedAverage_eq_loopAverage` | conditional exact counterpart | constant nonzero weight cancels from the weighted average |
| `E5` | `resolved_e5_effectiveWavenumber_chain` | conditional exact counterpart | combines closure and positive constant weight into the algebraic chain |
| `E9` | `polarCurrentProduct_im` | algebraic core | imaginary part of the polar current product is `u*dtheta` |
| `E9` | `phaseCurrent_of_polar_factorization` | conditional counterpart | assumes polar derivative factorization, then proves the phase-current identity |
| `E9` | `conservationResidual_zero_iff` | adjacent theorem | proves the local continuity residual equivalence |
| `E13` | `bandpass_oneMode_symbol` | spectral algebra core | one Fourier mode gives `r + a k² - b k⁴` |
| `E14` | `bandpass_oneMode_symbol` | adjacent theorem | supports the operator-symbol correspondence but not the full functional derivative |
| `E18` | `resolved_e18_energy_nonnegative` | conditional exact counterpart | nonnegative coefficients and terms imply nonnegative encoded energy |
| `E18` | `resolved_e18_gradientFlow_descent` | conditional core | assumes the chain-rule rate identity and proves nonpositive descent |
| `E58` | `bandGreenDenominator_pos` | exact counterpart | positive offset prevents a denominator zero |
| `E58` | `bandGreenDenominator_ge_offset` | exact counterpart | denominator is bounded below by `r` |
| `E58` | `bandGreenKernel_pos` | exact counterpart | Green kernel is positive |
| `E58` | `bandGreenKernel_le_inverseOffset` | exact counterpart | Green kernel is at most `1/r` |
| `E58` | `bandGreenKernel_at_shell` | exact counterpart | the upper bound is attained at the selected shell |
| `CM9` | `photonSecondOrder_iff_firstOrder` | exact algebraic counterpart | photon second-order and first-order acceleration forms are equivalent |
| `CM9` | `baryonSecondOrder_iff_firstOrder` | exact algebraic counterpart | baryon second-order and first-order acceleration forms are equivalent |
| `CM12` | `dimensionlessPowerSpectrum` | definition | dimensionless power-spectrum observable |
| `CM13` | `peakPowerRatio21`, `peakPowerRatio31`, `peakScaleRatio21`, `peakScaleRatio31` | definitions | peak-height and peak-scale ratios |
| `CM16` | `horizonWavenumber` | partial definition | defines `2π/R_hor`; the horizon-radius integral is not encoded |

## Structural mappings

| Canonical object | Lean declarations | Relationship |
|---|---|---|
| `M1`, `E3` | `finiteLockingAction`, `finiteLockingAction_nonnegative`, `finiteLockingAction_zero` | finite algebraic analogue |
| `E4`, `E8` | `alphaLock_closure`, `pointwiseLocked_weighted`, `correctedWeightedLockIdentity` | conditional finite counterpart |
| `M2`, `E17` | `complexRegularizerDenominator_positive`, `complexRegularizerDenominator_ne_zero`, `thetaComplex_zero_state` | corrected complex denominator and local operator support |
| `M3`, `M7`, `E12`, `E57`, `E61`, `E64` | finite-band declarations in `Models/BandPass.lean` | exact scalar Fourier-symbol support |
| `E1A`, `E1B` | `kappa_sq_dim`, `tau_sq_dim`, `sqrt_inverse_length_squared`, `sqrt_kappa_sq_dim` | dimensional support only |
| `E6`, `E7` | `hbar_div_c_mul_k_is_mass`, `weighted_average_preserves_dimension` | dimensional support only |
| `E20` | `cavityQuadratic_nonnegative` | conditional positive-semidefinite scalar sector |
| `E24`–`E27`, `E65`–`E70` | declarations in `Contracts/Analytic.lean` | arithmetic theorem, definitions, and explicit analytic contracts |
| `E28` | `alphaDrop_lt_one` | exact scalar implication under encoded hypothesis |
| `E33` | `exp_entropy_le_support` | exact order-theoretic consequence |
| `E45` | `effectiveQualityFactor_positive` | exact positivity theorem |
| `E47` | `stationaryPowerBalance_iff` | exact scalar equivalence |
| `E49` | `effectiveMassSqFromGap_eq` | definitional identity |
| `E51` | `curvatureGradientCommutator_eq` | quotient-rule scalar identity |
| `E53` | `curvaturePressureDensity_nonnegative` | exact nonnegativity theorem |
| `E59` | `maskProjection_idempotent` | finite coordinate-mask projection theorem |
| `E62` | `spectralEnergyFraction_mem_unitInterval` | exact unit-interval theorem |
| `E78` | `cos_orthogonality_TODO` | unresolved proposition only |
| `E81` | `spectralCoherenceLength`, `gradientCoherenceLength` | definitions |

## Explicit unmapped examples

The following remain outside substantive equation-specific Lean closure:

- complete generalized Euler–Lagrange calculus for the full action;
- function-space polar differentiation;
- PDE existence, uniqueness, regularity, decay, and stability;
- continuum loop integrals and manifold locking;
- `ε → 0` operator control;
- full cosmological dynamics and calibrated data fitting;
- theorem-level particle-mass, force, gauge, gravity, and experimental bridges.

The complete count and object list are maintained in [`FORMAL_COVERAGE_INDEX.md`](FORMAL_COVERAGE_INDEX.md).
