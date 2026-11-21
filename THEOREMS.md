# WCT Lean Theorem Inventory

This file lists maintained `WCTLean` declarations and separates kernel proofs from definitions, contracts, counterexamples, and unresolved work.

Nothing in this inventory proves WCT as a complete physical theory.

## Canonical registry (`WCTLean/Registry.lean`)

| Declaration | Kernel-checked content |
|---|---|
| `masterIds_length` | master-system family has 9 IDs |
| `canonicalIds_length` | canonical E-family has 83 IDs |
| `electronIds_length` | CLE family has 10 IDs |
| `auxiliaryIds_length` | auxiliary family has 5 IDs |
| `cosmologyIds_length` | CM family has 20 IDs |
| `topologyIds_length` | TOP family has 9 IDs |
| `correctionIds_length` | CORR family has 6 IDs |
| `allEquationIds_length` | complete registry has 142 IDs |
| `allEquationIds_nodup` | registry IDs are unique |
| `passIds_length` | effective `PASS` partition has 59 IDs |
| `conditionalIds_length` | effective `CONDITIONAL` partition has 27 IDs |
| `definitionIds_length` | effective `DEFINITION` partition has 26 IDs |
| `openIds_length` | effective `OPEN` partition has 30 IDs |
| `statusPartition_length` | status partition has 142 entries |
| `statusPartition_nodup` | no ID appears twice in the status partition |
| `statusPartition_complete` | status and canonical ID sets are equal |
| `every_registered_id_has_status` | every registered ID resolves to a status |
| `every_registered_id_has_family` | every registered ID resolves to a family |
| `canonicalRegistry_length` | compiled entry registry has 142 records |

These theorems prove registry integrity, not the mathematical content of all 142 equations.

## Registry-only closure batch (PR #36)

[Scoped evidence and analytical proofs](docs/REGISTRY_ONLY_CLOSURES_2026-10-30.md). These declarations are Lean theorems over stated scalar or finite-dimensional hypotheses, not physical laws.

| Declaration | Equation | Exact encoded result |
|---|---|---|
| `top6_statistic_scales_inverse_square` | TOP6 | unnormalized curvature statistic scales as inverse dilation squared when length and integrated curvature transform as stated |
| `top6_dilation_changes_statistic` | TOP6 | positive statistic strictly changes under a factor-two dilation |
| `cm3_potential_poisson_relation` | CM3 | Fourier-potential algebra for nonzero wavenumber |
| `cm4_decay_iff_nonpositive_logarithmic_rate` | CM4 | constant-coefficient real decay law iff logarithmic growth rate is nonpositive |
| `cm10_drag_contracts_difference` | CM10 | convex drag reduces or preserves mismatch |
| `cm15_cm20_compatible_iff_energy_loss` | CM15/CM20 | proposed expansion equation iff exact scalar energy-loss identity |
| `e44_local_curvature_global_phase_invariance` | E44 | unit phase cancels in the corrected local curvature expression with shared invariant denominator |
| `e44_phase_rotated_eigenvalue_obstruction` | E44 | a nontrivial phase rotation and the same nonlinear eigenvalue force vanishing eigenvalue-times-field |
| `e60_real_squared_amplitude_derivative` | E60 | exact squared-amplitude derivative under a scalar cubic ODE |
| `e60_real_stationary_iff` | E60 | scalar stationary states obey `A=0` or `mu=g A²` |
| `e82_information_gram_symmetric` | E82 | finite real Gram tensor symmetry |
| `e82_information_gram_diagonal_nonnegative` | E82 | diagonal nonnegativity |
| `e82_information_gram_quadratic_nonnegative` | E82 | sum-of-squares quadratic representation is nonnegative |

Existing adjacent module `WCTLean/Models/NarrowCanonicalCoverage.lean`:

| Declaration | Equation | Scope |
|---|---|---|
| `e15_scalar_modal_power_derivative`, `e15_scalar_modal_growth_bound` | E15 | real scalar cubic-saturation reduction, not arbitrary nonlinear PDE Fourier modes |
| `cle6_separated_mode_quotient` | CLE6 | algebraic separation identity at nonzero modal values |
| `cle7_angular_mode_periodic` | CLE7 | period of displayed angular modes; full ODE solution completeness is an independent obligation |

The independent [math compendium](https://github.com/rickyjreyes/math/blob/main/compendium/wct-elementary-mathematics/main.tex) already contains analytic proofs for E21, E30, CLE6, and CLE7. This inventory does not count those as Lean proofs in this repository.

## Corrected complex curvature (`WCTLean/Models/ComplexCurvature.lean`)

| Declaration | Equation | Content |
|---|---|---|
| `complex_normSq_nonnegative` | M2/E17 | complex modulus-square is nonnegative |
| `complexRegularizerDenominator_positive` | M2/E17/M6B | corrected denominator is positive for every complex field value when `ε > 0` |
| `complexRegularizerDenominator_ne_zero` | M2/E17 | corrected real denominator never vanishes under `ε > 0` |
| `thetaComplex_canonical_formula` | M6B | typed operator equals the canonical modulus-squared quotient |
| `thetaComplex_denominator_ne_zero` | M6B | cast complex denominator is nonzero for `ε > 0` |
| `complexRegularizerDenominator_at_zero` | M2/E17 | node denominator equals `ε²` |
| `complexRegularizedReciprocal_at_zero` | M2/E17 | regularized reciprocal is defined and zero at a node |
| `thetaComplex_zero_state` | M2/E17/M6B | supplied zero field/Laplacian state gives zero local curvature product |

The M6B results establish exact local operator form and denominator safety. They do not prove PDE well-posedness.

### M6B closure classification (issue #26)

`WCTLean/Models/ClosureClassification.lean`; 17 roots audited fail-closed
(`scripts/closure_classification_axiom_audit.lean`), only standard axioms.
Operator selection for pointwise jet maps `(ψ, Δψ) ↦ Θ`, not PDE-solution
uniqueness.

| Declaration | Content |
|---|---|
| `closure_classification` | `ℂ`-homogeneous in `Δψ` + global phase invariant ⇒ `Θ = -(Δψ ψ̄) g(|ψ|²)` |
| `radialClosure_homogeneous`, `radialClosure_phaseInvariant`, `denominatorClosure_structural` | converse: every radial reweighting is in the structural class |
| `denominatorClosure_maintained` | maintained `thetaComplex` = radial closure of `s + ε²e^{-2αs}` |
| `denominatorClosure_unit_invariant` | unit covariance of `D` ⇒ closure invariant under `(ψ, Δψ, ε) ↦ (λψ, λΔψ, λε)` |
| `admissible_profile`, `admissible_profile_asymptotic`, `profileRegularizer_admissible` | admissible regularizers are exactly `D_ε(s) = ε²Φ(s/ε²)`, `Φ > 0`, `Φ(u)/u → 1` |
| `shift_profile_admissible`, `admissible_closures_infinite` | infinitely many pairwise distinct admissible closures at fixed `ε` |
| `maintainedDenominator_not_unitCovariant` | fixed `α ≠ 0` violates unit covariance |
| `maintained_scaled_eq_profile`, `maintained_scaled_profile_admissible` | `α = a/ε²` gives the admissible profile `u + e^{-2au}` |
| `closure_unique_affine_normalized` | admissible + affine profile + `D_ε(0) = ε²` ⇒ closure = `thetaComplex · · ε 0` |
| `selected_regularizer_satisfies_principles` | the uniqueness hypotheses are satisfiable (non-vacuity) |
| `extra_principles_independent` | `u + 2` (affine, not normalized) and `u + e^{-u}` (normalized, not affine) are admissible and different |

## Curvature-phase locking (`WCTLean/Models/Locking.lean`)

| Declaration | Equation | Content | Boundary |
|---|---|---|---|
| `alphaLock_closure` | E4 | stated integration constant solves scalar winding closure | denominator assumed nonzero |
| `pointwiseLocked_weighted` | E4/E8 | multiplying pointwise lock by nonzero weight gives local weighted identity | finite scalar theorem |
| `correctedWeightedLockIdentity` | E8 | finite weighted phase-gradient sum equals curvature sum plus constant term | finite counting measure |
| `finiteLockingAction_nonnegative` | M1/E3 | finite mismatch action is nonnegative | nonnegative weights |
| `finiteLockingAction_zero` | M1/E3 | exact finite lock makes mismatch action zero | finite model |

## Phase flux and quantization (`WCTLean/Models/PhaseFlux.lean`)

| Declaration | Equation | Content |
|---|---|---|
| `RadialShellQuantized` | E10 | exact radial shell quantization predicate |
| `WindingQuantized` | E11 | exact winding quantization predicate |
| `radialShellQuantized_add` | E10 | shell-quantized phase integrals are closed under addition |
| `windingQuantized_add` | E11 | quantized circulations are closed under addition |
| `radialShellQuantized_iff_windingQuantized` | E10/E11 | both predicates implement the same integer law for a supplied observable |

These are exact algebraic closure theorems, not dynamical selection or defect-existence results.

## Finite-band selector (`WCTLean/Models/BandPass.lean`)

| Declaration | Equation | Content |
|---|---|---|
| `finiteBandPenalty_nonpositive` | M3/M7 | fourth-order shell contribution is nonpositive for `b ≥ 0` |
| `finiteBandPenalty_at_shell` | M3/M7/E57 | shell contribution vanishes at `k = k*` |
| `finiteBandPenalty_strict_off_shell` | M3/M7 | positive coefficient gives strict off-shell damping |
| `swiftHohenbergLinearSymbol_le_mu` | E12 | growth symbol is bounded above by its on-shell value |
| `swiftHohenbergLinearSymbol_at_shell` | E12/E61 | selected shell attains `μ` |
| `selectedShell_positive_at_onset` | E61 | positive onset parameter gives positive on-shell growth |
| `quarticGrowthSymbol_completedSquare` | E12 | exact completed-square identity |
| `selectedWavelength_positive` | E64 | corrected selected wavelength is positive for `a,b > 0` |

## Canonical algebraic checks (`WCTLean/Models/AlgebraicChecks.lean`)

| Declaration | Equation | Content |
|---|---|---|
| `cavityQuadratic_nonnegative` | E20 | cavity quadratic sector is nonnegative under positive-semidefinite coefficient conditions |
| `alphaDrop_lt_one` | E28 | corrected beta condition implies alpha-drop below one |
| `entropyPrunedUpperBound_nonnegative` | E29 | encoded pruning bound is nonnegative for nonnegative mode count |
| `entropyPrunedUpperBound_le_modeCount` | E29 | nonnegative entropy drop cannot increase the bound |
| `entropyPrunedUpperBound_antitone` | E29 | bound is antitone in entropy drop |
| `exp_entropy_le_support` | E33 | `H ≤ log K` implies `exp H ≤ K` |
| `effectiveQualityFactor_positive` | E45 | corrected quality factor is positive for positive inputs |
| `stationaryPowerBalance_iff` | E47 | zero energy rate is equivalent to source/sink balance |
| `effectiveMassSqFromGap_eq` | E49 | corrected effective-mass-square identity unfolds exactly |
| `curvatureGradientCommutator_eq` | E51 | quotient-rule commutator equals denominator-gradient term |
| `curvaturePressureDensity_nonnegative` | E53 | local curvature pressure is nonnegative under nonnegative inputs |
| `maskProjection_idempotent` | E59 | a fixed coordinate mask is an idempotent projection |
| `spectralEnergyFraction_mem_unitInterval` | E62 | annular spectral-energy fraction lies in `[0,1]` |

## Compact bounded dynamics (`WCTLean/Models/CompactDynamics.lean`)

| Declaration | Equation | Content | Boundary |
|---|---|---|---|
| `averagedUpdate` | E36 | finite-dimensional convex update definition | special case of general WCC update |
| `averagedUpdate_fixed_of_average_fixed` | E36 | fixed points of the averaging map remain fixed | exact algebraic theorem |
| `averagedUpdate_norm_le` | M5/E36 | update does not increase norm under convex mixing and local nonexpansiveness | pointwise finite-dimensional theorem |
| `InNormBound` | M5 | explicit bounded-resource predicate | definition |
| `averagedUpdate_preserves_normBound` | M5 | bounded norm ball is forward invariant | assumes local nonexpansiveness |
| `BandLimitedInvariantSet` | M5 | explicit invariant finite-band contract structure | contract, not existence proof |

These statements do not prove polynomial complexity or equivalence with classical complexity classes.

## Logarithmic flow and filament localization (`WCTLean/Models/LogFlow.lean`)

| Declaration | Equation | Content | Boundary |
|---|---|---|---|
| `logField` | EX | logarithmic field definition | real scalar model |
| `exp_logField_eq` | EX | exponentiation inverts `logField` for positive fields | positivity required |
| `logCurvatureResidual` | EY | nonlinear logarithmic residual | definition |
| `diffusionResidual` | EZ | linear diffusion residual | definition |
| `coleHopf_residual_factorization` | EY/EZ | diffusion residual equals field times logarithmic residual | temporal and Laplacian chain rules assumed |
| `diffusionResidual_zero_iff_logCurvatureResidual_zero` | EY/EZ | zero residuals are equivalent on a nonzero field sector | chain rules and nonzero field assumed |
| `filamentLocalizationMismatch` | FA | scalar localization mismatch | definition |
| `filamentLocalizationCondition_iff_mismatch_zero` | FA | localization condition iff mismatch vanishes | scalar equivalence |
| `exp_chain_rule_algebra` | EX/EY/EZ | commutative algebra used in exponential differentiation | algebra only |

## Ghost mode (`WCTLean/Models/GhostModes.lean`)

| Declaration | Equation | Content |
|---|---|---|
| `ghostMode` | G1 | log-periodic modulation definition |
| `abs_ghostMode_le` | G1 | modulation magnitude is bounded by absolute amplitude |
| `gaussianSmearingFactor` | related | smearing definition |
| `smearedGhostAmplitude` | related | smeared amplitude definition |
| `junoResolution` | related | detector-resolution definition |
| `deltaC9` | related | collider modulation definition |

No empirical fit or physical-origin claim is proved.

## Unified operator (`WCTLean/Models/UnifiedOperator.lean`)

| Declaration | Equation | Content |
|---|---|---|
| `unifiedShellTerm_nonpositive` | M6A/M7 | corrected negative fourth-order term is nonpositive |
| `unifiedShellTerm_zero_on_shell` | M6A/M7 | corrected shell term vanishes on shell |

`unifiedLinearSymbol` is a definition, not a proof of the full nonlinear UWCT equation.

## Analytic contracts (`WCTLean/Contracts/Analytic.lean`)

| Declaration | Equation | Status |
|---|---|---|
| `h2Subcritical_iff_le_three` | M4/E24/E67 | proved arithmetic equivalence `n < 4 ↔ n ≤ 3` |
| `SobolevCurvatureContract` | M4/E24/E26/E67/E69 | contract/interface, not proof of Sobolev embedding or curvature boundedness |
| `criticalSobolevExponent` | E25/E65 | definition |
| `FiniteConfinementEnergy` | E27 | definition |
| `GagliardoNirenbergBound` | E66 | proposition encoding the required inequality |
| `LocalEnergyBound` | E68 | proposition encoding the required localized estimate |
| `DimensionalStabilityCriterion` | E70 | definition separating hypotheses |
| `dimensional_stability_implies_le_three` | E70 | criterion implies its explicit `n ≤ 3` component |
| `biharmonic_scaling_dimension_four` | dimensional audit | at `n=4`, printed scaling factor is scale-invariant rather than divergent |

## Derived audit (`WCTLean/DerivedAudit.lean`)

| Declaration | Equation | Kernel-checked content | Boundary |
|---|---|---|---|
| `effectiveWavenumber_eq_loopAverage` | E5 | exact closure identifies winding wavenumber with integrated curvature divided by length | assumes closure equality |
| `constantWeightedAverage_eq_loopAverage` | E5 | constant nonzero weight cancels | finite algebraic reduction |
| `resolved_e5_effectiveWavenumber_chain` | E5 | combines closure and constant weight | does not prove dynamic locking |
| `polarCurrentProduct_im` | E9 | imaginary part of polar product is `u dθ` | pointwise identity |
| `phaseCurrent_of_polar_factorization` | E9 | supplied polar factorization gives phase current | derivative factorization is a hypothesis |
| `bandpass_oneMode_symbol` | E13/E14 | one-mode operator gives quartic symbol | not full variational derivative |
| `resolved_e18_energy_nonnegative` | E18 | finite energy sum is nonnegative | algebraic positivity |
| `resolved_e18_gradientFlow_descent` | E18 | supplied negative-square rate is nonpositive | full chain rule not proved |
| `bandGreenDenominator_pos` | E58 | Green denominator is positive | `r>0`, `a≥0` |
| `bandGreenDenominator_ge_offset` | E58 | denominator is at least offset | exact order theorem |
| `bandGreenKernel_pos` | E58 | Green kernel is positive | exact order theorem |
| `bandGreenKernel_le_inverseOffset` | E58 | `G(k) ≤ 1/r` | exact order theorem |
| `bandGreenKernel_at_shell` | E58 | `G(k*) = 1/r` | exact substitution |
| `photonSecondOrder_iff_firstOrder` | CM9 | photon first/second-order forms are equivalent | fixed definitions |
| `baryonSecondOrder_iff_firstOrder` | CM9 | baryon first/second-order forms are equivalent | fixed definitions |
| `dimensionlessPowerSpectrum` | CM12 | observable definition | definition |
| `peakPowerRatio21`, `peakPowerRatio31` | CM13 | ratio definitions | definitions |
| `peakScaleRatio21`, `peakScaleRatio31` | CM13 | scale-ratio definitions | definitions |
| `horizonWavenumber` | CM16 | `2π/R` definition | horizon dynamics not proved |

## Resolved audit (`WCTLean/ResolvedAudit.lean`)

| Declaration | Equation | Content |
|---|---|---|
| `resolved_e17_counterexample` | historical E17 | scalar denominator vanishes at `(-1,1,0)` |
| `conservationResidual_zero_iff` | E9 | zero residual iff time derivative equals minus divergence |
| `densityWeightedAverage_denominator_ne_zero` | E2 | positive total density implies nonzero denominator |
| `lockingMismatch_nonnegative` | E3 | finite mismatch is nonnegative |
| `lockingMismatch_zero` | E3 | exact finite locking makes mismatch zero |

## Dimension, curvature, energy, Koide, and Fourier foundations

Maintained foundational declarations include:

```lean
hbar_div_c_mul_k_is_mass
weighted_average_preserves_dimension
kappa_sq_dim
tau_sq_dim
sqrt_inverse_length_squared
sqrt_kappa_sq_dim
square_nonnegative
positive_quadratic_energy_nonnegative
koide_denominator_positive
koide_well_defined
koide_positive
two_cos_mul_cos
```

`cos_orthogonality_TODO` is retained only as the historical proposition; it is
**false** as stated (integer labels with only `n ≠ m`), and is refuted by
`cos_orthogonality_TODO_false` at `n = 1`, `m = -1`.

## Fourier orthogonality, spectral projection, and E78 (issue #23)

All declarations below are kernel-checked with only `propext`,
`Classical.choice`, and `Quot.sound` (audited fail-closed by
`scripts/fourier_e78_axiom_audit.lean` + `scripts/check_axiom_log.py`, 44 roots).

`WCTLean/Fourier.lean` — real trigonometric system on `[0, 2π]` (Lebesgue
interval integrals):

| Declaration | Content |
|---|---|
| `integral_cos_int_mul_period`, `integral_sin_int_mul_period` | `∫₀^{2π} cos(kx) = 0` (`k ≠ 0`), `∫₀^{2π} sin(kx) = 0` |
| `integral_cos_mul_cos_of_natAbs_ne`, `integral_cos_mul_cos_nat_of_ne` | cosine orthogonality for `|n| ≠ |m|` (integers) / `n ≠ m` (naturals) |
| `integral_sin_mul_sin_of_natAbs_ne`, `integral_sin_mul_sin_nat_of_ne` | sine orthogonality |
| `integral_sin_mul_cos_int` | sine/cosine orthogonality for all integer labels |
| `integral_cos_mul_cos_self`, `integral_sin_mul_sin_self`, `integral_cos_sq_int_mul`, `integral_sin_sq_int_mul` | normalization `= π` for `n ≠ 0` |
| `integral_cos_mul_cos_int` | full cosine Gram matrix: `0` if `|n| ≠ |m|`, `π` if `|n| = |m| ≠ 0`, `2π` if `n = m = 0` |
| `cos_orthogonality_TODO_false` | the historical integer TODO is false (`n = 1`, `m = -1` gives `π`) |
| `cos_orthogonality_corrected_holds` | corrected integer statement with `|n| ≠ |m|` |

`WCTLean/FourierSpectral.lean` — `L²(AddCircle T; ℂ)` with normalized Haar
measure and modes `e_n = fourierLp 2 n` (periodic model, `T > 0`):

| Declaration | Content |
|---|---|
| `spectralProjection_eq_starProjection` | `P_S f = ∑_{n∈S} f̂(n) e_n` is the orthogonal projection onto `span{e_n : n ∈ S}` |
| `spectralProjection_idem`, `spectralProjection_inner_symm`, `fourierCoeff_spectralProjection` | idempotent, self-adjoint, diagonal on coefficients |
| `norm_sq_spectralProjection`, `norm_sq_eq_spectralProjection_add_remainder`, `norm_sq_sub_spectralProjection`, `sum_norm_sq_fourierCoeff_le`, `norm_spectralProjection_le` | finite Parseval, Pythagoras, exact remainder, Bessel, contraction |
| `norm_sub_spectralProjection_le` | best approximation in the band |
| `tendsto_spectralProjection`, `tendsto_symmetric_spectralProjection`, `tendsto_norm_sub_symmetric_spectralProjection` | infinite resolution: `P_S f → f`; symmetric partial sums `P_{[-N,N]} f → f` in `L²` |
| `hasSum_norm_sq_fourierCoeff`, `tsum_tail_eq_norm_sq_sub_spectralProjection` | Parseval in norm form; tail energy equals projection error |
| `bandMultiplier_fourierMode`, `inner_bandMultiplier_self`, `re_inner_bandMultiplier_le`, `norm_bandMultiplier_le` | band-limited Fourier multipliers: eigenvectors, quadratic form, coercivity and boundedness from symbol bounds |
| `swiftHohenbergMultiplier_energy_le`, `quarticGrowthMultiplier_energy_le` | M3/M7 and E12/E64 scalar symbols lifted to `L²` energy bounds `≤ μ‖P_S f‖²`, `≤ (r + a²/4b)‖P_S f‖²` |

`WCTLean/Models/FisherCurvature.lean` — E78 on the periodic 1D model
`[0, 2π]` with the maintained corrected operator `thetaComplex` and `Δψ = ψ''`:

| Declaration | Content |
|---|---|
| `e78_no_universal_constant` | for every `c > 0`, every `ε`, every `α ≥ 0`, a smooth periodic witness `ψ_k = 1 + cos(kx)/2` violates `c∫|Θ_ε|² ≤ I_F` |
| `e78_universal_bound_false` | no `c > 0` makes E78 hold on smooth periodic fields with `|ψ|² ≥ 1/4` |
| `e78Probe_fisher`, `e78Probe_curvatureEnergy_ge`, `e78Probe_mass` | `I_F[ψ_k²] = k²π`, `∫|Θ_ε[ψ_k]|² ≥ k⁴π/(9+4ε²)²`, fixed mass `∫ψ_k² = 9π/4` |
| `e78_fisher_curvature_identity` | real `C²`, zero-free, periodic boundary values: `I_F[ψ²] = 4∫Re Θ_ε[ψ]·D_ε(ψ) = 4∫(ψ')²` for every `(ε, α)` |
| `e78_fisher_sq_le_curvature_energy` | reverse inequality `I_F² ≤ 16 (∫D_ε²)(∫|Θ_ε|²)` |
| `periodic_integral_mul_second_deriv`, `fisher_sq_eq_four_dirichlet`, `interval_cauchy_schwarz` | periodic integration by parts, Fisher–Dirichlet identity, Cauchy–Schwarz |

Scope: these are periodic one-dimensional statements. They are not
whole-space WCT results and do not address complex fields with nontrivial
phase in the identity (only the counterexample allows general complex fields).

## Nodal ε → 0 dichotomy for the curvature energy (issue #22)

`WCTLean/Models/CurvatureNodalEnergy.lean`, one-dimensional model with the
maintained `thetaComplex` and `Δψ = ψ''`; 12 roots audited fail-closed
(`scripts/curvature_nodal_energy_axiom_audit.lean`), only standard axioms.

| Declaration | Content |
|---|---|
| `norm_thetaComplex` | exact modulus `|Θ_ε| = |Δψ||ψ|/D_ε(ψ)` |
| `curvature_energy_node_lower_bound` | complex fields, supplied Laplacian: if `c|x-x₀| ≤ |ψ| ≤ L|x-x₀|` and `|Δψ| ≥ m` on `[x₀-ε, x₀+ε]`, `α ≥ 0`, then `∫|Θ_ε|² ≥ 2m²c²/(3(L²+1)²ε)` |
| `simple_zero_local_bounds` | a simple zero of a `C¹` real field vanishes exactly linearly nearby |
| `nodal_curvature_energy_lower_bound` | real `C²` field, simple zero with `ψ''(x₀) ≠ 0`: `∫_{x₀-ε}^{x₀+ε}|Θ_ε|² ≥ C/ε` for `0 < ε ≤ δ` |
| `nodal_curvature_energy_tendsto_atTop` | the energy on any interval containing such a node tends to `+∞` as `ε → 0⁺` |
| `cos_sub_half_curvature_energy_tendsto_atTop` | concrete smooth `2π`-periodic witness `cos x - 1/2`: one-period energy `→ +∞` |
| `curvature_energy_tendsto_of_multiplicative` | if `ψ'' = Vψ`, `V` continuous, nodal set null: `∫₀^{2π}|Θ_ε|² → ∫₀^{2π}V²` (any `α`) |
| `sin_curvature_energy_tendsto` | eigenmodes `sin(kx)`, `k ≠ 0`: energy `→ 2πk⁴` |

`WCTLean/Models/CurvatureNodalWeakLimit.lean` (10 roots,
`scripts/curvature_nodal_weak_limit_axiom_audit.lean`) separates the modes of
convergence at a simple node with nonzero Laplacian:

| Declaration | Content |
|---|---|
| `nodal_curvature_L1_lower_bound`, `nodal_curvature_L1_tendsto_atTop` | `∫|Θ_ε| ≥ C log(δ/ε)`; no strong `L¹_loc` limit (any `α ≥ 0`) |
| `nodal_ibp_identity` | `α = 0`: `∫Θ_ε φ = [u log(ψ²+ε²)]_a^b - ∫u' log(ψ²+ε²)`, `u = -ψ''φ/(2ψ')` |
| `nodal_log_integral_tendsto`, `log_sq_add_sq_bound`, `tendsto_log_sq_add_sq` | dominated convergence of the logarithmic term (log-integrable majorant) |
| `nodal_curvature_weak_limit` | `α = 0`, `C³` field, slope floor `|ψ'| ≥ c` on `[a,b]`, zero in `(a,b)`, `C¹` test function: `∫_a^b Θ_ε φ` converges, with explicit limit `nodalWeakLimit` |
| `cos_sub_half_nodal_trichotomy` | `cos x - 1/2` on `[π/6, π/2]`: `L²` and `L¹` norms diverge, weak pairing converges |

Interpretation: energy convergence as `ε → 0⁺` is decided at the nodal set.
It fails at rate `1/ε` whenever a simple node carries nonzero Laplacian and
holds when the Laplacian factors through the field. Not addressed: whole-space
fields, two-dimensional vortex nodes, weak-formulation (distributional)
limits, and nodes of actual WCT PDE trajectories.

## Linear M7 evolution on `L²(AddCircle T)` (issues #19/#21, linear part only)

`WCTLean/Models/M7LinearSemigroup.lean`; 18 roots audited fail-closed
(`scripts/m7_linear_semigroup_axiom_audit.lean`), only standard axioms.
Periodic one-dimensional model; the nonlinear curvature term is **not**
included.

| Declaration | Content |
|---|---|
| `evolution`, `fourierCoeff_evolution` | `S(t)f = ∑ e^{t⁺σ(n)} f̂(n) e_n` for any real symbol bounded above |
| `evolution_zero`, `evolution_add_time`, `evolution_sub`, `evolution_smul` | identity, semigroup law, linearity |
| `norm_evolution_le`, `norm_evolution_sub_le` | `‖S(t)f‖ ≤ e^{μt⁺}‖f‖`; Lipschitz dependence on data |
| `tendsto_evolution_zero` | strong continuity at `t = 0` |
| `evolution_fourier_mild`, `fourier_mild_unique` | existence and uniqueness of Fourier-mild solutions on `[0, ∞)` |
| `evolution_fourierMode`, `evolution_exponentially_stable`, `evolution_mode_unbounded` | eigenmodes; exponential stability if `σ ≤ -γ`; modal instability if `σ(k) > 0` |
| `m7SymbolAtWavenumber_le`, `m7_linear_well_posed` | M7 symbol `c₁(σ₀²-k²) - c₂(k⋆²-k²)²` bounded above for `c₂ > 0`; global linear well-posedness |
| `swiftHohenberg_shell_unstable`, `swiftHohenberg_subcritical_stable` | onset instability of a resonant shell mode; subcritical exponential stability |

`WCTLean/Models/M7Smoothing.lean` (6 roots, `scripts/m7_smoothing_axiom_audit.lean`):

| Declaration | Content |
|---|---|
| `m7Symbol_coercive` | M7 symbol `≤ C - (c₂/2)k⁴` for `c₂ > 0` |
| `evolution_H2_smoothing` | any symbol `≤ C - a k⁴`: `∑|k_n²(S(t)f)^(n)|² ≤ e^{2tC}/(2at)‖f‖²`, `t > 0` |
| `m7_H2_smoothing` | M7: spectral `‖ΔS(t)f‖ ≤ e^{tC}(c₂t)^{-1/2}‖f‖` |
| `smoothing_rate_integrable` | `t^{-1/2}` integrable on `(0, τ)` (Duhamel requirement) |

## Curve-integral locking and winding (issue #24)

`WCTLean/Models/CurveLocking.lean`; 15 roots audited fail-closed
(`scripts/curve_locking_axiom_audit.lean`), only standard axioms.

| Declaration | Content |
|---|---|
| `exp_logCurveIntegral` | `exp(∫_a^b γ'/γ) = γ(b)/γ(a)` for `C¹` nonvanishing curves |
| `winding_quantized` | closed loop: `∮ dψ/ψ = 2πi n`, `n ∈ ℤ` |
| `phaseCirculation_windingQuantized`, `amplitude_return_zero` | `Im ∮ dψ/ψ` satisfies E11 `WindingQuantized`; `Re ∮ dψ/ψ = 0` |
| `field_loop_winding_quantized` | `ψ` `C¹` and nonvanishing on open `U ⊆ E` (real normed space), `c` a `C¹` loop in `U` |
| `logCurveIntegral_of_global_log`, `logCurveIntegral_eq_zero_of_global_log` | path independence with a single-valued `C¹` logarithm |
| `polar_phaseCirculation` | local identity: `γ = ρe^{iθ}` ⇒ circulation `θ(b) − θ(a)` |
| `no_global_log_of_winding_ne_zero`, `logCurveIntegral_exp_int`, `exp_int_loop_closed`, `exp_int_loop_no_global_log` | global obstruction; every integer winding occurs |
| `logCurveIntegral_mul`, `product_loop_windingQuantized` | E11 additivity from products of loops |
| `alpha_determined_by_winding` | E4 locking constant fixed by the geometric winding |

## Continuum obligations (issue #28)

`WCTLean/Models/ContinuumObligations.lean`; 9 roots audited fail-closed
(`scripts/continuum_obligations_axiom_audit.lean`).

| Declaration | Content |
|---|---|
| `coreIntegrability_improper_iff`, `coreIntegrability_integral`, `coreIntegrability_not_integrable` | `r^(2p-2)` integrable on `(0,R)` iff `p > 1/2`; value `R^(2p-1)/(2p-1)` |
| `phaseCoherence_integral_bound`, `phaseCoherence_finite_of_memLp` | E50 measurability and integration step; `ψ ∈ L²` corollary |
| `coleHopf_log_derivatives`, `coleHopf_function_bridge`, `coleHopf_heat_iff_log_flow` | EX–FA chain rule derived in 1+1 dimensions; heat flow ⇔ log-curvature flow |
| `ContinuumObligation`, `continuumObligationStatus`, `continuumObligations_closed_count` | typed inventory: 3 of 8 obligations closed, 5 blocked with named missing infrastructure |

## Koide derivation module

`WCTLean/Models/KoideDerivation.lean` proves:

```lean
spinKoide_identity
spinKoide_half
geometricKoide_of_curvature_harmonic
```

These are algebraic consequences of the encoded definitions. They do not derive the physical identification of spin with the Koide mass angle.

## Remaining analytical boundary

Not closed by the current theorem set:

- exact variation of the full WCT action;
- function spaces, admissible domains, and boundary conditions;
- local/global well-posedness of the full nonlinear PDE (the linear M7 part is well posed on `L²(AddCircle T)`, `Models/M7LinearSemigroup.lean`);
- existence, localization, finite energy, decay, and continuum-limit survival;
- linearized spectral and orbital stability;
- `ε → 0` quotient control beyond the one-dimensional nodal dichotomy below (whole-space, weak-formulation and PDE-trajectory limits);
- Fourier analysis beyond the periodic one-dimensional `L²(AddCircle T)` layer (whole-space or curved-domain spectral projection);
- curve-integral locking beyond `C¹` loops on open subsets of real normed spaces (homotopy invariance, general manifold charts);
- theorem-level derivation of particle masses, forces, gauge fields, gravity, cosmology, or experimental claims.

## Frozen D4 Phase VI (`WCTLean/Models/D4Binding.lean`)

Canonical source: geometry_of_resonance PR36 head `31f322c94d2ef32b20acea741884514806025c85`, merge `5a4c58a4206005ad9d46ee2951069186490b01f1`. D4 is square symmetry in two spatial dimensions.

| Classification | Declarations / content | Undischarged boundary |
|---|---|---|
| Definition | `WholeSpaceData`, `State`, `mass`, `hamiltonian`, `I2`, `minimizers` | H² membership and weak Laplacian are explicit inputs; actual Sobolev space, integrability and bounded/nonempty infimum set remain uninstantiated |
| Fully instantiated kernel-checked theorem | `frozen_beta_pos`, `frozen_mass_pos`, `frozen_rho_pos`, `frozen_rho_exact`, `frozen_margin_exact`, `frozen_margin_pos`, `frozen_threshold_pos`, `frozen_below_threshold` | Exact dyadic constants; no analytic assumptions |
| Conditional kernel theorem | `nonlinear_square_completion`, `dilation_polynomial`, `dilation_gap`, `dilation_lower_bound`, `dilation_unique_positive`, `dilation_virial`, `improved_square_identity`, `improved_D_bound` | Exact scalar algebra with displayed sign/nonzero/virial premises; functional change-of-variables and integrated square identity are not yet proved |
| Conditional kernel theorem | `sobolev_cap_from_D_bound`, `L6_L4_ratio_from_cap`, `amplitude_ratio_from_L6_bound`, `amplitude_bound` | Fourier/Sobolev estimate and integral comparison are explicit premises |
| Typed analytic input | `BindingSequenceInputs` | Negative infimum, adjusted minimizing sequences, applied ratio estimate, and admissible amplitude trials; no strict binding assumption |
| Conditional kernel theorem | `infimum_scaling_bound`, `quantitative_gap`, `binding_of_strict_energy_per_mass`, `frozen_strict_binding`, `frozen_I2_strict_binding` | Limit argument and strictly positive quantitative gap are proved; `BindingSequenceInputs` must still be established for actual H² data |
| Typed analytic input | `VariationalCompactnessInputs` | Continuity, translation invariance, minimizing sequence, and subsequential compactness at the specified mass only |
| Conditional kernel theorem | `attainment_of_compactness`, `frozen_minimizers_nonempty` | Attainment derived from convergence; no attained infimum assumed; compactness is not derived from binding here |
| Conditional kernel theorem | `stability_from_energy_trapping` | Conservation, initial energy control and trapping; same-mass data, arbitrary perturbation symmetry; actual global H² flow and distance to the entire minimizing set remain uninstantiated |
| Open analytical obligation | Exclusion of vanishing/dichotomy, concentration compactness, Euler–Lagrange regularity, H² flow, full minimizing-set orbital stability | No finite-dimensional surrogate or numerical candidate is substituted |

Build receipts and source hashes are recorded in `docs/evidence/d4_phase_vi/`. The source contains no placeholder proof or custom axiom. A green build checks the implications, not their uninstantiated continuum premises. Issues #20/#21 remain open. The periodic numerical root, whole-space minimizers, and S004 higher-derivative action remain distinct.

## D4 Phase VII additions

`WCTLean/Models/D4Analytical.lean` adds 11 theorems; the 28 Phase VI theorems
remain unchanged. Kernel-check status is recorded in the Phase VII evidence
receipt, not inferred from this list.

| Theorem | Classification and remaining premises |
|---|---|
| gap_slack_pos, gaussian_d_floor_pos, gaussian_c_cap_pos | Fully instantiated exact rational arithmetic |
| uniform_gap_constant_pos, uniform_gap_constant_gt | Fully instantiated rational κ>1/3000000 |
| frozen_slack_floor | Fully instantiated h*=221/100000 ≤ 1−m/B |
| gaussian_gap_lower | Scalar implication from displayed coefficient bounds; Gaussian integral identities external |
| split_gap_from_per_mass | Scalar split assembly; displayed energy-per-mass inequalities required |
| binding_inputs_from_cap | Constructs old binding inputs from negativity, adjusted sequences, the direct Sobolev cap and admissible amplitude trials; concrete H² instance OPEN |
| nearby_mass_stability_from_trapping | Conservation and explicitly displayed near-mass trapping; concrete flow and trapping instances OPEN |
| no_exit_of_observable_bound | The displayed all-time observable lower bound excludes the specified exit set |

The conventional continuum proof is independently audited in
`docs/D4_PHASE_VII_ANALYSIS.md`. It proves binding, attainment and full-set
orbital stability for the actual two-dimensional functional, and an all-time
moving-ball confinement consequence near its minimizers. Those prose proofs
are not claimed to be instantiated Lean theorems. The numerical periodic
branch is not identified with a whole-space minimizer. D4 is not dimension four.


## Corrected S004 two-component variational and coefficient results (PR #38)

The modules below apply to the **corrected S004 covariant curvature weight**
\(F(s)=s/(s+\varepsilon^2 e^{-2\alpha s})^2\), with \(s=|\psi|^2\),
\(\varepsilon>0\), and \(\alpha\ge0\). They are not proofs for the independent
F01 cubic-quintic evolution.

| Exact maintained declaration | Scope | Open boundary |
|---|---|---|
| `WCTLean.correctedRadialDenominator_floor` | Field-independent denominator lower bound, including nodes | Does not imply positive principal coefficient |
| `WCTLean.correctedRadialWeight_hasDerivAt` | Exact quotient-rule radial derivative | Pointwise; no integrated action |
| `WCTLean.realTwoComponentWeight_hasDerivAt` | Exact real directional derivative of F(x²+y²), including the 2(x dx+y dy) factor | Pointwise |
| `WCTLean.S004JetVariation.curvatureQuadratic_hasDerivAt` | Actual derivative of the independent acceleration/Laplacian quadratic jet | Pointwise |
| `WCTLean.S004TwoComponent.localDensity_hasDerivAt` | Actual first variation of the corrected two-real-component flat S004 local density with variable V and F | One declared spatial gradient component per real field |
| `WCTLean.curvatureWeight_ge_on_amplitude_annulus` | Positive coefficient bound \(F(s)\ge\delta/(M+\varepsilon^2)^2>0\) if \(0<\delta\le s\le M\) | Annulus is not proved invariant under nonlinear flow |
| `WCTLean.arbitrarily_small_weight_high_density` | Explicit high-amplitude failure of global uniform coefficient lower bound | Does not establish PDE ill-posedness |
| `WCTLean.complexWeight_ae_lower_bound` and `WCTLean.curvatureEnergyDensity_ae_lower_bound` | Exact almost-everywhere complex-field and weighted-curvature-density inequalities on the annulus | No integration theorem or invariant Sobolev class is assumed |
| `WCTLean.S004IntegratedVariation.integratedDensity_hasDerivAt_of_dominated` | **Genuine differentiation of the integrated corrected local S004 action density** by combining the verified pointwise derivative with Mathlib dominated parameter differentiation | Requires explicitly stated a.e. potential differentiability, integrability, measurability, common-ball Lipschitz domination; **not proved for arbitrary Sobolev data** |

The exact source definitions are in
`WCTLean/Models/{CorrectedWeightCalculus,CorrectedWeightDirection,S004JetVariation,S004TwoComponentVariation,S004AmplitudeAnnulus,S004PrincipalDegeneracy,S004IntegratedVariation}.lean`.
All are imported from `WCTLean/Main.lean`.

**Not closed:** the complete spatial tensor/gradient assembly, Sobolev trace and
mapping estimates, higher-derivative integration by parts, boundary terms,
identification of the Euler-Lagrange PDE, nonlinear A2/S004 constraint
preservation, and local/global WCT PDE well-posedness. Issues #17-#19 stay OPEN.
The current PR's CI status must be checked at its exact final head; an earlier
green run does not certify later commits.


## S004 Phase XVII: full finite-spatial-gradient corrected action and integral variation

**Exact maintained source:**
`WCTLean/Models/S004FullSpatialJet.lean` and
`WCTLean/Models/S004FullSpatialIntegratedVariation.lean`, imported from
`WCTLean/Main.lean`. In the flat complex scalar model with `d` spatial
directions, all `Fin d` gradient squares appear, together with the
independent acceleration, Laplacian, potential and corrected
`F(|psi|²) = |psi|²/(|psi|²+epsilon² exp(-2 alpha |psi|²))²` terms.

| Theorem | Kernel-checked mathematical scope | Unresolved obligation |
|---|---|---|
| `S004FullSpatialJet.gradient_sum_hasDerivAt` | First variation of the complete finite spatial-gradient energy sum, every `d : Nat` | Pointwise finite jet, not a PDE |
| `S004FullSpatialJet.fullLocalDensity_hasDerivAt` | Entire flat two-real-component S004 local density derivative, **all d spatial gradients**, corrected regulator and arbitrary differentiable potential | No IBP or Sobolev space map |
| `S004FullSpatialIntegral.action_hasDerivAt_of_dominated` | **Integrated** first variation of that exact flat local density on an arbitrary measured domain; mathematically derived from pointwise variation and Mathlib differentiation under the integral | Requires separately justified measurable/integrable action, a.e. potential derivative and common-neighborhood integrable Lipschitz bound |
| `S004AmplitudeAnnulus.curvatureWeight_ge_on_amplitude_annulus` | Explicit strict positive curvature coefficient on `0<delta<=|psi|²<=M` | Annulus neither invariant nor globally admissible for arbitrary L² whole-space fields |

An important negative analytical constraint: the kernel-checked
`ReyesMath.E26.not_ae_norm_ge_of_memLp` in
`rickyjreyes/math/lean/MathProofs/RegularizedCurvatureL2.lean`
proves that a finite-mass L² field on Euclidean whole space cannot
possess a positive uniform amplitude floor a.e. The annulus-based
positive coefficient estimate must therefore not be advertised as a
global uniformly elliptic PDE regime for all finite-mass whole-space
initial data. It may be relevant on bounded or periodic domains, or
for local patch estimates.

**Open:** derive domination from explicit Sobolev hypotheses;
higher-order integration by parts with appropriate boundary traces;
the exact weak and strong Euler-Lagrange PDE; local/global nonlinear
WCT well-posedness; canonical constraints and a dynamically invariant
healthy nonlinear S004/A2 sector.

The exact-head reproducibility workflow runs
`scripts/s004_axiom_audit.lean` for ten concrete theorem roots.


## S004 Phase XVIII: actual Euler momenta, Green identities and compatible field action

The following results are maintained under `WCTLean/Main.lean`, from
the **original corrected two-real-component S004 action**, including the
nonlinear \(F(|\psi|^2)\) multiplier, the potential derivative, every
`Fin d` spatial gradient and the original acceleration/Laplacian
mixed curvature quadratic.

| Kernel theorem | Exact mathematical statement | Still missing |
|---|---|---|
| `S004EulerCoefficients.curvature_direction_coefficients` | Computes both independently varying coefficients of \(K(a,b)\), including mixed \(\gamma\) term | Integrated action assembly |
| `S004EulerCoefficients.fullLocalDirection_coefficients` | Decomposes actual full corrected density variation into field force, time momentum, all spatial gradient terms, acceleration momentum and Laplacian momentum | Continuum adjoints |
| `S004EulerCoefficients.fullLocalDensity_hasDerivAt_coefficients` | Those exact Euler momenta are **actually** the directional derivative of the maintained nonlinear S004 local action density | Full weak PDE |
| `S004IntervalGreen.integral_mul_first_deriv_eq_neg` and `integral_mul_second_deriv_eq` | Real interval-integral first and second temporal integration by parts with genuine boundary trace cancellation, proved via Mathlib FTC | Multidimensional spacetime Fubini |
| `S004IntervalGreen.integral_mul_first_deriv_periodic` and `integral_mul_second_deriv_periodic` | Real periodic-cell first/second derivative Green identities with matching 0th/1st traces | Actual periodic Sobolev realization |
| `S004CompatibleFields.jetOf_fieldShift` | All field, velocity, acceleration, spatial gradient and Laplacian variations derive from a **single** field path when first-order derivative operators are linear and higher derivatives are iterated | Concrete operators on Sobolev functions |
| `S004CompatibleFields.fieldAction_hasDerivAt_of_dominated` | Genuine integrated corrected field-action first variation, compatible derivatives, explicit measurable/integrable Lipschitz domination | Discharge domination from chosen regularity |
| `S004TemporalEuler.x_component_temporal_euler` / `y_component_temporal_euler` | Exact nonlinear S004 temporal \(-\partial_t P_t+\partial_t^2P_{tt}\) contributions after genuine second-order time IBP, with admissible test traces | Combine into full spacetime PDE |
| `S004SpatialEuler.x_component_periodic_euler` / `y_component_periodic_euler` | Exact one-dimensional periodic spatial \(-\partial_xP_g+\partial_x^2P_\Delta\) contributions for corrected S004 gradient and Laplacian momenta | Extend to d dimensions and Fubini |

The updated `scripts/s004_axiom_audit.lean` checks **26 named theorem
roots**. `scripts/check_s004_axioms.py` fails closed if any root is
missing or any axiom other than the ordinary logical axioms appears.
Check exact-head GitHub Actions before treating any fresh audit as final.

**Critical scope boundary:** This is not yet a kernel-verified
**combined spacetime Euler–Lagrange equation** for S004. The
time-direction and 1D periodic spatial integrations have been proved
separately. They must be assembled using actual spacetime measure,
Fubini, concrete Sobolev derivative operators, valid product/quotient
estimates, boundary traces and a weak-to-strong PDE correspondence.
No nonlinear A2/S004 well-posedness or ghost elimination follows.


## Phase XIX: actual 1+1 spacetime S004 Euler–Lagrange assembly

**New kernel-verified modules**, imported in `WCTLean/Main.lean`:

- `S004SpacetimeFubini.lean`:
  `rectangle_integral_swap` and
  `corrected_density_direction_swap` prove real Lebesgue
  time/space interval integration interchange from
  **product-measure integrability**, using the Mathlib theorem pinned
  at Lean 4.23.0 (rather than an unavailable newer wrapper).
  `continuous_rectangle_integrable` proves the required
  integrability for continuous integrands on compact rectangles;
  `continuous_rectangle_integral_swap` discharges the original
  Fubini hypothesis in that regular case.
- `S004SpacetimeGreen.lean`:
  `temporal_first_spacetime`,
  `temporal_second_spacetime`,
  `spatial_first_spacetime` and
  `spatial_second_spacetime` are four **actual 1+1-dimensional
  continuum Green identities**, built from the verified one-variable
  FTC integration-by-parts and real Fubini. They require ordinary
  coefficient/test derivative regularity, integrability, zero
  temporal traces, and periodic spatial traces; the desired adjoint
  identities are not assumed.
- `S004SpacetimeEuler.lean`:
  `weakComponent_eq_strongComponent` is ONE combined 1+1
  spacetime theorem, for either real field component, converting
  the five true nonlinear S004 coefficient contributions (field,
  time gradient, time acceleration, space gradient and Laplacian)
  from weak to strong integral pairings. The curvature coefficient
  retains the full density-dependent regulator and its exact
  derivative.
  `fullLocalDirection_eq_component_sum` certifies that the
  two individual real-component weak densities REASSEMBLE the
  ORIGINAL corrected S004 local action derivative.
  `integrated_fullLocalDirection_component_split` certifies
  the corresponding true Lebesgue integral splitting under
  ordinary integrability hypotheses.

**Formal verification:** the corrected-action modules and the
pointwise/integrated component reassembly compiled in the maintained
pinned Lean repository. The exact-head strict audit was expanded from
26 to **37 named theorem roots**; inspect its final CI result before
claiming that updated audit is green.

**Still OPEN:** #17 requires a single original *action* critical-point
iff distributional Euler–Lagrange theorem, including correct
single-integral to iterated-integral termwise linearity, complete
actual weak-derivative realization, trace and density arguments,
and weak-to-strong equivalence. #18 requires an actual admissible
Sobolev phase space and quotient/product mapping estimates
discharging the remaining hypotheses. The current 1+1 theorem
addresses the smooth finite-period-cell case under explicit
classical derivative/integrability conditions, not all
`H^s(I × 𝕋^d)` data. Neither result proves #19 PDE
well-posedness.


## Phase XX: Euler residual separation and boundary-compatible test functions

The following maintained Lean modules are imported by `WCTLean/Main.lean`
and remain **specific to the corrected nonlinear two-real-component
S004 action**. They do not concern the separate F01 Hamiltonian.

| Proof declaration | Exact statement and scope | Not established |
|---|---|---|
| `S004EulerSeparation.all_integrable_probes_zero_iff_ae_zero` | For a genuinely square-integrable real residual on any measure space, zero pairing against **every test with integrable product** is equivalent to vanishing almost everywhere, proved using the nonnegative integral of the residual squared | The test class is broader than smooth compactly time-supported S004 variations |
| `S004EulerSeparation.two_component_integrable_probes_iff_ae_zero` | Separate the real and imaginary Euler residuals by independently choosing the two actual field-component test directions | No action-to-admissible-variation density result |
| `S004EulerSeparation.corrected_euler_all_probes_iff_ae_equations` | Applies the preceding lemma to the **actual S004 nonlinear corrected strong Euler residual** obtained from the previously verified full force, time/acceleration and spatial/Laplacian momenta | Does not assert those abstract tests are all admissible original-action variations |
| `S004ContinuousEuler.continuous_square_integrable` | Derives the real (L^2) input from continuity on an actual compact time × periodic fundamental rectangle using Lebesgue integrability | Smooth/Sobolev mapping regularity for the S004 field still needs construction |
| `S004ContinuousEuler.corrected_euler_continuous_probes_iff_ae_equations` | Applies actual corrected S004 duality with no separately assumed (L^2) estimate when its two strong residuals are continuous | All-continuous test directions do not automatically meet S004 second-order trace conditions |
| `S004BoundaryWeightedEuler.weighted_zero_integral_iff_ae_zero` | On the actual OPEN spacetime rectangle, the nonnegative weighted square integral with (w(t)=(t-a)^2(b-t)^2>0) in the interior vanishes iff the Euler residual vanishes a.e. | Requires actual integrability of that weighted square |
| `S004BoundaryWeightedEuler.weighted_test_zero_temporal_traces` | Proves that (h(t,x)=w(t)E(t,x)) has (h=\partial_t h=0) at both temporal endpoints when E has endpoint derivatives | Does not alone establish interior (C^2) or spatial derivative regularity |
| `S004BoundaryWeightedEuler.weighted_test_periodic_values` | Proves that the same explicit test inherits spatial periodic VALUE traces when E has them | Periodicity of spatial first derivatives remains a separate analytical condition |
| `S004BoundaryWeightedEuler.boundary_periodic_test_critical_forces_ae_euler` | A genuine restricted fundamental lemma: vanishing residual pairing for every test with the specified temporal and periodic value traces forces the residual to be zero a.e.; the proof explicitly constructs and validates its weighted residual test | **Not yet** the original action-critical-point iff full S004 distributional PDE result |

The exact-head axiom audit is expanded to **54 roots**, including all
16 new theorem roots from these three modules. A passing CI result is
necessary before reporting that 54-root audit as verified.

**Original-claim boundary:** #17 remains open until the original
field action and admissible (C^2/H^s) test space are identified
with the complete spacetime Euler pairing, including justified
spatial first-derivative periodic traces and a weak-to-strong
equivalence. #18 remains open until actual Sobolev derivative and
quotient composition estimates discharge the remaining analytical
hypotheses. Neither result establishes nonlinear S004 flow
well-posedness (#19).

### Phase XX follow-up: first spatial-derivative trace for S004 Euler tests (issue #17/#18)

The `WCTLean/Models/S004FirstSpatialTraceEuler.lean` module proves that the explicit weighted Euler test `h(t,x)=w(t)E(t,x)` satisfies both the zero temporal value/first derivative traces and **the first spatial-derivative periodic trace**, provided the corrected residual has a classical spatial derivative with matching endpoint traces. Its `corrected_euler_first_spatial_trace_critical_forces_ae` theorem instantiates the separation argument with the genuine nonlinear corrected S004 Euler residual, without assuming the Euler equation. This establishes a missing first-order trace condition, **not** higher-order Sobolev admissibility, action-criticality equivalence, or PDE well-posedness. See the four new exact theorem roots in `scripts/s004_axiom_audit.lean`.

### 2026-11-11 original S004 spacetime action-to-weak bridge (#17/#18)

`WCTLean/Models/S004SpacetimeActionBridge.lean` proves `rectangleVolume_integral_eq_iterated`, `five_terms_integrable`, `weakPointwise_integral_eq_weakComponent`, and `originalAction_hasDerivAt_iterated_weak`. This links the actual corrected nonlinear integrated S004 action's directional derivative to the original five-term, time-major real/imaginary weak Euler functionals on a 1+1 finite spacetime rectangle. Product Fubini and Lebesgue linearity are proved, not assumed as a conclusion. The domination and five-term integrability conditions remain explicit. No unconditional smooth/Sobolev field-space differentiability, original-action strong Euler criticality equivalence or PDE well-posedness is claimed. These four roots are included in the expanded exact axiom audit.

### 2026-11-11 complete conditional S004 action-to-strong Euler bridge (#17)

`WCTLean/Models/S004SpacetimeStrongBridge.lean` supplies `green_data_proves_weak_strong` and `originalAction_hasDerivAt_strong`. The latter identifies the genuine corrected nonlinear S004 integrated-action derivative on an actual finite 1+1 Lebesgue rectangle with the FULL two-component strong Euler integrals including real temporal first/second acceleration and periodic spatial gradient/Laplacian momentum derivatives. The proof derives the weak-to-strong step from the real Green theorem under named exact derivative, trace and product-integrability premises. It does **not** derive that every smooth/Sobolev field automatically satisfies these analytical hypotheses, identify all jets with concrete Sobolev derivatives, prove integrated residual separation on the same variation class, or close #17/#18.

### 2026-11-11 original corrected S004 action-to-Euler single-pairing theorem

`WCTLean/Models/S004SpacetimeEulerPairing.lean` proves `integral_five_signed`, `strongComponent_eq_residual_pairing`, and `originalAction_hasDerivAt_euler_pairing`: the original corrected nonlinear S004 action derivative is the sum of ONE actual Lebesgue integral per real Euler component, with the exact corrected residual from `S004EulerSeparation.correctedEulerResidual` (including F' and higher momenta). The proof composes existing verified action differentiation, product Fubini and real 1+1 Green formulas; it does not presume the desired pairing identity. Explicit product integrability for the residual's strong spatial derivatives is required in addition to the action/Green analytic hypotheses. **Not yet proved:** field-jet realization from a concrete smooth/Sobolev class; sufficient nonlinear regularity to discharge those analytic hypotheses; criticality to Euler equivalence and weak-to-classical equivalence. #17 and #18 remain OPEN.

### 2026-11-11 Phase XXII: original corrected S004 continuous finite-cell admissibility (#18, #17)

`S004ContinuousAdmissibility.lean` proves six new audited declarations. The actual regularized S004 quotient is continuous for continuous real and imaginary field components even at nodes, with no positive-amplitude annulus assumption. Its genuine Lebesgue integrability on finite 1+1 rectangles follows. Compact-domain continuous classical weak coefficient/test products imply each of the **ten** original weak integrability premises for both real components. Four strong spatial products follow analogously. `originalAction_hasDerivAt_euler_pairing_of_continuity` instantiates the exact original-action Euler integral theorem while **deriving**, rather than assuming, those fourteen integrability inputs. The ORIGINAL nonlinear action and regulator remain unchanged. Precise limits: differentiation-under-integral domination, actual derivative jet realization, periodic Green traces, and Sobolev composition estimates still appear as named hypotheses; full #18 and criticality equivalence remain OPEN.

### 2026-11-12 Phase XXIII: original corrected S004 action density is integrable for continuous classical jets

`S004ClassicalDensity.lean` formalizes continuity of every physical real/imag S004 jet coordinate, demonstrates its closure under the *actual* simultaneous jet shift, and derives continuity of the original corrected high-order curvature quadratic and full nonlinear density. Continuous original potential and nonzero regulator suffice for actual finite-rectangle Lebesgue integrability of the full action density for **every** perturbation parameter. The original density and F(rho) remain unchanged, including field nodes. This is an analytically discharged action integrability premise, not full domination, derivative-jet realization, Sobolev mapping, action criticality equivalence or a solution to geometry #53. Audit count 73→78.

### Phase XXIII genuine classical field-to-jet realization

`S004ClassicalField.lean` adds a pair of real classical scalar fields with actual first/second ordinary time and space derivative certificates, common field shifts with derivative linearity, and a verified bridge to the original corrected S004 full physical jet. The action density of every varied genuine C²-type field is Lebesgue integrable on a compact spacetime cell from the preceding original-density theorem. This discharges independent-jet compatibility for this explicit classical derivative class, but does not derive smoothness from Sobolev membership or prove the stronger Green trace/Lipschitz domination and criticality equivalence requirements. Five roots added (78→83).

### Phase XXIII: periodic original-field derivative traces from actual scalar derivatives

`S004ClassicalPeriodicity.lean` verifies the real differentiation theorem that a translation-periodic classical scalar function has translation-periodic first and second derivatives. Applied separately in spatial and temporal directions to a genuine `ClassicalScalarField`, an original spatial field periodicity assumption implies every one of its five physical jet components (field, velocity, acceleration, gradient, Laplacian) is periodic. For real and imaginary fields this discharges the ten independent jet-value matching conditions. This does not imply nonlinear Euler momentum Green regularity, Sobolev traces or full action domination. Five new roots (83→88).
