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

The M6B results establish exact local operator form and denominator safety. They do not prove uniqueness of the nonlinear closure or PDE well-posedness.

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

`cos_orthogonality_TODO` is a proposition definition, not a proof.

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
- local/global well-posedness of the full nonlinear PDE;
- existence, localization, finite energy, decay, and continuum-limit survival;
- linearized spectral and orbital stability;
- `ε → 0` quotient control;
- complete Fourier integral orthogonality;
- curve-integral locking on manifolds;
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
