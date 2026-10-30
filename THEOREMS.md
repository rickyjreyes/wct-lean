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

## Continuum integration branch for issues #19–#21

The pinned `reyes_math` dependency imports actual `H²(ℝ²; ℂ)` theorems
in `WCTLean/Continuum/CubicQuinticWholeSpace.lean`. The new exported
declarations prove whole-plane independent cubic–quintic existence, nonzero
positive-mass minimizers, spatial-translation invariance, strong H² compactness
modulo translations, global independent flow, and full minimizing-set orbital
stability. Exact D4 binary64 coefficients are recorded as rational constants.

**Scope:** These theorems concern an independently defined fourth-order
cubic–quintic Hamiltonian on ℝ². They do **not** establish local evolution
well-posedness for the corrected curvature quotient, identify the periodic D4
numerical root, certify a torus linearized gap, or assert physical WCT stability.
See `docs/WCT_CONTINUUM_19_21_AUDIT.md` for the issue-by-issue proof ledger.


The independent cubic–quintic pointwise nonlinearity is also represented in `WCTLean/Continuum/CubicQuinticLinearization.lean`: its exact real-linear algebraic terms and higher-order remainders are proved for arbitrary complex perturbations. These polynomial identities do not by themselves establish a Fréchet derivative on the torus's unbounded operator domain or the D4 spectral gap.

The corrected M2/E17 curvature quotient has an additional exact pointwise limitation: `WCTLean.Continuum.no_positive_uniform_quotient_coefficient_lower_bound` rules out any strictly positive global lower bound on the modulus of the quotient's Laplacian coefficient, because it vanishes at field nodes. This is **not** a theorem of failure of uniform ellipticity for the complete governing PDE, let alone ill-posedness or finite-time blow-up.

### Positive canonical curvature-energy obstruction (#20)

The positive corrected-curvature candidate `E(u) = K(u) + Wc(ε,α,u)`,
on `H²(ℝ²; ℂ)`, has an exact constrained infimum zero **without any
attaining minimizer** when ε>0, α≥0 and mass m>0. Indeed no mass-m field
is even a local constrained minimum: arbitrarily small H² neighborhoods
contain an equal-mass lower-energy dilation. These are instantiated
whole-space theorems from the pinned `MathProofs.CurvatureNonattainment`,
not a no-go theorem for all canonical WCT dynamics or nonvariational
localized solutions. They directly rule out this specific **positive-energy
constrained-minimization route** to intrinsic confinement.

Exact exported declarations:
`WCTLean.Continuum.canonical_positive_energy_infimum_zero`,
`WCTLean.Continuum.canonical_positive_energy_nonattainment`,
`WCTLean.Continuum.canonical_positive_energy_no_local_minimizer`.


### Independent whole-plane CQ flow: continuous dependence and conservation

`WCTLean/Continuum/CubicQuinticFlowBridge.lean` now directly exports the
infinite-dimensional, mass-changing-perturbation continuous-dependence theorem
and the all-real-times mass/energy conservation theorem from pinned
`ReyesMath.OrbitalStability.global_flow`. It also instantiates global
well-posedness and conservation at the exact rational frozen CQ coefficients.
These theorems are **not** a well-posedness theorem for the corrected
quasilinear M2/M6B/M7 curvature evolution or the periodic D4 stationary
branch. CI is the authority for the new declarations' compilation status.

## External periodic D4 certificate status, distinct from Lean verification

The frozen periodic D4 root and qualitative all-time orbital-stability
certificates are not simply missing. In `wct-pde`, **#24 and #25 are closed
under their explicitly scoped continuum acceptance criteria** at source commit
`e9a2b589243cfc8fa1492b67a02949c9ba660e93`, with independent
160-bit Arb existence and 160/192-bit coercivity verification and CI
[38775402440](https://github.com/rickyjreyes/wct-pde/actions/runs/38775402440).

- [Existence audit](https://github.com/rickyjreyes/wct-pde/blob/e9a2b589243cfc8fa1492b67a02949c9ba660e93/docs/D4_INDEPENDENT_EXISTENCE_AUDIT.md):
  real D4-gauge stationary solution on `R²/(42Z)²`, full Fourier Wiener
  existence radius `10^-8`, explicit residual, inverse, tail, and saved-array
  linkage bounds. This is *not* whole-space existence on `R²`.
- [Stability audit](https://github.com/rickyjreyes/wct-pde/blob/e9a2b589243cfc8fa1492b67a02949c9ba660e93/docs/D4_INDEPENDENT_STABILITY_AUDIT.md):
  complete complex perturbation sectors, all infinite spectral tails,
  constrained `H²` coercivity reported above
  `0.0008267789943812908`, phase/translation kernels, mass-normal
  directions, and qualitative local all-time orbital stability.
  An explicit numerical orbital basin for arbitrary data remains open.

**Trust boundary:** These are externally checked computer-assisted
mathematical certificates using a Python/FLINT/Arb trusted computation
chain. They are **not kernel-checked Lean declarations** and are not
automatically imported by this PR. Issue #21 remains PARTIAL as a *Lean
formalization* until the relevant infinite-dimensional Wiener/torus spaces,
exact candidate and outward certificate data, operator inverse/tail
estimates, spectral coercivity, modulation and flow are formally connected.

No contradiction exists between scoped PDE #24/#25 completion and unfinished
WCT-Lean #21. No claim of external independent expert review is implied.
