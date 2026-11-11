# WCT Lean Formal Coverage Index

This index separates **canonical registration**, **equation-specific typed support**, **kernel-proved content**, and **physical validation**.

## Canonical navigation

- [Corrected 142-object equation registry](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/WCT_FULL_EQUATION_LIST_CORRECTED.md)
- [Master equation architecture](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/WCT_MASTER_EQUATIONS_UPDATED.md)
- [Complete SymPy classification](https://github.com/rickyjreyes/wct-sympy/blob/main/VERIFICATION_INDEX.md)
- [Lean theorem inventory](THEOREMS.md)
- [SymPy-to-Lean map](SYMPY_MAP.md)
- [Public research-corpus map](https://rickyjreyes.github.io/research-corpus/)

The canonical registry defines equation text, symbols, assumptions, and scientific boundaries. Lean claims only what its declarations encode and what the kernel accepts under displayed hypotheses.

## Layer 1 — Compiled canonical registration: 142 / 142

`WCTLean/Registry.lean` compiles every canonical ID:

| Family | Count |
|---|---:|
| Master systems | 9 |
| Canonical equations | 83 |
| Curvature-locked electron equations | 10 |
| Auxiliary equations | 5 |
| Cosmology equations | 20 |
| Topology equations | 9 |
| Correction equations | 6 |
| **Total** | **142** |

Lean proves registry length, family partition, status partition, uniqueness, and completeness through:

```lean
masterIds_length
canonicalIds_length
electronIds_length
auxiliaryIds_length
cosmologyIds_length
topologyIds_length
correctionIds_length
allEquationIds_length
allEquationIds_nodup
statusPartition_length
statusPartition_nodup
statusPartition_complete
every_registered_id_has_status
every_registered_id_has_family
canonicalRegistry_length
```

The effective symbolic-audit partition inherited from the current `wct-sympy` main branch is:

| Status | Count |
|---|---:|
| `PASS` | 68 |
| `CONDITIONAL` | 18 |
| `DEFINITION` | 26 |
| `OPEN` | 30 |
| **Total** | **142** |

These are inherited symbolic-audit classifications, not Lean theorem counts. The active SymPy expansion PR is intentionally tracked separately until it is merged to `wct-sympy` main.

## Layer 2 — Non-registry typed Lean support: 92 IDs (this branch, subject to CI)

The following IDs have a maintained equation-specific definition, proposition, theorem, counterexample, analytic contract, or kernel-checked constraint beyond registry metadata:

```text
M1 M2 M3 M4 M5 M6A M6B M7
E1A E1B E2 E3 E4 E5 E6 E7 E8 E9 E10 E11
E12 E13 E14 E15 E16 E17 E18 E19 E20 E22
E24 E25 E26 E27 E28 E29 E32 E33 E36 E37 E38 E41
E44 E44 E45 E47 E49 E50 E51 E53
E57 E58 E59 E60 E61 E62 E64
E65 E66 E67 E68 E69 E70 E72
E78 E81 E82
CLE4 CLE5 CLE6 CLE7 CLE8 CLE9 CLE10
G1 EX EY EZ FA
CM3 CM4 CM9 CM10 CM11 CM12 CM13 CM15 CM16 CM20
TOP3 TOP6 TOP7
CORR2
```

The branch's kernel-checked coverage expansion adds eighteen IDs relative to the original 62-ID baseline:

```text
E16 E19 E22 E32 E37 E38 E41 E50 E72
CLE4 CLE5 CLE6 CLE7 CLE8 CLE9 CLE10
CM11 TOP3 TOP6 TOP7 CORR2
```

Some of these are exact conditional constraints rather than proofs of the full physical claim. They count as equation-specific formal support because the theorem itself is kernel-checked; they do **not** change the scientific status of the associated canonical claim unless a separate symbolic or analytic audit justifies that change.

### Direct algebraic, order-theoretic, counting, or finite-dynamical theorem support

```text
M1 M2 M3 M4 M5 M6B M7
E2 E3 E4 E5 E8 E9 E10 E11
E12 E13 E14 E15 E16 E17 E18 E19 E20 E22 E28 E29 E32 E33 E36 E37 E38 E41
E45 E47 E49 E50 E51 E53
E57 E58 E59 E60 E61 E62 E64 E72 E81 E82
CLE4 CLE5 CLE8 CLE9 CLE10
G1 EX EY EZ FA
CM3 CM4 CM9 CM10 CM11 CM15 CM20
TOP3 TOP7
CORR2
```

This category includes conditional theorems, finite analogues, scalar reductions, exact algebraic bridges, counting lemmas, and quantitative error bounds. It does not imply full PDE, variational, continuum, or physical closure.

### Dimensional support

```text
E1A E1B E6 E7
```

### Definitions or model skeletons

```text
M6A E25 E27 E65 CM12 CM13 CM16
```

### Explicit analytic contracts or predicates

```text
M4 E24 E26 E66 E67 E68 E69 E70
```

The contracts expose missing Sobolev, regularity, interpolation, and stability hypotheses rather than assuming them silently.

### Counterexample or unresolved proposition support

```text
E17 E78
```

E17 includes both the historical scalar-denominator counterexample and the corrected complex denominator theorem. E78 remains a proposition/TODO rather than a completed Fisher-information theorem.


### Current 12-ID source-level closure batch

Beyond the preceding 80-ID baseline, existing `NarrowCanonicalCoverage.lean` supplies equation-specific E15, CLE6 and CLE7 support, and this PR adds exact narrowly scoped statements for TOP6, CM3, CM4, CM10, CM15, CM20, E44, E60 and E82. Together these yield **92/142 IDs with substantive typed support**, leaving 50 registry-only, **conditional on CI accepting the new module**. See [the mathematical scope and analytic cross-references](docs/REGISTRY_ONLY_CLOSURES_2026-10-30.md).

TOP6's geometric/isotopy step, CM15's continuum derivative chain rule and E82's explicit indexed Gram quadratic identity are analytic statements not yet fully encoded in the new Lean file. This batch does not promote any OPEN physical claim. The 12 IDs are not all new discoveries and do not represent full equation-level physical closure.

## Latest coverage expansion

### CORR2 — quantified weak-intermittency closure

`meanAmplitudeReciprocalFactor_band` proves that if a relative denominator fluctuation `δ` is trapped in `[-η,η]` with `0 ≤ η < 1`, then

```text
1/(1+η) ≤ 1/(1+δ) ≤ 1/(1-η).
```

Multiplying by the nonnegative mean spectral factor `k^4/Q_eff` gives the rigorous enclosure corresponding to the mean-amplitude closure. `meanAmplitudeReciprocal_upperError_exact` proves that the upper relative error factor is exactly

```text
η/(1-η).
```

Thus the closure error vanishes as the intermittency amplitude tends to zero. This does not assert that the local denominator actually satisfies the required uniform intermittency bound; that remains a model/analysis hypothesis.

### E32 — uniform alpha-drop margin

`alphaDrop_uniform_margin_bound` proves that the corrected E28 relation plus a uniform positive margin `β ≤ -A-δ`, `δ>0`, yields `α ≤ 1-δ`. `alphaDrop_uniform_margin_lt_one` then proves the strict pointwise tail inequality `α<1`. Applying the same margin on all sufficiently large indices supplies the algebraic core of the canonical `limsup α(n)<1` statement.

### E50 — phase-coherence finiteness core

`phaseCoherenceIntegrand_bound` proves the pointwise estimate

```text
0 ≤ density / |∇θ| ≤ density / δ
```

under nonnegative density and a positive floor `|∇θ| ≥ δ > 0`. For `density=|ψ|²` and `ψ∈L²`, integration gives the stated finite coherence bound. The Lean theorem formalizes the pointwise inequality; measurability and integration remain continuum assumptions.

### E41 and E72 — discrete retention counting

`iterated_count_retention_bound` proves that genuine nonnegative stepwise count-retention inequalities multiply through a finite sequence. `alphaFromRetentionLogSum_exponent_identity` proves the exact exponent bookkeeping connecting the retention product and E28 alpha definition. These theorems formalize the finite counting core; they do not independently establish that a physical WCT dynamics admits the required finite encoding.

### E19 — gap/mass consistency constraint

`gapCurvature_massSquared_chain` proves that a curvature-squared gap `Δω=c² C_gap σ²` inserted into the E49 mass relation gives

```text
m_eff² = C_gap (ℏ σ / c)².
```

`gapCurvature_unitCoefficient_recovers_massLawSquared` shows exact recovery of the squared E6 mass law at `C_gap=1`. This constrains the coefficient if the sectors are identified; it does not derive the spectral gap law itself.

### E22 — complex metric reality constraint

`complexMetricDerivativeEntry_hermitian` proves the raw complex derivative entry is Hermitian under index exchange. `complexMetricDerivativeEntry_not_symmetric_example` gives a concrete complex derivative pair for which the raw entries are not symmetric, while `complexMetricDerivativeEntry_realPart_symmetric` proves taking the real part restores symmetry. Nondegeneracy and Lorentzian signature remain separate obligations.

### TOP7 — curvature-energy diagnostic

`planarConstantCurvatureMass_squared` proves that in the torsion-free constant-curvature reduction,

```text
m² = (ℏ/c)² ε_κ
```

when `ε_κ=κ²`. This is a kernel-checked constraint showing that the canonical mass law naturally gives a squared-mass relation in that sector, not by itself a universal linear `m ∝ ε_κ` relation.

### CLE5 and CLE8 — flat-product torus selection

`flatProductTorusEigenvalue_nonnegative` proves nonnegativity of the integer Fourier-mode eigenvalue encoded as the sum of squared radius-scaled mode labels. For fixed winding/chirality `n = +1`, `flatProductTorus_fixedWinding_one_minimal` proves that the `m = 0` mode minimizes the flat-product eigenvalue, and `flatProductTorus_fixedWinding_one_eq_iff` proves that for nonzero major radius equality occurs only at integer `m = 0`.

These are exact statements for the flat-product torus spectrum. They do not prove that the full curved torus has the same spectrum without approximation, nor do they derive the physical winding/selection rule.

### TOP3 — exact negative-gradient-flow descent

`finiteGradientFlowEnergyRate_nonpositive` proves that the finite-dimensional exact negative-gradient-flow rate `-Σᵢ gᵢ²` is nonpositive. This is the algebraic core of the continuum identity `dE/dt = -||δE/δγ||² ≤ 0` under the differentiability and regularity hypotheses.

It does not establish well-posedness of the topology dynamics or differentiability of a singular self-avoidance functional.

### E16 — linearized spectral selection

`linearModePower_nonnegative` proves that nonnegative initial mode power stays nonnegative in the supplied exponential-growth model. `linearModePower_selects_larger_growth` proves that, for equal positive initial power and positive time, the mode with the larger supplied growth rate has strictly larger linearized power.

This is a linearized mode-selection theorem, not a proof of nonlinear global pattern selection.

### E37 and E38 — resource-scale algebra

`energyBandlimit_nonnegative` proves nonnegativity of the encoded energy-limited wavenumber scale under nonnegative coefficient/energy and positive `hbar,c`. `channelCapacityUpperBound_nonnegative` proves nonnegativity of the scalar channel-capacity upper-bound expression under nonnegative factors.

These results validate the encoded scalar structure; they do not derive the physical constants or prove the full computational-complexity interpretation.

### CM11 — Gaussian damping envelope

`curvatureDampingEnvelope_positive` proves strict positivity of the Gaussian envelope, while `curvatureDampingEnvelope_zero` proves exact zero-wavenumber normalization.

### CLE4, CLE9, and CLE10 — curvature-lock algebra

`curvatureLock_iff_lockedEigenEquation` proves, away from field zeros, equivalence between the scalar curvature quotient and the locked eigen-equation. `curvatureRadius_mul_curvature` proves the reciprocal radius identity for nonzero curvature. `curvatureScalarSq_iff_lockedEigenEquation` proves the corresponding squared-curvature eigen-equation equivalence.

These are scalar algebraic closures and do not prove existence or uniqueness of a toroidal electron solution.

## Earlier non-shallow mappings

### M4 — dimensional threshold

`h2Subcritical_iff_le_three` proves the integer arithmetic equivalence

```text
n < 4  ↔  n ≤ 3
```

while `SobolevCurvatureContract` keeps the actual embedding and curvature-boundedness obligations explicit.

### M5 and E36 — bounded averaged dynamics

`averagedUpdate_norm_le` proves norm nonincrease for convex mixing with a norm-nonexpansive local average. `averagedUpdate_preserves_normBound` proves forward invariance of the encoded bounded resource ball. `averagedUpdate_fixed_of_average_fixed` proves preservation of fixed points.

These are finite-dimensional update theorems, not complexity-class equivalences.

### M6B — nonlinear curvature operator

`thetaComplex_canonical_formula` proves that the typed complex operator is exactly

```text
(-Δψ · conjugate ψ) / (|ψ|² + ε² exp(-2 α |ψ|²))
```

after reassociation. `thetaComplex_denominator_ne_zero` supplies the positive-`ε` denominator condition.

This does not prove uniqueness of the nonlinear closure or PDE well-posedness.

### E10 and E11 — quantization closure

`radialShellQuantized_add` and `windingQuantized_add` prove closure under addition of phase integrals and integer indices. `radialShellQuantized_iff_windingQuantized` proves that the two predicates implement the same integer quantization law once the observable is fixed.

### E29 — entropy-pruning bound

Lean proves:

```text
0 ≤ K exp(-ΔH)
ΔH ≥ 0  →  K exp(-ΔH) ≤ K
ΔH₁ ≤ ΔH₂  →  K exp(-ΔH₂) ≤ K exp(-ΔH₁)
```

for nonnegative mode count `K`.

### G1 — bounded log-periodic ghost mode

`abs_ghostMode_le` proves that the modulation magnitude is bounded by the absolute amplitude.

### EX, EY, EZ, and FA — logarithmic-flow bridge

`exp_logField_eq` proves inversion of the logarithmic field on the positive sector. `coleHopf_residual_factorization` and `diffusionResidual_zero_iff_logCurvatureResidual_zero` prove the exact algebraic residual bridge under displayed temporal and Laplacian chain-rule hypotheses. `filamentLocalizationCondition_iff_mismatch_zero` characterizes localization as zero scalar mismatch.

These results do not supply the missing function-space chain rule or PDE regularity theorem.

## Layer 3 — Registry-only coverage: 50 IDs (this branch, subject to CI)

The remaining 50 IDs compile with family and status metadata but do not yet have a maintained equation-specific typed declaration that captures substantive mathematical content.

Registry-only does **not** mean false. It means the object is inventoried and classified, but its formula or claim has not yet been represented beyond metadata in the maintained Lean library.

## Major compiled modules

| Module | Principal coverage |
|---|---|
| `WCTLean/Registry.lean` | all 142 IDs, families, effective statuses, completeness proofs |
| `WCTLean/Models/ComplexCurvature.lean` | M2, M6B, E17 corrected complex quotient and denominator safety |
| `WCTLean/Models/Locking.lean` | M1, E3, E4, E8 finite locking algebra |
| `WCTLean/Models/BandPass.lean` | M3, M7, E12, E57, E61, E64 finite-band algebra |
| `WCTLean/Models/PhaseFlux.lean` | E9, E10, E11 phase flux and additive quantization closure |
| `WCTLean/Models/AlgebraicChecks.lean` | E20, E28, E29, E33, E45, E47, E49, E51, E53, E59, E62, E81 |
| `WCTLean/Models/CoverageExpansion.lean` | E16, E32, E37, E38, E50, CLE4, CLE5, CLE8, CLE9, CLE10, CM11, TOP3, CORR2 theorem-level support |
| `WCTLean/Models/NarrowCanonicalCoverage.lean` | E15, CLE6, CLE7 reduced scalar-mode identities and periodic angular examples |
| `WCTLean/Models/RegistryOnlyClosures.lean` | TOP6, CM3, CM4, CM10, CM15, CM20, E44, E60, E82 narrow mathematical results; see [proof scope](docs/REGISTRY_ONLY_CLOSURES_2026-10-30.md) |
| `WCTLean/Models/DerivedConstraints.lean` | E19, E22, E41, E72, TOP7 cross-equation and counting constraints |
| `WCTLean/Models/CompactDynamics.lean` | M5, E36 fixed points, norm nonincrease, bounded-set invariance |
| `WCTLean/Models/LogFlow.lean` | EX, EY, EZ, FA logarithmic and diffusion residual bridge |
| `WCTLean/Models/GhostModes.lean` | G1 bounded ghost-mode modulation and smearing definitions |
| `WCTLean/Contracts/Analytic.lean` | M4, E24–E27, E65–E70 analytic boundaries/contracts |
| `WCTLean/DerivedAudit.lean` | E5, E9, E13/E14, E18, E58, CM9, CM12, CM13, CM16 |
| `WCTLean/ResolvedAudit.lean` | E2, E3, E9, historical E17 counterexample |
| `WCTLean/Models/KoideDerivation.lean` | spin-dependent Koide algebra outside the canonical-ID count |
| `WCTLean/Models/Collider.lean` | collider log-coordinate and winding definitions |

## Status discipline

| Label | Meaning |
|---|---|
| `PROVED` | Lean accepts a theorem under its displayed hypotheses |
| `COUNTEREXAMPLE` | Lean proves a concrete failure of an unrestricted or historical claim |
| `CONDITIONAL` | named assumptions are required |
| `DEFINITION` | an object is introduced but no substantive property is proved |
| `CONTRACT` | an analytical requirement is represented explicitly as a hypothesis-bearing interface |
| `REGISTRY-ONLY` | ID, family, and status compile, but no equation-specific typed support is maintained |
| `TODO` / `OPEN` | no completed theorem closes the obligation |

A SymPy `PASS` must never be reported as a Lean proof. A Lean theorem must never be reported as empirical validation.

## Reproducibility

CI runs:

```bash
lake update
lake exe cache get
python scripts/audit_formal_sources.py
lake build
```

The audit rejects `sorry` and `admit`, verifies the public import closure, hashes every Lean source file, and confirms the pinned dependency graph remains unchanged.

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

## Phase VII dependency boundary

The six fully instantiated Phase VII arithmetic/threshold lemmas and five
conditional bridge lemmas are enumerated in THEOREMS.md. The new module does
not change D4Binding.lean, add axioms, or provide an opaque continuum instance.
The direct-cap constructor discharges the scalar amplitude-ratio premise.
Concrete Sobolev/Fourier integration, change of variables, adjusted minimizing
sequences, Brezis–Lieb/Rellich, and global H² evolution remain formalization
obligations. Conventional mathematical proofs of these model-specific steps
are in docs/D4_PHASE_VII_ANALYSIS.md. A checked implication and its conventional
analytic instantiation have different verification status.


## 2026-11-10 corrected S004 coverage boundary: #17, #18, #19

**Maintained-source path:** `WCTLean/Main.lean` imports
`UniformCurvatureDenominator`, `CorrectedWeightCalculus`,
`CorrectedWeightDirection`, `S004JetVariation`,
`S004TwoComponentVariation`, `S004AmplitudeAnnulus`,
`S004PrincipalDegeneracy`, and `S004IntegratedVariation`.

**Verified theorem types, with exact logical scope:**

- **Pointwise exact:** nonlinear denominator floor; exact radial and
  two-real-component derivative of \(F(|\psi|^2)\); full declared local
  higher-order jet-density directional derivative. These theorems have
  mathematical statements derived from the corrected equations, not
  assumed symbolic slopes.
- **Amplitude-sector exact:** coefficient lower bound on
  \(0<\delta\le |\psi|^2\le M\), counterexamples to a global positive
  lower bound near zero and at large amplitude, almost-everywhere lifting
  to complex fields and curvature energy densities.
- **Integrated first variation, explicit analytic hypotheses:**
  `S004IntegratedVariation.integratedDensity_hasDerivAt_of_dominated`
  derives the Gâteaux derivative of the *actual integral* of the
  specified corrected S004 local jet density from Mathlib differentiation
  under the integral. Its analytic assumptions include an integrable
  a.e. local Lipschitz majorant and measurability; it does **not**
  separately construct an admissible Sobolev class satisfying them.
- **Missing:** actual full spacetime complex tensor action with all spatial
  gradients; variable-coefficient high-order integration by parts and
  boundary traces; final Euler-Lagrange operator/evolution equivalence;
  nonlinear flow construction, uniqueness, continuation, global bounds,
  and any invariant nonvanishing-amplitude annulus.

The last two categories must not be collapsed: proving an integral
first variation under explicit domination is a **conditional continuum
theorem**, not automatically a full variational/PDE closure. Original
issue completion requires discharge of these function-space
hypotheses and higher-order boundary terms.


## Phase XVII full-spatial S004 continuum status

**Proved in Lean at the action-density level:** arbitrary finite
spatial dimension `d` with all gradient squares, real two-component
corrected-quotient chain rule, independent acceleration and
Laplacian jets, arbitrary differentiable potential, and the actual
integrated action's Gâteaux derivative under explicitly stated
dominated-differentiation hypotheses.

- `S004FullSpatialJet.fullLocalDensity_hasDerivAt`:
  all `Fin d` spatial gradient components, no one-direction surrogate.
- `S004FullSpatialIntegral.action_hasDerivAt_of_dominated`:
  real integral of the same density, not a finite sum or an assumed
  action derivative. Domination/integrability/measurability and the
  potential's derivative are explicit hypotheses.
- `scripts/s004_axiom_audit.lean`: direct standard-axiom verification
  for ten S004 roots; workflow collects `s004-axioms.log`.

**Not proved:** generic Sobolev sufficient conditions for the
dominated-differentiation hypotheses, nontrivial boundary/IBP
identities, complete Euler-Lagrange PDE equivalence, nonlinear
Cauchy flow existence/uniqueness or continuation, or ghost
elimination from the original covariant Hamiltonian.

**Infinite-volume obstruction:** no positive global pointwise
amplitude annulus on nonzero finite-mass whole-space H² data.
See existing kernel-verified `ReyesMath.E26.not_ae_norm_ge_of_memLp`;
annulus coercivity is a bounded/periodic/local-sector observation.


## Phase XVIII, issue #17/#18/#19: actual high-order variational bridge

The branch now includes:
- `S004EulerCoefficients.lean`: exact field, time, gradient,
  acceleration and Laplacian first-variation coefficients for the
  original corrected **two-real-component** S004 local density.
  Zero-order force contains the true nonlinear curvature radial slope.
- `S004IntervalGreen.lean`: four **genuine** real interval-integral
  Green identities (zero temporal test traces and matching periodic
  spatial traces), including second-order integration by parts.
- `S004CompatibleFields.lean`: field-to-jet compatibility for a
  *single* varied underlying field, with accelerations and Laplacians
  built from iterated declared first-order linear operators. The
  integrated action derivative is derived under genuine analytic
  domination hypotheses, not postulated. Realization as specific
  periodic Sobolev derivatives is OPEN.
- `S004TemporalEuler.lean`: temporal strong-Euler contributions for
  both real components using actual nonlinear S004 momenta and
  verified Green identities.
- `S004SpatialEuler.lean`: one-dimensional periodic spatial
  strong-Euler contributions for both real components, retaining
  the corrected nonlinear Laplacian momentum.
- Strict 26-root S004 `#print axioms` audit and fail-closed checker.

**Unresolved:** actual d-dimensional spacetime Fubini and integration
of those directional identities into one weak Euler–Lagrange theorem,
concrete Sobolev mapping and domination estimates, strong PDE
correspondence, full nonlinear constraint analysis, flow
existence/uniqueness and continuation. No nonzero finite-mass
whole-space L² field can satisfy a strictly positive global amplitude
floor, so fixed-annulus coercivity requires a bounded/periodic/local
domain interpretation.

Prior historical S004 local-jet and integral proofs retain their
earlier exact scopes; a compiled partial result must not be reported
as complete PDE formalization.


## 2026-11-10 Phase XIX, continuum gap narrowed

The full real-two-component corrected S004 local and integrated
variations are connected, through genuine Mathlib interval-Fubini
and FTC Green identities, to an **actual 1+1 dimensional**
time-periodic-space weak-to-strong Euler integral for each component.

Concrete theorem roots:
- `S004SpacetimeFubini.continuous_rectangle_integrable`:
  continuity on a finite compact time/space rectangle suffices for
  actual product Lebesgue integrability; it is not an abstract
  integrability contract.
- `S004SpacetimeGreen.temporal_second_spacetime` and
  `spatial_second_spacetime`: real 2D continuum
  second-derivative IBP with correct temporal-zero and
  spatial-periodic trace hypotheses, and Fubini where required.
- `S004SpacetimeEuler.weakComponent_eq_strongComponent`:
  all five actual momentum families assembled in one
  1+1 weak-to-strong identity.
- `S004SpacetimeEuler.fullLocalDirection_eq_component_sum` and
  `integrated_fullLocalDirection_component_split`: two
  weak component densities recombine exactly into the original
  corrected S004 Gâteaux action derivative, also after true
  Lebesgue integration.

**Mathematical boundary:** the current weak component is a sum of
five genuine iterated integrals. A full *single-integral*
weak Euler identity for the action additionally needs rigorously
integrable termwise linearity on the spacetime measure; a
distributional fundamental lemma and Sobolev trace/mapping
regularity; extension to multidimensional spatial tori; and
the actual PDE weak-to-strong equivalence. Do not treat these
as completed simply because the component identity compiles.
The original three target issues remain open.
