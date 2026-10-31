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

## Layer 2 — Non-registry typed Lean support: 80 IDs

The following IDs have a maintained equation-specific definition, proposition, theorem, counterexample, analytic contract, or kernel-checked constraint beyond registry metadata:

```text
M1 M2 M3 M4 M5 M6A M6B M7
E1A E1B E2 E3 E4 E5 E6 E7 E8 E9 E10 E11
E12 E13 E14 E16 E17 E18 E19 E20 E22
E24 E25 E26 E27 E28 E29 E32 E33 E36 E37 E38 E41
E45 E47 E49 E50 E51 E53
E57 E58 E59 E61 E62 E64
E65 E66 E67 E68 E69 E70 E72
E78 E81
CLE4 CLE5 CLE8 CLE9 CLE10
G1 EX EY EZ FA
CM9 CM11 CM12 CM13 CM16
TOP3 TOP7
CORR2
```

The branch's kernel-checked coverage expansion adds eighteen IDs relative to the original 62-ID baseline:

```text
E16 E19 E22 E32 E37 E38 E41 E50 E72
CLE4 CLE5 CLE8 CLE9 CLE10
CM11 TOP3 TOP7 CORR2
```

Some of these are exact conditional constraints rather than proofs of the full physical claim. They count as equation-specific formal support because the theorem itself is kernel-checked; they do **not** change the scientific status of the associated canonical claim unless a separate symbolic or analytic audit justifies that change.

### Direct algebraic, order-theoretic, counting, or finite-dynamical theorem support

```text
M1 M2 M3 M4 M5 M6B M7
E2 E3 E4 E5 E8 E9 E10 E11
E12 E13 E14 E16 E17 E18 E19 E20 E22 E28 E29 E32 E33 E36 E37 E38 E41
E45 E47 E49 E50 E51 E53
E57 E58 E59 E61 E62 E64 E72 E81
CLE4 CLE5 CLE8 CLE9 CLE10
G1 EX EY EZ FA
CM9 CM11
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

## Layer 3 — Registry-only coverage: 62 IDs

The remaining 62 IDs compile with family and status metadata but do not yet have a maintained equation-specific typed declaration that captures substantive mathematical content.

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

## Continuum issues #19–#21 (independent CQ model bridge)

The pinned `reyes_math` imports and concrete whole-space weak-Sobolev bridge
live in `WCTLean/Continuum/CubicQuinticWholeSpace.lean`. The model is the
**independent** cubic–quintic Hamiltonian on ℝ², not the canonical corrected
curvature PDE and not the periodic torus D4 root. See
`docs/WCT_CONTINUUM_19_21_AUDIT.md` for theorem mapping and remaining
acceptance obligations. Issues #19, #20, and #21 are not closed.

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

### Free-space L² mass-tail localization (#20)

`WCTLean/Continuum/FreeSpaceMassTails.lean` proves the continuum
integral statement `∫_{|x|>n} |u(x)|² → 0` as n→∞ for every
`H²(ℝ²;ℂ)` state, the resulting finite-radius epsilon criterion,
and an energy-attaining whole-space CQ minimizer satisfying that
criterion. The argument uses `H2.integrable_sq_val` and Mathlib's
antitone set-integral convergence theorem. It assumes no symmetry
or box boundary.

**Interpretation:** This is L² mass-tail localization, which every
finite-mass state satisfies. It is **not** an exponential/pointwise
tail estimate and does **not alone** establish a physical trapping
mechanism or canonical WCT confinement. All added declarations
remain pending exact-head CI until verified.

## 2026-10-31 continuation: new kernel-checked mathematics

Phase 0 repair: `cubicTerm_eq_normSq`/`quinticTerm_eq_normSq` now close via
`Complex.mul_conj` (the earlier residual cast goal made
`cubicQuinticPotential_eq` depend on `sorryAx`), and `FreeSpaceMassTails`
uses `Metric.isClosed_closedBall`. Full `lake build` (7280+ jobs), every
focused continuum module, `scripts/audit_formal_sources.py` and the locked
dependency diff pass locally; all continuum declarations print only
`[propext, Classical.choice, Quot.sound]`.

### #19 — canonical evolutions: frozen principal-symbol dichotomy
(`WCTLean/Continuum/CurvatureEvolutionSymbol.lean`)

The registry (`geometry_of_resonance`, `WCT_FULL_EQUATION_LIST_CORRECTED.md`)
contains two different curvature evolutions. They are kept distinct:

| Declaration | Exact statement |
|---|---|
| `complexRegularizedReciprocal_uniform_bound` | `‖R_ε(ψ)‖ ≤ 1 + (ε² e^{-2α})^{-2}` for all `ψ ∈ ℂ`, `ε>0`, `α≥0` (via `‖R_ε(ψ)‖² = positiveCurvatureWeight ε α |ψ|²` and pinned `ReyesMath.positive_curvature_weight_uniform_bound`) |
| `m7_principal_symbol_uniformly_parabolic` | M7 frozen principal symbol `p(q)=c₁(σ²−q)−c₂(k⋆²−q)²+q R_ε(ψ₀)` satisfies `Re p(q) ≤ C − (c₂/2)q²`, `C` explicit and independent of the background `ψ₀` |
| `m7_principal_symbol_high_frequency_damping` | for every `Λ` there is `Q` with `Re p(q) ≤ −Λ` for all `q ≥ Q` and all backgrounds |
| `cm1Rhs_quadratic_in_laplacian`, `cm1Rhs_laplacian_expansion` | CM1 `−Θ_ε[ψ]J[ψ] = ε_vac|ψ|²R_ε(ψ)(Δψ)²`; exact expansion in the second-order slot with principal coefficient `κ = 2ε_vac|a|²R_ε(a)b` |
| `cm1_principal_coefficient_harmonic`, `cm1_principal_coefficient_node` | `κ = 0` at harmonic backgrounds (`Δψ₀ = 0`) and at nodes |
| `cm1_principal_coefficient_im` | `Im κ = 2ε_vac|a|² Im(ā b)/D_ε(a)` |
| `frozen_mode_unbounded_growth` | `Im κ < 0` ⇒ frozen-mode amplification `exp(−Im κ · q t)` is unbounded over `q` for every `t>0` |
| `cm1_frozen_hadamard_obstruction` | for every `ε>0`, `α`, `ε_vac ≠ 0`: backgrounds exist with unbounded forward-time growth **and** others with unbounded backward-time growth |

Interpretation. M7 (the equation with explicit `−c₂(Δ+k⋆²)²`, `c₂>0`) passes
the frozen-coefficient necessary condition uniformly: the bounded curvature
quotient is a lower-order perturbation of fourth-order parabolic damping.
CM1 fails it: its linearization is degenerate at harmonic backgrounds and
backward-parabolic on an explicit open set of backgrounds, for either sign
of `ε_vac` and either time orientation. **Not proved:** the nonlinear M7
Duhamel fixed point in `C([0,T];H^s)`, continuation criterion, or a
nonlinear CM1 ill-posedness theorem. M7's `c₄R^{-(2+n/p)}ψ` and
`ηψ∘ξ(t)` terms are not specified precisely enough to include.

### #20 — uniform and dynamical free-space localization
(`WCTLean/Continuum/FreeSpacePersistentLocalization.lean`)

| Declaration | Exact statement |
|---|---|
| `massTail_perturb` | `tail_R(v) ≤ 2 tail_R(u) + 2‖v−u‖²_{L²}` |
| `minimizer_set_uniformly_tight` | for every `η>0` one radius `R` works for **every** constrained CQ minimizer after translation: `∀ U ∈ Gset, ∃ y, tail_R(U(·+y)) < η` (proved by contradiction from translated compactness + single-state tails) |
| `orbitally_stable_persistent_localization` | `∃ δ>0, ∃ R`: every whole-plane solution with `distX(u(0), Gset) < δ` has, at **every** real time `t`, a center `y(t)` with `tail_R(u(t)(·+y(t))) < η` |
| `frozen_persistent_localization` | the same at the exact rational frozen parameters |

No box, boundary, potential, radial or D4 restriction is used, and the initial
perturbation may change the mass. This is genuine boundary-independent,
energy-driven dynamical confinement **for the independent CQ model**.
**Not proved:** pointwise/exponential decay, the Euler–Lagrange equation and
regularity of minimizers, and any transfer to the corrected-curvature
energy (whose positive-energy constrained infimum is not attained).

### #21 — a posteriori contraction theorem
(`WCTLean/Continuum/RadiiPolynomial.lean`)

| Declaration | Exact statement |
|---|---|
| `radii_displacement_bound` | `‖DT(x)‖ ≤ Z0 + L‖x−x̄‖` on the ball ⇒ `‖T x − T x̄‖ ≤ Z0ρ + (L/2)ρ²`, `ρ = ‖x−x̄‖` |
| `radii_polynomial_unique_fixed_point` | on any real Banach space: `‖T x̄ − x̄‖ ≤ Y0`, `Y0 + Z0 r + (L/2) r² ≤ r`, `Z0 + L r < 1` ⇒ exactly one fixed point in `closedBall x̄ r` |
| `radii_polynomial_unique_zero` | Newton map `T x = x − A F(x)`, `A` injective ⇒ exactly one zero of `F` in the ball |

This is the abstract analytical theorem only. **Not proved in Lean:** the
42-torus Fourier/Wiener space and bordered map, kernel-checked
`Y0, Z0, L, r` for the saved candidate, the `L±` constrained coercivity,
and the mass-penalized Lyapunov argument for the periodic root. Those
remain externally certified (`wct-pde` #24/#25, `e9a2b589`).
