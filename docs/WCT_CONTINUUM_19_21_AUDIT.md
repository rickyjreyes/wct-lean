# Continuum issues #19–#21: theorem-level verification ledger

Source baseline: `wct-lean` main `1b281271caf84495b41ad93e775b9570db626302`.
Reused formal source: `math` SHA `afa8c27db10e9eff54f4dbb3e8e2d9530d042542`, package root `lean/`.
Toolchain and Mathlib: 4.23.0.

## Model separation

**Independent CQ:** `H²(ℝ²;ℂ)` is the weak/Schwartz-closure space
`ReyesMath.Sobolev.H2 2`. `M`, `energy` and `Imin` are the imported
genuine mass, fourth-order Hamiltonian and mass-constrained infimum. WCT Lean's
`mass`, `energy` and `constrainedInfimum` abbreviations are definitionally
identical, so no approximation or unstated equivalence is introduced.

**Corrected WCT:** `WCTLean.thetaComplex` is
`-lapPsi * conj(psi) / (|psi|² + ε² exp(-2α|psi|²))`. Positive denominator
does not prove quasilinear PDE existence, conservation, or coercivity.

**Periodic D4:** The root of `(Δ+1)²u − β|u|²u + γ|u|⁴u` on the 42-periodic
two-torus is not identified with a translated ℝ² minimizer. D4 denotes square
symmetry, not spatial dimension four.

## Exact frozen values

`β=γ=4608178181141995/1125899906842624`,
`m=1432536998431173/562949953421312`, `k=1`.
`ReyesMath.StrictBinding.frozen_parameters` establishes
`m < mB β β 1`; this is a **sufficient whole-space binding criterion**.

## Claim-to-Lean declaration map

| Issue | Model / scope | Exported declaration | Proof provenance | Status |
|---|---|---|---|---|
| #19 (independent benchmark) | Continuous dependence for general complex H² data and all-time conservation | `WCTLean.Continuum.independent_continuous_dependence`, `WCTLean.Continuum.independent_conservation` | imported `ReyesMath.OrbitalStability.global_flow` | Check CI |
| #21 (independent benchmark) | Frozen-parameter whole-space global flow and conservation | `WCTLean.Continuum.frozen_independent_global_flow`, `WCTLean.Continuum.frozen_independent_conservation` | exact rational coefficient instantiation | Check CI |
| #19 | Corrected M2/E17 quotient nodal vanishing and no globally positive coefficient floor | `WCTLean.Continuum.corrected_curvature_vanishes_at_field_node`, `WCTLean.Continuum.no_positive_uniform_quotient_coefficient_lower_bound` | direct corrected-model proof, no PDE well-posedness claim | Check CI |
| #20 (positive corrected curvature candidate) | Exact whole-plane zero infimum, nonattainment and local constrained no-minimizer on complex H² | `WCTLean.Continuum.canonical_positive_energy_infimum_zero`, `WCTLean.Continuum.canonical_positive_energy_nonattainment`, `WCTLean.Continuum.canonical_positive_energy_no_local_minimizer` | `ReyesMath.Curvature.global_nonattainment` and `.no_local_minimizer` with c₁=c₂=1 and d=2 | Check CI |
| #20 | Definitional weak H² model agreement | `WCTLean.Continuum.model_correspondence` | direct definitional proof | Check CI |
| #20 | Whole-plane prescribed mass and minimizer | `WCTLean.Continuum.exists_free_space_minimizer` | `ReyesMath.WholeSpace.exists_minimizer` | Check CI |
| #20 | Existence of a nonzero L² field | `WCTLean.Continuum.exists_nonzero_minimizer` | minimizer + positive mass | Check CI |
| #20 | Strong H² subsequential compactness modulo translations | `WCTLean.Continuum.free_space_minimizing_sequences_compact` | `ReyesMath.WholeSpace.compactness` | Check CI |
| #20 | Exact symmetry invariance of mass and energy | `WCTLean.Continuum.free_space_translation_invariant` | `H2.M_translate`, `H2.energy_translate` | Check CI |
| #20 | Exact frozen mass threshold and existence | `WCTLean.Continuum.frozen_whole_plane_existence` | `StrictBinding.frozen_parameters` + attainment | Check CI |
| #19 (separate model) | Global complex CQ H² evolution | `WCTLean.Continuum.independent_global_flow` | `ReyesMath.OrbitalStability.global_flow` | Check CI |
| #21 | Arbitrary-complex pointwise cubic/quintic expansion and exact first-order terms | `WCTLean.Continuum.cubic_exact_expansion`, `WCTLean.Continuum.quintic_exact_expansion`, `WCTLean.Continuum.cubicQuinticPotential_eq` | polynomial identities, no spectrum claim | Check CI |
| #21 (separate model) | Full-set CQ orbital stability | `WCTLean.Continuum.independent_orbital_stability` | `ReyesMath.OrbitalStability.orbital_stability` | Check CI |
| #21 (separate model) | Frozen-parameter CQ whole-plane stability | `WCTLean.Continuum.frozen_whole_plane_orbital_stability` | threshold + global CQ orbit theorem | Check CI |

## Acceptance verdicts

- **#19 PARTIAL.** Proved: uniform `R_ε` bound; global Lipschitz bound for
  `R_ε`; `N_curv : H²(ℝ²) → L²` with mapping and local Lipschitz estimates;
  multiplier-level `t^{−1/2}` smoothing of the linear M7 symbol; uniform
  parabolicity of the M7 frozen principal symbol; CM1 frozen-coefficient
  Hadamard obstruction in both time orientations. Missing: the operator-level
  damped semigroup on `H²`, the Duhamel fixed point (M7 existence,
  uniqueness, continuous dependence, continuation), and nonlinear CM1
  ill-posedness.
- **#20 PARTIAL.** Proved for the independent CQ model: existence, compactness,
  single-state tails, uniform tightness, all-time dynamical localization, and
  the constrained Euler–Lagrange equation with explicit multiplier. Proved
  obstruction for the positive corrected-curvature energy (infimum zero, not
  attained). Missing: elliptic regularity beyond `H²`, decay rates, symmetry/
  positivity analysis, and any canonical-model confinement mechanism.
- **#21 PARTIAL.** Proved: abstract radii-polynomial theorem; exact parameter
  identity with the certificate; kernel-checked infinite high-mode diagonal
  bound `d_k ≥ 79`; certificate scalar inequalities. Externally replayed:
  the full Arb certificate. Missing in Lean: `Y0`, `Z0`, `L` (computational
  obstruction above), the torus Wiener space and bordered map as Lean
  objects, `L±` constrained coercivity and periodic orbital stability.

## Integrity and required final verification

Run `lake update`, `lake exe cache get`, `lake build` from repository root.
Run `lake build WCTLean.Continuum.CubicQuinticWholeSpace`, source audit,
`#print axioms` and the CI workflows at the exact PR head.
No statuses in this report imply local build or GitHub CI passed before
those runs finish. Do not merge or close any issues from this ledger alone.

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

### Exact real/imaginary Hessian-potential split

`WCTLean.Continuum.cubicQuinticFirstOrder_real_blocks` proves that at an
arbitrary *real-valued profile amplitude* a, and for **every complex**
perturbation h, the pointwise first-order cubic–quintic potential has
coefficients `-3βa²+5γa⁴` on the real sector and
`-βa²+γa⁴` on the imaginary sector. This recovers the exact polynomial
contributions to the periodic `Lplus` and `Lminus` operators, with
no radial or D4 perturbation restriction. Domain/self-adjointness,
stationary-root substitution and spectrum remain separate Lean obligations.

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

## 2026-10-31 second continuation: Euler–Lagrange, M7 nonlinear estimates, D4 certificate components

All declarations below print only `[propext, Classical.choice, Quot.sound]`.

### #20 — constrained Euler–Lagrange equation (`CubicQuinticEulerLagrange.lean`)

| Declaration | Exact statement |
|---|---|
| `Esp_taylor` | `E(w) − E(u) ≤ 2·elForm(u, w−u) + C_R‖w−u‖²_{H²}` on `H²` balls (kinetic part exact, potential via pinned `Nsp_taylor`) |
| `elForm_eq_zero_of_tangent` | a mass-constrained minimizer over `H²` has zero first variation in every `L²`-tangent direction |
| `euler_lagrange_of_constrained_min` | `elForm(u,h) = (elForm(u,u)/m)·Re⟨u,h⟩` for all `h ∈ H²` |
| `minimizer_euler_lagrange` | every `U ∈ 𝒢_m` (`γ>0`, `m>0`) satisfies `Re⟨(Δ+k²)U,(Δ+k²)h⟩ + Re⟨F(U),h⟩ = ω Re⟨U,h⟩` for all complex `h ∈ H²`, with `ω m = ‖(Δ+k²)U‖² + Re⟨F(U),U⟩` |
| `frozen_minimizer_euler_lagrange` | the same at the exact frozen parameters |

This is the weak form of `(Δ+k²)²U − β|U|²U + γ|U|⁴U = ωU`: minimizers are
standing waves of the whole-plane CQ flow. **Not proved:** regularity beyond
`H²` (elliptic bootstrap), pointwise/polynomial/exponential decay, symmetry or
positivity of minimizers, and any corrected-curvature confinement.

### #19 — M7 nonlinear estimates (`M7CurvatureNonlinearity.lean`)

| Declaration | Exact statement |
|---|---|
| `denom_ge_floor`, `abs_exp_sub_exp_le_of_nonpos`, `denom_sub_le` | `D_ε ≥ min(1, ε²e^{−2α})`; exponential and denominator increments |
| `reciprocal_lipschitz` | `R_ε` globally Lipschitz on ℂ with `L_ε = 1/δ + (1+2αε²)(B² + 1/δ)` |
| `memLp_curvField`, `curvOp`, `norm_curvOp_le` | `N_curv[ψ] = −(Δψ)R_ε(ψ) ∈ L²` for every `ψ ∈ H²(ℝ²)`, `‖N_curv[ψ]‖ ≤ B‖Δψ‖` |
| `curvOp_lipschitz` | `‖N_curv[ψ]−N_curv[φ]‖² ≤ 2B²‖Δψ−Δφ‖² + 2L_ε²‖ψ−φ‖²_{H²}‖Δφ‖²` |
| `m7_multiplier_smoothing` | `(1+q)e^{tℓ(q)} ≤ e^{tC}(1 + (c₂t)^{−1/2})` for the linear M7 symbol `ℓ`, all `q ≥ 0`, `t > 0` |

These are the nonlinear mapping/Lipschitz estimates and the multiplier-level
smoothing rate of a Duhamel formulation of M7. **Not proved:** the damped
semigroup as an operator on `H²` (only its symbol bound), the Duhamel fixed
point, hence no M7 local existence/uniqueness/continuous dependence or
continuation theorem. The pinned unitary-group machinery of
`ReyesMath.Sobolev.CubicQuinticFlow` cannot be reused: it relies on a
loss-free `H² → H²` nonlinearity and an invertible group, whereas
`N_curv` loses two derivatives and `e^{−c₂t(Δ+k²)²}` is a non-invertible
smoothing semigroup. CM1 remains at the frozen-coefficient obstruction level.

### #21 — certificate components (`D4CertificateInterface.lean`)

| Declaration | Status |
|---|---|
| `cert_beta_eq_frozen`, `cert_mass_eq_frozen` | kernel-checked: certificate binary64 `β=γ` and mass are exactly `frozenBeta`, `frozenMass` |
| `d4_high_mode_diagonal_ge`, `d4_high_mode_inverse_le` | kernel-checked: `d_k ≥ 79` and `0 < 1/d_k ≤ 1/79` for **every** mode with `max(|k₁|,|k₂|) ≥ 21` (rigorous `π > 3.141592`) |
| `d4_cert_scalar_conditions` | kernel-checked arithmetic for the reported outward upper bounds |
| `d4_conditional_existence` | **conditional** on the external Arb bounds `Y0`, `Z0`, `L`; not a verified certificate |

Independent replay (this session): `tools/closure_d4_wiener_certificate.py --cutoff 20`
at `wct-pde` `e9a2b589` with python-flint 0.9.0 reproduces the receipt
exactly (PASS; identical `Y0`, `Z0`, `high_diagonal_lower`, all three radii;
candidate SHA-256 `9fcf8e32…`), and `tests/test_d4_wiener_certificate.py`
passes (4/4). This is external interval-arithmetic validation, not Lean.

**Computational obstruction to a kernel-only certificate:** `Y0` requires an
exact quintic convolution of a half-width-70 dyadic candidate (≈10⁹
128-bit multiplications); `Z0` requires `‖I − B J_LL‖₁` for a dense 232×232
Arb-midpoint matrix (≈10⁷ operations) and convolution column sums. These
exceed Lean kernel reduction; `native_decide` would add `Lean.ofReduceBool`,
which this project excludes. Constrained coercivity of `L±` on the complex
torus space and periodic orbital stability are not formalized.
