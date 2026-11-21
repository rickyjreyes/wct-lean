/-
  WCTLean/Models/ContinuumObligations.lean

  Issue #28: close the continuum-analysis obligations that Mathlib already
  supports, and record the remaining ones as named, typed targets.

  Closed here (kernel-checked):

  * **Core integrability threshold (improper integral).**
    `r ↦ r^(2p-2)` is integrable on `(0, R)` iff `p > 1/2`
    (`coreIntegrability_improper_iff`), with value `R^(2p-1)/(2p-1)`
    (`coreIntegrability_integral`).  This upgrades the exponent reduction
    `coreIntegrabilityExponent_iff` of `Models/FormalUpgrades.lean`.
  * **E50 measurability and integration step.**  For an integrable
    nonnegative density and an a.e.-strongly-measurable phase-gradient
    magnitude with floor `δ > 0`, the coherence integrand is integrable and
    `∫ ρ/|∇θ| ≤ (∫ ρ)/δ` (`phaseCoherence_integral_bound`); for `ρ = |ψ|²`
    with `ψ ∈ L²` (`phaseCoherence_finite_of_memLp`).
  * **EX–FA chain rule (1+1 dimensions).**  For a positive field
    `ψ(t, x)` with genuine first time derivative and first/second space
    derivatives, the derivatives of `u = log ψ` are computed
    (`coleHopf_log_derivatives`), and the diffusion residual vanishes iff the
    logarithmic curvature residual of the *actual derivatives of* `log ψ`
    vanishes (`coleHopf_function_bridge`, `coleHopf_heat_iff_log_flow`).
    The chain-rule hypotheses of `Models/LogFlow.lean` are thereby derived,
    not assumed.

  Remaining obligations are enumerated in `ContinuumObligation` with the
  missing infrastructure stated.
-/

import Mathlib
import WCTLean.Models.FormalUpgrades
import WCTLean.Models.CoverageExpansion
import WCTLean.Models.LogFlow

namespace WCTLean

open MeasureTheory Filter Topology

noncomputable section

/-! ### Core integrability threshold -/

/-- **Improper-integral form of the core threshold.**  For `R > 0`,
`r ↦ r^(2p-2)` is integrable on `(0, R)` exactly when `p > 1/2`. -/
theorem coreIntegrability_improper_iff (p R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun r : ℝ => r ^ (2 * p - 2)) (Set.Ioo 0 R) ↔ p > 1 / 2 :=
  (intervalIntegral.integrableOn_Ioo_rpow_iff hR).trans (coreIntegrabilityExponent_iff p)

/-- Value of the core integral for `p > 1/2`:
`∫₀^R r^(2p-2) dr = R^(2p-1)/(2p-1)`. -/
theorem coreIntegrability_integral (p R : ℝ) (hp : p > 1 / 2) :
    ∫ r in (0 : ℝ)..R, r ^ (2 * p - 2) = R ^ (2 * p - 1) / (2 * p - 1) := by
  have hr : -1 < 2 * p - 2 := by linarith
  rw [integral_rpow (Or.inl hr)]
  have h1 : 2 * p - 2 + 1 = 2 * p - 1 := by ring
  rw [h1, Real.zero_rpow (by linarith : (2 * p - 1) ≠ 0), sub_zero]

/-- Below the threshold the core power law is not integrable near zero. -/
theorem coreIntegrability_not_integrable (p R : ℝ) (hR : 0 < R) (hp : p ≤ 1 / 2) :
    ¬ IntegrableOn (fun r : ℝ => r ^ (2 * p - 2)) (Set.Ioo 0 R) := by
  rw [coreIntegrability_improper_iff p R hR]
  linarith

/-! ### E50: measurability and integration -/

/-- **E50 integration step.**  An integrable nonnegative density and an
a.e.-strongly-measurable phase-gradient magnitude with a uniform floor `δ > 0`
give an integrable coherence integrand with `∫ ρ/|∇θ| ≤ (∫ ρ)/δ`. -/
theorem phaseCoherence_integral_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (ρ g : α → ℝ) {δ : ℝ} (hδ : 0 < δ) (hρ : Integrable ρ μ) (hρ0 : ∀ᵐ x ∂μ, 0 ≤ ρ x)
    (hg : AEStronglyMeasurable g μ) (hgδ : ∀ᵐ x ∂μ, δ ≤ g x) :
    Integrable (fun x => phaseCoherenceIntegrand (ρ x) (g x)) μ ∧
      ∫ x, phaseCoherenceIntegrand (ρ x) (g x) ∂μ ≤ (∫ x, ρ x ∂μ) / δ := by
  have hpt : ∀ᵐ x ∂μ, 0 ≤ phaseCoherenceIntegrand (ρ x) (g x) ∧
      phaseCoherenceIntegrand (ρ x) (g x) ≤ ρ x / δ := by
    filter_upwards [hρ0, hgδ] with x h0 h1
    exact phaseCoherenceIntegrand_bound (ρ x) (g x) δ h0 hδ h1
  have hmeas : AEStronglyMeasurable (fun x => phaseCoherenceIntegrand (ρ x) (g x)) μ := by
    unfold phaseCoherenceIntegrand
    exact (hρ.aestronglyMeasurable.aemeasurable.div hg.aemeasurable).aestronglyMeasurable
  have hint : Integrable (fun x => phaseCoherenceIntegrand (ρ x) (g x)) μ := by
    refine (hρ.div_const δ).mono' hmeas ?_
    filter_upwards [hpt] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2
  refine ⟨hint, ?_⟩
  calc ∫ x, phaseCoherenceIntegrand (ρ x) (g x) ∂μ ≤ ∫ x, ρ x / δ ∂μ :=
        integral_mono_ae hint (hρ.div_const δ) (hpt.mono fun x hx => hx.2)
    _ = (∫ x, ρ x ∂μ) / δ := integral_div δ ρ

/-- **E50 for `L²` fields.**  If `ψ ∈ L²(μ)` and the phase-gradient magnitude
has floor `δ > 0`, the coherence integral of `|ψ|²` is finite and bounded by
`‖ψ‖²_{L²}/δ`. -/
theorem phaseCoherence_finite_of_memLp {α F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup F] (ψ : α → F) (hψ : MemLp ψ 2 μ) (g : α → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hg : AEStronglyMeasurable g μ) (hgδ : ∀ᵐ x ∂μ, δ ≤ g x) :
    Integrable (fun x => phaseCoherenceIntegrand (‖ψ x‖ ^ 2) (g x)) μ ∧
      ∫ x, phaseCoherenceIntegrand (‖ψ x‖ ^ 2) (g x) ∂μ ≤ (∫ x, ‖ψ x‖ ^ 2 ∂μ) / δ :=
  phaseCoherence_integral_bound (fun x => ‖ψ x‖ ^ 2) g hδ
    ((memLp_two_iff_integrable_sq_norm hψ.1).mp hψ)
    (Eventually.of_forall fun _ => sq_nonneg _) hg hgδ

/-! ### EX–FA: Cole–Hopf chain rule from genuine derivatives -/

/-- **Derivatives of `u = log ψ`.**  For a positive field with time derivative
`ψt`, space derivative `ψx` (at every point of the slice) and second space
derivative `ψxx`, the time, space and second space derivatives of `log ψ` are
`ψt/ψ`, `ψx/ψ` and `ψxx/ψ - (ψx/ψ)²`. -/
theorem coleHopf_log_derivatives (ψ ψt ψx ψxx : ℝ → ℝ → ℝ) (t x : ℝ)
    (hpos : ∀ y, 0 < ψ t y) (hposT : 0 < ψ t x)
    (ht : HasDerivAt (fun s => ψ s x) (ψt t x) t)
    (hx : ∀ y, HasDerivAt (fun y => ψ t y) (ψx t y) y)
    (hxx : HasDerivAt (fun y => ψx t y) (ψxx t x) x) :
    deriv (fun s => Real.log (ψ s x)) t = ψt t x / ψ t x ∧
      deriv (fun y => Real.log (ψ t y)) x = ψx t x / ψ t x ∧
      deriv (fun y => deriv (fun z => Real.log (ψ t z)) y) x =
        ψxx t x / ψ t x - (ψx t x / ψ t x) ^ 2 := by
  have hd1 : ∀ y, deriv (fun z => Real.log (ψ t z)) y = ψx t y / ψ t y := fun y =>
    ((hx y).log (hpos y).ne').deriv
  refine ⟨(ht.log hposT.ne').deriv, hd1 x, ?_⟩
  have hfun : (fun y => deriv (fun z => Real.log (ψ t z)) y) = fun y => ψx t y / ψ t y :=
    funext hd1
  rw [hfun]
  have h : HasDerivAt (fun y => ψx t y / ψ t y)
      ((ψxx t x * ψ t x - ψx t x * ψx t x) / ψ t x ^ 2) x := hxx.div (hx x) (hpos x).ne'
  rw [h.deriv]
  have := (hpos x).ne'
  field_simp

/-- **Function-level Cole–Hopf bridge.**  For a positive field, the diffusion
residual `ψ_t - ψ_xx` vanishes at `(t, x)` exactly when the logarithmic
curvature residual `u_t - (u_xx + u_x²)` of the genuine derivatives of
`u = log ψ` vanishes there. -/
theorem coleHopf_function_bridge (ψ ψt ψx ψxx : ℝ → ℝ → ℝ) (t x : ℝ)
    (hpos : ∀ y, 0 < ψ t y)
    (ht : HasDerivAt (fun s => ψ s x) (ψt t x) t)
    (hx : ∀ y, HasDerivAt (fun y => ψ t y) (ψx t y) y)
    (hxx : HasDerivAt (fun y => ψx t y) (ψxx t x) x) :
    diffusionResidual (ψt t x) (ψxx t x) = 0 ↔
      logCurvatureResidual (deriv (fun s => Real.log (ψ s x)) t)
        (deriv (fun y => deriv (fun z => Real.log (ψ t z)) y) x)
        ((deriv (fun y => Real.log (ψ t y)) x) ^ 2) = 0 := by
  obtain ⟨hut, hux, huxx⟩ := coleHopf_log_derivatives ψ ψt ψx ψxx t x hpos (hpos x) ht hx hxx
  rw [hut, hux, huxx]
  have hne := (hpos x).ne'
  apply diffusionResidual_zero_iff_logCurvatureResidual_zero (ψ t x) _ _ _ _ _ hne
  · field_simp
  · field_simp
    ring

/-- **Cole–Hopf equivalence of the flows.**  A positive `C^{1,2}` field solves
the heat equation `ψ_t = ψ_xx` everywhere iff `u = log ψ` solves the
logarithmic curvature flow `u_t = u_xx + u_x²` everywhere. -/
theorem coleHopf_heat_iff_log_flow (ψ ψt ψx ψxx : ℝ → ℝ → ℝ)
    (hpos : ∀ t y, 0 < ψ t y)
    (ht : ∀ t x, HasDerivAt (fun s => ψ s x) (ψt t x) t)
    (hx : ∀ t y, HasDerivAt (fun y => ψ t y) (ψx t y) y)
    (hxx : ∀ t x, HasDerivAt (fun y => ψx t y) (ψxx t x) x) :
    (∀ t x, ψt t x = ψxx t x) ↔
      ∀ t x, deriv (fun s => Real.log (ψ s x)) t =
        deriv (fun y => deriv (fun z => Real.log (ψ t z)) y) x +
          (deriv (fun y => Real.log (ψ t y)) x) ^ 2 := by
  constructor
  · intro hheat t x
    have h := (coleHopf_function_bridge ψ ψt ψx ψxx t x (hpos t) (ht t x) (hx t) (hxx t x)).mp
      (by unfold diffusionResidual; rw [hheat t x, sub_self])
    unfold logCurvatureResidual at h
    linarith
  · intro hlog t x
    have h := (coleHopf_function_bridge ψ ψt ψx ψxx t x (hpos t) (ht t x) (hx t) (hxx t x)).mpr
      (by unfold logCurvatureResidual; rw [hlog t x, sub_self])
    unfold diffusionResidual at h
    linarith

/-! ### Inventory of the issue-#28 obligations -/

/-- The continuum obligations listed in issue #28. -/
inductive ContinuumObligation where
  /-- EX–FA function-space chain rule (closed in 1+1 dimensions:
  `coleHopf_function_bridge`, `coleHopf_heat_iff_log_flow`; the
  `n`-dimensional version needs the Laplacian via `fderiv`/`iteratedFDeriv`). -/
  | logFlowChainRule
  /-- E50 measurability and integration (closed: `phaseCoherence_integral_bound`,
  `phaseCoherence_finite_of_memLp`). -/
  | phaseCoherenceIntegration
  /-- E29: derivation of `ΔH` from the field dynamics.  Blocked: the registry
  fixes neither the entropy functional nor the dynamics that produces `ΔH`. -/
  | entropyPruningDerivation
  /-- CLE5/CLE8 curved-torus spectrum.  Blocked: Mathlib has no
  Laplace–Beltrami operator or spectral theory on surfaces of revolution. -/
  | curvedTorusSpectrum
  /-- TOP3 singular self-avoidance gradient flow.  Blocked: requires gradient
  flows of singular functionals on curve spaces (no Mathlib API). -/
  | singularGradientFlow
  /-- Core integrability threshold as an improper integral (closed:
  `coreIntegrability_improper_iff`, `coreIntegrability_integral`). -/
  | coreImproperIntegral
  /-- Thin-shell toroidal asymptotics.  Blocked: needs surface integrals of
  mean curvature on tori of revolution (Willmore energy) in Mathlib. -/
  | thinShellTorusAsymptotics
  /-- Continuum justification of finite-count / finite-encoding reductions.
  Blocked: the continuum objects behind each reduction are not specified in
  the registry. -/
  | finiteReductionJustification
  deriving DecidableEq, Repr

/-- Status of an obligation on this branch. -/
inductive ObligationStatus where
  | closed
  | blocked
  deriving DecidableEq, Repr

/-- Current status of each issue-#28 obligation. -/
def continuumObligationStatus : ContinuumObligation → ObligationStatus
  | .logFlowChainRule => .closed
  | .phaseCoherenceIntegration => .closed
  | .entropyPruningDerivation => .blocked
  | .curvedTorusSpectrum => .blocked
  | .singularGradientFlow => .blocked
  | .coreImproperIntegral => .closed
  | .thinShellTorusAsymptotics => .blocked
  | .finiteReductionJustification => .blocked

/-- Exactly three of the eight obligations are closed on this branch. -/
theorem continuumObligations_closed_count :
    ([ContinuumObligation.logFlowChainRule, .phaseCoherenceIntegration,
      .entropyPruningDerivation, .curvedTorusSpectrum, .singularGradientFlow,
      .coreImproperIntegral, .thinShellTorusAsymptotics,
      .finiteReductionJustification].filter
        (fun o => continuumObligationStatus o = .closed)).length = 3 := by
  decide

end

end WCTLean
