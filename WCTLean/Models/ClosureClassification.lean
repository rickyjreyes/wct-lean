/-
  WCTLean/Models/ClosureClassification.lean

  Issue #26 (M6B): which nonlinear curvature closures are admissible, and is
  the maintained one uniquely selected?

  This is an *operator-selection* result about pointwise jet maps
  `(ψ, Δψ) ↦ Θ`; it says nothing about uniqueness of PDE solutions.

  Admissible class (all hypotheses explicit):

  * `LaplacianHomogeneous`: `ℂ`-homogeneous in the Laplacian slot;
  * `PhaseInvariant`: invariant under a common global unit phase of
    `(ψ, Δψ)`;
  * regularized radial form `Θ = -(Δψ ψ̄) / D_ε(|ψ|²)` with a real denominator
    family `D` that is node-safe (`D_ε(s) > 0` for `s ≥ 0`, `ε > 0`), has the
    correct off-node limit (`D_ε(s) → s` as `ε → 0⁺`, `s > 0`), and is
    `UnitCovariant` (`D_{λε}(λ² s) = λ² D_ε(s)`: rescaling the field unit,
    under which `ε` carries the field's dimension, leaves `Θ` unchanged).

  Results:

  * `closure_classification`: every homogeneous, phase-invariant pointwise
    closure is a radial reweighting `-(Δψ ψ̄) g(|ψ|²)`; conversely every such
    reweighting is admissible (`radialClosure_homogeneous`,
    `radialClosure_phaseInvariant`).
  * `admissible_profile`, `admissible_profile_asymptotic`,
    `profileRegularizer_admissible`: admissible regularizers are *exactly*
    `D_ε(s) = ε² Φ(s/ε²)` with `Φ > 0` on `[0, ∞)` and `Φ(u)/u → 1`.
  * Non-uniqueness: `admissible_closures_infinite` (pairwise distinct
    admissible closures at the same `ε`).
  * `maintainedDenominator_not_unitCovariant`: the maintained regularizer
    with a fixed `α ≠ 0` is *not* unit covariant; with `α = a/ε²` it is the
    profile `u + e^{-2au}` (`maintained_scaled_eq_profile`).
  * **Uniqueness under two explicit extra principles**
    (`closure_unique_affine_normalized`): an admissible regularizer whose
    profile is affine and which is normalized at nodes (`D_ε(0) = ε²`) is
    `D_ε(s) = s + ε²`, i.e. the closure is the maintained `thetaComplex` with
    `α = 0`.  Both extra principles are independent and necessary:
    `u + 2` is affine but not normalized, `u + e^{-u}` is normalized but not
    affine, and both are admissible and different
    (`extra_principles_independent`).
-/

import Mathlib
import WCTLean.Models.ComplexCurvature

namespace WCTLean

open Filter Topology ComplexConjugate

noncomputable section

/-! ### Pointwise closures and their structure -/

/-- A pointwise curvature closure: `(ψ, Δψ) ↦ Θ`. -/
abbrev JetClosure : Type :=
  ℂ → ℂ → ℂ

/-- `ℂ`-homogeneity in the Laplacian slot. -/
def LaplacianHomogeneous (C : JetClosure) : Prop :=
  ∀ ψ c z : ℂ, C ψ (c * z) = c * C ψ z

/-- Global `U(1)` phase invariance: a common unit phase on field and Laplacian
leaves the curvature unchanged. -/
def PhaseInvariant (C : JetClosure) : Prop :=
  ∀ u ψ z : ℂ, ‖u‖ = 1 → C (u * ψ) (u * z) = C ψ z

/-- Radial reweighting `-(Δψ ψ̄) g(|ψ|²)`. -/
def radialClosure (g : ℝ → ℂ) : JetClosure :=
  fun ψ z => -(z * conj ψ) * g (Complex.normSq ψ)

theorem radialClosure_homogeneous (g : ℝ → ℂ) : LaplacianHomogeneous (radialClosure g) := by
  intro ψ c z
  simp only [radialClosure]
  ring

theorem normSq_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) : Complex.normSq u = 1 := by
  rw [Complex.normSq_eq_norm_sq, hu]; norm_num

theorem mul_conj_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) : u * conj u = 1 := by
  rw [Complex.mul_conj, normSq_of_norm_eq_one hu]; simp

theorem radialClosure_phaseInvariant (g : ℝ → ℂ) : PhaseInvariant (radialClosure g) := by
  intro u ψ z hu
  simp only [radialClosure, map_mul, normSq_of_norm_eq_one hu, one_mul]
  have h : u * z * (conj u * conj ψ) = (u * conj u) * (z * conj ψ) := by ring
  rw [h, mul_conj_of_norm_eq_one hu, one_mul]

/-- **Classification of homogeneous phase-invariant closures.**  Every
pointwise closure that is `ℂ`-homogeneous in the Laplacian and globally phase
invariant is a radial reweighting `-(Δψ ψ̄) g(|ψ|²)`. -/
theorem closure_classification (C : JetClosure) (hhom : LaplacianHomogeneous C)
    (hph : PhaseInvariant C) : ∃ g : ℝ → ℂ, C = radialClosure g := by
  have hlin : ∀ ψ z, C ψ z = z * C ψ 1 := by
    intro ψ z
    have h := hhom ψ z 1
    rwa [mul_one] at h
  have hK : ∀ u ψ, ‖u‖ = 1 → u * C (u * ψ) 1 = C ψ 1 := by
    intro u ψ hu
    have h := hph u ψ 1 hu
    rwa [mul_one, hlin (u * ψ) u] at h
  have hK0 : C 0 1 = 0 := by
    have h := hK (-1) 0 (by simp)
    simp only [mul_zero, neg_one_mul] at h
    have h2 : (2 : ℂ) * C 0 1 = 0 := by linear_combination -h
    simpa using h2
  refine ⟨fun s => -(C ((Real.sqrt s : ℝ) : ℂ) 1) / ((Real.sqrt s : ℝ) : ℂ), ?_⟩
  funext ψ z
  simp only [radialClosure]
  rw [hlin ψ z]
  by_cases hψ : ψ = 0
  · subst hψ
    simp [hK0]
  · have hr : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
    have hsqrt : Real.sqrt (Complex.normSq ψ) = ‖ψ‖ := by
      rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    rw [hsqrt]
    have hrC : ((‖ψ‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    set u : ℂ := ψ / ((‖ψ‖ : ℝ) : ℂ) with hu_def
    have hu : ‖u‖ = 1 := by
      rw [hu_def, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
        div_self hr.ne']
    have hψu : ψ = u * ((‖ψ‖ : ℝ) : ℂ) := by
      rw [hu_def, div_mul_cancel₀ _ hrC]
    have hcu : conj u * u = 1 := by rw [mul_comm]; exact mul_conj_of_norm_eq_one hu
    have hKψ : C ψ 1 = conj u * C ((‖ψ‖ : ℝ) : ℂ) 1 := by
      have h := hK u ((‖ψ‖ : ℝ) : ℂ) hu
      rw [← hψu] at h
      calc C ψ 1 = (conj u * u) * C ψ 1 := by rw [hcu, one_mul]
        _ = conj u * (u * C ψ 1) := by ring
        _ = conj u * C ((‖ψ‖ : ℝ) : ℂ) 1 := by rw [h]
    have hconj : conj u = conj ψ / ((‖ψ‖ : ℝ) : ℂ) := by
      rw [hu_def, map_div₀, Complex.conj_ofReal]
    rw [hKψ, hconj]
    field_simp

/-! ### Regularized radial closures -/

/-- The closure induced by a real denominator family `D ε s`. -/
def denominatorClosure (D : ℝ → ℝ → ℝ) (ε : ℝ) : JetClosure :=
  fun ψ z => -(z * conj ψ) / ((D ε (Complex.normSq ψ) : ℝ) : ℂ)

theorem denominatorClosure_eq_radial (D : ℝ → ℝ → ℝ) (ε : ℝ) :
    denominatorClosure D ε = radialClosure (fun s => (((D ε s)⁻¹ : ℝ) : ℂ)) := by
  funext ψ z
  simp only [denominatorClosure, radialClosure, Complex.ofReal_inv, div_eq_mul_inv]

/-- Every regularized radial closure is in the admissible structural class. -/
theorem denominatorClosure_structural (D : ℝ → ℝ → ℝ) (ε : ℝ) :
    LaplacianHomogeneous (denominatorClosure D ε) ∧ PhaseInvariant (denominatorClosure D ε) := by
  rw [denominatorClosure_eq_radial]
  exact ⟨radialClosure_homogeneous _, radialClosure_phaseInvariant _⟩

/-- The maintained regularizer `s + ε² e^{-2αs}` as a family. -/
def maintainedDenominator (α ε s : ℝ) : ℝ :=
  s + ε ^ 2 * Real.exp (-2 * α * s)

/-- The maintained `thetaComplex` is the regularized radial closure of the
maintained denominator. -/
theorem denominatorClosure_maintained (α ε : ℝ) (ψ z : ℂ) :
    denominatorClosure (maintainedDenominator α) ε ψ z = thetaComplex z ψ ε α := by
  rw [thetaComplex_canonical_formula]
  simp only [denominatorClosure, maintainedDenominator, complexRegularizerDenominator]
  rw [show star ψ = conj ψ from rfl]
  ring

/-- Unit covariance of a denominator family: `D_{λε}(λ² s) = λ² D_ε(s)`. -/
def UnitCovariant (D : ℝ → ℝ → ℝ) : Prop :=
  ∀ l ε s : ℝ, 0 < l → 0 < ε → 0 ≤ s → D (l * ε) (l ^ 2 * s) = l ^ 2 * D ε s

/-- Unit covariance of `D` makes the closure invariant under rescaling the
field unit `(ψ, Δψ, ε) ↦ (λψ, λΔψ, λε)`. -/
theorem denominatorClosure_unit_invariant (D : ℝ → ℝ → ℝ) (hD : UnitCovariant D)
    (hpos : ∀ ε s, 0 < ε → 0 ≤ s → 0 < D ε s)
    {l ε : ℝ} (hl : 0 < l) (hε : 0 < ε) (ψ z : ℂ) :
    denominatorClosure D (l * ε) ((l : ℂ) * ψ) ((l : ℂ) * z) = denominatorClosure D ε ψ z := by
  simp only [denominatorClosure]
  have hn : Complex.normSq ((l : ℂ) * ψ) = l ^ 2 * Complex.normSq ψ := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal]; ring
  rw [hn, hD l ε _ hl hε (Complex.normSq_nonneg ψ)]
  have hDpos := hpos ε (Complex.normSq ψ) hε (Complex.normSq_nonneg ψ)
  have hDC : ((D ε (Complex.normSq ψ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hlC : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  rw [map_mul, Complex.conj_ofReal]
  push_cast
  field_simp

/-- The admissible regularizer class. -/
structure AdmissibleRegularizer (D : ℝ → ℝ → ℝ) : Prop where
  pos : ∀ ε s, 0 < ε → 0 ≤ s → 0 < D ε s
  limit : ∀ s, 0 < s → Tendsto (fun ε => D ε s) (𝓝[>] 0) (𝓝 s)
  covariant : UnitCovariant D

/-- **Profile representation.**  An admissible regularizer is determined by
its unit-scale profile `Φ = D 1`: `D_ε(s) = ε² Φ(s/ε²)`. -/
theorem admissible_profile {D : ℝ → ℝ → ℝ} (hD : AdmissibleRegularizer D) {ε s : ℝ}
    (hε : 0 < ε) (hs : 0 ≤ s) : D ε s = ε ^ 2 * D 1 (s / ε ^ 2) := by
  have h := hD.covariant ε 1 (s / ε ^ 2) hε one_pos (div_nonneg hs (sq_nonneg _))
  rwa [mul_one, mul_div_cancel₀ _ (pow_ne_zero 2 hε.ne')] at h

theorem tendsto_real_sqrt_atTop : Tendsto Real.sqrt atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun b => ⟨b ^ 2, fun a ha => ?_⟩
  calc b ≤ |b| := le_abs_self b
    _ = Real.sqrt (b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
    _ ≤ Real.sqrt a := Real.sqrt_le_sqrt ha

/-- **Profile asymptotics.**  The profile of an admissible regularizer is
asymptotically linear: `Φ(u)/u → 1` as `u → ∞`. -/
theorem admissible_profile_asymptotic {D : ℝ → ℝ → ℝ} (hD : AdmissibleRegularizer D) :
    Tendsto (fun u => D 1 u / u) atTop (𝓝 1) := by
  have hlim := hD.limit 1 one_pos
  have hε : Tendsto (fun u : ℝ => (Real.sqrt u)⁻¹) atTop (𝓝[>] 0) :=
    tendsto_inv_atTop_nhdsGT_zero.comp tendsto_real_sqrt_atTop
  refine (hlim.comp hε).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with u hu
  simp only [Function.comp]
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  rw [admissible_profile hD (inv_pos.mpr hsu) zero_le_one]
  have hsq : ((Real.sqrt u)⁻¹) ^ 2 = u⁻¹ := by rw [inv_pow, Real.sq_sqrt hu.le]
  rw [hsq, one_div, inv_inv, div_eq_mul_inv, mul_comm]

/-- The regularizer generated by a profile `Φ`: `D_ε(s) = ε² Φ(s/ε²)`. -/
def profileRegularizer (Φ : ℝ → ℝ) (ε s : ℝ) : ℝ :=
  ε ^ 2 * Φ (s / ε ^ 2)

theorem tendsto_div_sq_nhdsGT_atTop {s : ℝ} (hs : 0 < s) :
    Tendsto (fun ε : ℝ => s / ε ^ 2) (𝓝[>] 0) atTop := by
  have hsq : Tendsto (fun ε : ℝ => ε ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun ε : ℝ => ε ^ 2) (𝓝 0) (𝓝 (0 ^ 2)) :=
        (continuous_pow 2).tendsto 0
      rw [show (0 : ℝ) ^ 2 = 0 by norm_num] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      simp only [Set.mem_Ioi] at hε ⊢
      positivity
  have := (tendsto_inv_nhdsGT_zero.comp hsq).const_mul_atTop hs
  simpa [Function.comp, div_eq_mul_inv] using this

/-- **Converse.**  Every positive, asymptotically linear profile generates an
admissible regularizer. -/
theorem profileRegularizer_admissible (Φ : ℝ → ℝ) (hpos : ∀ u, 0 ≤ u → 0 < Φ u)
    (hasym : Tendsto (fun u => Φ u / u) atTop (𝓝 1)) :
    AdmissibleRegularizer (profileRegularizer Φ) where
  pos := by
    intro ε s hε hs
    exact mul_pos (pow_pos hε 2) (hpos _ (div_nonneg hs (sq_nonneg _)))
  limit := by
    intro s hs
    have h := (hasym.comp (tendsto_div_sq_nhdsGT_atTop hs)).const_mul s
    rw [mul_one] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [Function.comp, profileRegularizer]
    have hε2 : ε ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hε)
    field_simp
  covariant := by
    intro l ε s hl hε _
    simp only [profileRegularizer]
    have hl2 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl.ne'
    have hε2 : ε ^ 2 ≠ 0 := pow_ne_zero 2 hε.ne'
    rw [show l ^ 2 * s / (l * ε) ^ 2 = s / ε ^ 2 by field_simp]
    ring

/-! ### Non-uniqueness -/

/-- Shifted affine profiles `Φ_β(u) = u + β`, `β > 0`. -/
theorem shift_profile_admissible (β : ℝ) (hβ : 0 < β) :
    AdmissibleRegularizer (profileRegularizer fun u => u + β) := by
  apply profileRegularizer_admissible
  · intro u hu; linarith
  · have h : Tendsto (fun u : ℝ => 1 + β * u⁻¹) atTop (𝓝 (1 + β * 0)) :=
      tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul β)
    rw [mul_zero, add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with u hu
    field_simp

theorem shift_profile_formula (β ε s : ℝ) (hε : ε ≠ 0) :
    profileRegularizer (fun u => u + β) ε s = s + β * ε ^ 2 := by
  simp only [profileRegularizer]
  field_simp

/-- **Admissible closures are not unique.**  The shifted profiles give
pairwise distinct admissible closures at every regulator `ε > 0`. -/
theorem admissible_closures_infinite (ε : ℝ) (hε : 0 < ε) :
    Set.Infinite (Set.range fun n : ℕ =>
      denominatorClosure (profileRegularizer fun u => u + ((n : ℝ) + 1)) ε) := by
  apply Set.infinite_range_of_injective
  intro n m h
  have h1 := congrFun (congrFun h 1) 1
  simp only [denominatorClosure, map_one, mul_one,
    shift_profile_formula _ ε 1 hε.ne'] at h1
  have hpos : ∀ k : ℕ, (0 : ℝ) < 1 + ((k : ℝ) + 1) * ε ^ 2 := fun k => by positivity
  have hne : ∀ k : ℕ, ((1 + ((k : ℝ) + 1) * ε ^ 2 : ℝ) : ℂ) ≠ 0 := fun k => by
    exact_mod_cast (hpos k).ne'
  have h2 : ((1 + ((n : ℝ) + 1) * ε ^ 2 : ℝ) : ℂ) = ((1 + ((m : ℝ) + 1) * ε ^ 2 : ℝ) : ℂ) := by
    have := h1
    rw [neg_div, neg_div, neg_inj, div_eq_div_iff (hne n) (hne m), one_mul, one_mul] at this
    exact this.symm
  have h3 : (1 + ((n : ℝ) + 1) * ε ^ 2) = (1 + ((m : ℝ) + 1) * ε ^ 2) := by exact_mod_cast h2
  have hε2 : ε ^ 2 ≠ 0 := pow_ne_zero 2 hε.ne'
  have h4 : (n : ℝ) = m := by
    have := mul_right_cancel₀ hε2 (by linarith : ((n : ℝ) + 1) * ε ^ 2 = ((m : ℝ) + 1) * ε ^ 2)
    linarith
  exact_mod_cast h4

/-! ### The maintained regularizer and dimensional consistency -/

/-- **The maintained regularizer with a fixed `α ≠ 0` is not unit covariant.** -/
theorem maintainedDenominator_not_unitCovariant (α : ℝ) (hα : α ≠ 0) :
    ¬ UnitCovariant (maintainedDenominator α) := by
  intro h
  have h1 := h 2 1 1 (by norm_num) one_pos zero_le_one
  simp only [maintainedDenominator] at h1
  have h2 : Real.exp (-2 * α * (2 ^ 2 * 1)) = Real.exp (-2 * α * 1) := by
    have : (2 * 1 : ℝ) ^ 2 * Real.exp (-2 * α * (2 ^ 2 * 1)) =
        2 ^ 2 * (1 ^ 2 * Real.exp (-2 * α * 1)) := by linarith
    nlinarith [Real.exp_pos (-2 * α * (2 ^ 2 * 1)), Real.exp_pos (-2 * α * 1)]
  have h3 := Real.exp_eq_exp.mp h2
  apply hα
  linarith

/-- With the dimensionally consistent scaling `α = a/ε²`, the maintained
regularizer is the profile regularizer of `Φ_a(u) = u + e^{-2au}`. -/
theorem maintained_scaled_eq_profile (a ε s : ℝ) (hε : ε ≠ 0) :
    maintainedDenominator (a / ε ^ 2) ε s =
      profileRegularizer (fun u => u + Real.exp (-2 * a * u)) ε s := by
  simp only [maintainedDenominator, profileRegularizer]
  have hε2 : ε ^ 2 ≠ 0 := pow_ne_zero 2 hε
  rw [show -2 * (a / ε ^ 2) * s = -2 * a * (s / ε ^ 2) by ring]
  field_simp

/-- The dimensionally consistent maintained family (`a ≥ 0`) is admissible. -/
theorem maintained_scaled_profile_admissible (a : ℝ) (ha : 0 ≤ a) :
    AdmissibleRegularizer (profileRegularizer fun u => u + Real.exp (-2 * a * u)) := by
  apply profileRegularizer_admissible
  · intro u hu; have := Real.exp_pos (-2 * a * u); linarith
  · have hnn : ∀ᶠ u in atTop, 0 ≤ Real.exp (-2 * a * u) * u⁻¹ := by
      filter_upwards [eventually_gt_atTop 0] with u hu
      exact mul_nonneg (Real.exp_pos _).le (inv_nonneg.mpr hu.le)
    have hle : ∀ᶠ u in atTop, Real.exp (-2 * a * u) * u⁻¹ ≤ u⁻¹ := by
      filter_upwards [eventually_gt_atTop 0] with u hu
      have hexp : Real.exp (-2 * a * u) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        have : 0 ≤ a * u := mul_nonneg ha hu.le
        linarith
      calc Real.exp (-2 * a * u) * u⁻¹ ≤ 1 * u⁻¹ :=
            mul_le_mul_of_nonneg_right hexp (inv_nonneg.mpr hu.le)
        _ = u⁻¹ := one_mul _
    have hsmall : Tendsto (fun u : ℝ => Real.exp (-2 * a * u) * u⁻¹) atTop (𝓝 0) :=
      squeeze_zero' hnn hle tendsto_inv_atTop_zero
    have h := tendsto_const_nhds (x := (1 : ℝ)) |>.add hsmall
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with u hu
    field_simp

/-! ### Uniqueness under explicit extra principles -/

/-- **Uniqueness under two extra principles.**  If an admissible regularizer
has an affine profile and is normalized at nodes (`D_ε(0) = ε²`), then
`D_ε(s) = s + ε²` for all `ε > 0`, `s ≥ 0`. -/
theorem admissible_affine_normalized_unique {D : ℝ → ℝ → ℝ} (hD : AdmissibleRegularizer D)
    (haff : ∃ a b : ℝ, ∀ u, 0 ≤ u → D 1 u = a * u + b)
    (hnorm : ∀ ε, 0 < ε → D ε 0 = ε ^ 2) :
    ∀ ε s, 0 < ε → 0 ≤ s → D ε s = s + ε ^ 2 := by
  obtain ⟨a, b, hab⟩ := haff
  have hb : b = 1 := by
    have h0 := hab 0 le_rfl
    rw [hnorm 1 one_pos] at h0
    linarith
  have ha : a = 1 := by
    have hasym := admissible_profile_asymptotic hD
    have hlin : Tendsto (fun u : ℝ => D 1 u / u) atTop (𝓝 a) := by
      have h : Tendsto (fun u : ℝ => a + b * u⁻¹) atTop (𝓝 (a + b * 0)) :=
        tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul b)
      rw [mul_zero, add_zero] at h
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with u hu
      rw [hab u hu.le]
      field_simp
    exact tendsto_nhds_unique hlin hasym
  intro ε s hε hs
  rw [admissible_profile hD hε hs, hab _ (div_nonneg hs (sq_nonneg _)), ha, hb]
  field_simp

/-- **Closure-level uniqueness.**  Under the admissibility axioms plus the two
extra principles, the closure is exactly the maintained `thetaComplex` with
`α = 0`. -/
theorem closure_unique_affine_normalized {D : ℝ → ℝ → ℝ} (hD : AdmissibleRegularizer D)
    (haff : ∃ a b : ℝ, ∀ u, 0 ≤ u → D 1 u = a * u + b)
    (hnorm : ∀ ε, 0 < ε → D ε 0 = ε ^ 2) {ε : ℝ} (hε : 0 < ε) :
    denominatorClosure D ε = fun ψ z => thetaComplex z ψ ε 0 := by
  funext ψ z
  rw [← denominatorClosure_maintained]
  simp only [denominatorClosure, maintainedDenominator]
  rw [admissible_affine_normalized_unique hD haff hnorm ε _ hε (Complex.normSq_nonneg ψ)]
  simp

/-- **Non-vacuity.**  The uniqueness hypotheses are satisfiable: the affine
profile `u + 1` is admissible, affine and node-normalized. -/
theorem selected_regularizer_satisfies_principles :
    AdmissibleRegularizer (profileRegularizer fun u => u + 1) ∧
      (∃ a b : ℝ, ∀ u, 0 ≤ u → profileRegularizer (fun u => u + 1) 1 u = a * u + b) ∧
      ∀ ε, 0 < ε → profileRegularizer (fun u => u + 1) ε 0 = ε ^ 2 := by
  refine ⟨shift_profile_admissible 1 one_pos, ⟨1, 1, fun u _ => ?_⟩, fun ε hε => ?_⟩
  · simp [profileRegularizer]
  · rw [shift_profile_formula 1 ε 0 hε.ne']; ring

/-- **The two extra principles are independent.**  `u + 2` is admissible and
affine but not normalized; `u + e^{-u}` is admissible and normalized but not
affine; both differ from the selected `u + 1`. -/
theorem extra_principles_independent :
    (AdmissibleRegularizer (profileRegularizer fun u => u + 2) ∧
        (∃ a b : ℝ, ∀ u, 0 ≤ u → profileRegularizer (fun u => u + 2) 1 u = a * u + b) ∧
        profileRegularizer (fun u => u + 2) 1 0 ≠ 1 ^ 2) ∧
      (AdmissibleRegularizer (profileRegularizer fun u => u + Real.exp (-2 * (1 / 2) * u)) ∧
        (∀ ε, 0 < ε →
          profileRegularizer (fun u => u + Real.exp (-2 * (1 / 2) * u)) ε 0 = ε ^ 2) ∧
        ¬ ∃ a b : ℝ, ∀ u, 0 ≤ u →
          profileRegularizer (fun u => u + Real.exp (-2 * (1 / 2) * u)) 1 u = a * u + b) := by
  refine ⟨⟨shift_profile_admissible 2 (by norm_num), ⟨1, 2, fun u _ => ?_⟩, ?_⟩,
    ⟨maintained_scaled_profile_admissible (1 / 2) (by norm_num), fun ε hε => ?_, ?_⟩⟩
  · simp [profileRegularizer]
  · simp [profileRegularizer]
  · simp only [profileRegularizer, zero_div, mul_zero, Real.exp_zero, zero_add, mul_one]
  · rintro ⟨a, b, hab⟩
    have h0 := hab 0 le_rfl
    have h1 := hab 1 zero_le_one
    have h2 := hab 2 zero_le_two
    simp only [profileRegularizer, one_pow, div_one, one_mul] at h0 h1 h2
    norm_num at h0 h1 h2
    -- `e^{-u}` would be affine on `{0,1,2}`: `e^{-2} - 2 e^{-1} + 1 = 0`, impossible
    have hconv : Real.exp (-2) - 2 * Real.exp (-1) + 1 = 0 := by linarith
    have hsq : Real.exp (-2) = Real.exp (-1) ^ 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [hsq] at hconv
    have h1' : Real.exp (-1) = 1 := by nlinarith [sq_nonneg (Real.exp (-1) - 1)]
    have : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith

end

end WCTLean
