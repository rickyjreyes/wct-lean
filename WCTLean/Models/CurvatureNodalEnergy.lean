/-
  WCTLean/Models/CurvatureNodalEnergy.lean

  Issue #22: the ε → 0 limit of the regularized curvature *energy* for genuine
  one-dimensional `C²` fields, with the nodal set treated explicitly.

  The maintained corrected operator is
      Θ_ε[ψ] = -Δψ · ψ̄ / (|ψ|² + ε² e^{-2α|ψ|²})          (`thetaComplex`),
  and on the one-dimensional model `Δψ = ψ''`.

  Sharp dichotomy proved here (real fields, `α ≥ 0` where stated):

  * **Nodal blow-up.**  If `ψ` has a *simple* zero `x₀` (`ψ x₀ = 0`,
    `ψ' x₀ ≠ 0`) at which the Laplacian does not vanish (`ψ'' x₀ ≠ 0`), then
    for small `ε` the curvature energy on `[x₀ - ε, x₀ + ε]` is at least
    `C / ε` (`nodal_curvature_energy_lower_bound`), so on every interval
    containing `x₀` the regularized energy tends to `+∞` as `ε → 0⁺`
    (`nodal_curvature_energy_tendsto_atTop`).  The general quantitative
    estimate `curvature_energy_node_lower_bound` holds for complex fields
    with supplied Laplacian.
  * **Concrete periodic witness.**  `ψ = cos x - 1/2` (smooth, `2π`-periodic,
    simple node at `π/3` with `ψ''(π/3) = -1/2`) has
    `∫₀^{2π} |Θ_ε[ψ]|² → +∞` (`cos_sub_half_curvature_energy_tendsto_atTop`).
  * **Convergence under the multiplicative relation.**  If `ψ'' = V ψ`
    with `V` continuous and the nodal set is Lebesgue-null, then
    `∫₀^{2π} |Θ_ε[ψ]|² → ∫₀^{2π} V²` for every `α`
    (`curvature_energy_tendsto_of_multiplicative`); for the eigenmodes
    `sin (k x)` (`k ≠ 0`) the limit is `2π k⁴`
    (`sin_curvature_energy_tendsto`).

  So energy convergence as `ε → 0⁺` is decided at the nodal set: it fails
  (at rate `1/ε`) whenever a simple node carries nonzero Laplacian, and holds
  when the Laplacian factors through the field.  This is the periodic /
  one-dimensional model only; whole-space and weak-formulation limits are
  not addressed here.
-/

import Mathlib
import WCTLean.Models.ComplexCurvature
import WCTLean.Models.FisherCurvature

namespace WCTLean

open Real Filter Topology MeasureTheory intervalIntegral

noncomputable section

/-! ### Norm of the maintained operator -/

/-- The corrected denominator is nonnegative. -/
theorem complexRegularizerDenominator_nonneg (psi : ℂ) (ε α : ℝ) :
    0 ≤ complexRegularizerDenominator psi ε α := by
  unfold complexRegularizerDenominator
  exact add_nonneg (Complex.normSq_nonneg _) (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)

/-- Exact modulus of the maintained curvature operator:
`|Θ_ε| = |Δψ| |ψ| / D_ε(ψ)` (valid unconditionally, with Lean's `x / 0 = 0`). -/
theorem norm_thetaComplex (lap psi : ℂ) (ε α : ℝ) :
    ‖thetaComplex lap psi ε α‖ = ‖lap‖ * ‖psi‖ / complexRegularizerDenominator psi ε α := by
  unfold thetaComplex complexRegularizedReciprocal
  rw [norm_mul, norm_neg, norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (complexRegularizerDenominator_nonneg psi ε α), mul_div_assoc]

/-- `D_ε(ψ) ≤ |ψ|² + ε²` when `α ≥ 0`. -/
theorem complexRegularizerDenominator_le (psi : ℂ) (ε α : ℝ) (hα : 0 ≤ α) :
    complexRegularizerDenominator psi ε α ≤ ‖psi‖ ^ 2 + ε ^ 2 := by
  unfold complexRegularizerDenominator
  rw [Complex.normSq_eq_norm_sq]
  have hexp : Real.exp (-2 * α * ‖psi‖ ^ 2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ α * ‖psi‖ ^ 2 := mul_nonneg hα (sq_nonneg _)
    linarith
  have := mul_le_of_le_one_right (sq_nonneg ε) hexp
  linarith

/-- Continuity of the maintained curvature density for continuous data and
`ε ≠ 0`. -/
theorem continuous_thetaComplex_comp {ψ lap : ℝ → ℂ} (hψ : Continuous ψ) (hl : Continuous lap)
    {ε : ℝ} (hε : ε ≠ 0) (α : ℝ) :
    Continuous fun x => thetaComplex (lap x) (ψ x) ε α := by
  have hD : Continuous fun x => complexRegularizerDenominator (ψ x) ε α := by
    unfold complexRegularizerDenominator
    have hn : Continuous fun x => Complex.normSq (ψ x) := Complex.continuous_normSq.comp hψ
    fun_prop
  have hDne : ∀ x, ((complexRegularizerDenominator (ψ x) ε α : ℝ) : ℂ) ≠ 0 := by
    intro x
    have hpos : 0 < complexRegularizerDenominator (ψ x) ε α := by
      unfold complexRegularizerDenominator
      have h1 : 0 ≤ Complex.normSq (ψ x) := Complex.normSq_nonneg _
      have h2 : 0 < ε ^ 2 := by positivity
      have h3 := Real.exp_pos (-2 * α * Complex.normSq (ψ x))
      nlinarith [mul_pos h2 h3]
    exact_mod_cast ne_of_gt hpos
  unfold thetaComplex complexRegularizedReciprocal
  exact hl.neg.mul ((continuous_star.comp hψ).div (Complex.continuous_ofReal.comp hD) hDne)

/-! ### Quantitative lower bound at a node (complex fields, supplied Laplacian) -/

/-- `∫_{x₀-ε}^{x₀+ε} (x - x₀)² = 2ε³/3`. -/
theorem integral_sq_sub_center (x₀ ε : ℝ) :
    ∫ x in (x₀ - ε)..(x₀ + ε), (x - x₀) ^ 2 = 2 * ε ^ 3 / 3 := by
  rw [intervalIntegral.integral_comp_sub_right (fun x => x ^ 2) x₀, integral_pow]
  ring

/-- **Local nodal lower bound.**  Suppose that on `[x₀ - ε, x₀ + ε]` the field
vanishes at most linearly from both sides, `c |x - x₀| ≤ |ψ x| ≤ L |x - x₀|`,
and the Laplacian stays away from zero, `m ≤ |Δψ x|`.  Then for `α ≥ 0`
`∫_{x₀-ε}^{x₀+ε} |Θ_ε[ψ]|² ≥ 2 m² c² / (3 (L² + 1)² ε)`. -/
theorem curvature_energy_node_lower_bound (ψ lap : ℝ → ℂ) (x₀ ε α c L m : ℝ)
    (hψc : Continuous ψ) (hlc : Continuous lap) (hε : 0 < ε) (hα : 0 ≤ α) (hc : 0 < c)
    (hm : 0 < m) (hL : 0 ≤ L)
    (hlow : ∀ x ∈ Set.Icc (x₀ - ε) (x₀ + ε), c * |x - x₀| ≤ ‖ψ x‖)
    (hup : ∀ x ∈ Set.Icc (x₀ - ε) (x₀ + ε), ‖ψ x‖ ≤ L * |x - x₀|)
    (hlap : ∀ x ∈ Set.Icc (x₀ - ε) (x₀ + ε), m ≤ ‖lap x‖) :
    2 * m ^ 2 * c ^ 2 / (3 * (L ^ 2 + 1) ^ 2 * ε) ≤
      ∫ x in (x₀ - ε)..(x₀ + ε), ‖thetaComplex (lap x) (ψ x) ε α‖ ^ 2 := by
  set K : ℝ := m ^ 2 * c ^ 2 / ((L ^ 2 + 1) ^ 2 * ε ^ 4) with hK_def
  have hlowInt : ∫ x in (x₀ - ε)..(x₀ + ε), K * (x - x₀) ^ 2 =
      2 * m ^ 2 * c ^ 2 / (3 * (L ^ 2 + 1) ^ 2 * ε) := by
    rw [intervalIntegral.integral_const_mul, integral_sq_sub_center, hK_def]
    field_simp
  rw [← hlowInt]
  have hcont := continuous_thetaComplex_comp hψc hlc (ne_of_gt hε) α
  apply intervalIntegral.integral_mono_on (by linarith)
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · exact (hcont.norm.pow 2).intervalIntegrable _ _
  · intro x hx
    have hxε : |x - x₀| ≤ ε := by
      rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    have hn := hlow x hx
    have hnu := hup x hx
    have hl := hlap x hx
    have hD0 : 0 < complexRegularizerDenominator (ψ x) ε α := by
      unfold complexRegularizerDenominator
      have h1 : 0 ≤ Complex.normSq (ψ x) := Complex.normSq_nonneg _
      have h2 : 0 < ε ^ 2 := by positivity
      have h3 := Real.exp_pos (-2 * α * Complex.normSq (ψ x))
      nlinarith [mul_pos h2 h3]
    have hDle : complexRegularizerDenominator (ψ x) ε α ≤ (L ^ 2 + 1) * ε ^ 2 := by
      have h := complexRegularizerDenominator_le (ψ x) ε α hα
      have hsq : ‖ψ x‖ ^ 2 ≤ L ^ 2 * ε ^ 2 := by
        have h0 : 0 ≤ ‖ψ x‖ := norm_nonneg _
        have h1 : ‖ψ x‖ ≤ L * ε := le_trans hnu (mul_le_mul_of_nonneg_left hxε hL)
        calc ‖ψ x‖ ^ 2 ≤ (L * ε) ^ 2 := pow_le_pow_left₀ h0 h1 2
          _ = L ^ 2 * ε ^ 2 := by ring
      nlinarith
    -- lower bound for `|Θ|`
    have hlower : m * (c * |x - x₀|) / ((L ^ 2 + 1) * ε ^ 2) ≤
        ‖thetaComplex (lap x) (ψ x) ε α‖ := by
      rw [norm_thetaComplex]
      apply div_le_div₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul hl hn (by positivity) (norm_nonneg _)) hD0 hDle
    have hlower0 : 0 ≤ m * (c * |x - x₀|) / ((L ^ 2 + 1) * ε ^ 2) := by positivity
    have hsq := pow_le_pow_left₀ hlower0 hlower 2
    have hε0 : ε ≠ 0 := ne_of_gt hε
    have hL1 : L ^ 2 + 1 ≠ 0 := by positivity
    calc K * (x - x₀) ^ 2 = (m * (c * |x - x₀|) / ((L ^ 2 + 1) * ε ^ 2)) ^ 2 := by
          rw [hK_def, ← sq_abs (x - x₀)]
          field_simp
      _ ≤ ‖thetaComplex (lap x) (ψ x) ε α‖ ^ 2 := hsq

/-! ### Simple zeros of real `C²` fields -/

/-- Near a simple zero, a `C¹` real field vanishes exactly linearly:
`|ψ' x₀|/2 · |x - x₀| ≤ |ψ x| ≤ 3|ψ' x₀|/2 · |x - x₀|` on a neighbourhood. -/
theorem simple_zero_local_bounds (ψ ψ' : ℝ → ℝ) (x₀ : ℝ)
    (h1 : ∀ x, HasDerivAt ψ (ψ' x) x) (hc1 : Continuous ψ') (hzero : ψ x₀ = 0)
    (hsimple : ψ' x₀ ≠ 0) :
    ∃ δ > 0, ∀ x, |x - x₀| ≤ δ →
      |ψ' x₀| / 2 * |x - x₀| ≤ |ψ x| ∧ |ψ x| ≤ 3 * |ψ' x₀| / 2 * |x - x₀| := by
  set a := ψ' x₀ with ha_def
  have ha : 0 < |a| := abs_pos.mpr hsimple
  obtain ⟨δ', hδ', hball⟩ := Metric.continuous_iff.mp hc1 x₀ (|a| / 2) (by positivity)
  refine ⟨δ' / 2, by positivity, ?_⟩
  intro x hx
  set s := Set.Icc (x₀ - δ' / 2) (x₀ + δ' / 2) with hs_def
  have hconv : Convex ℝ s := convex_Icc _ _
  have hmem : ∀ y, |y - x₀| ≤ δ' / 2 → y ∈ s := by
    intro y hy
    rw [abs_le] at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  -- `g x = ψ x - a (x - x₀)` has derivative bounded by `|a|/2` on `s`
  set g : ℝ → ℝ := fun y => ψ y - a * (y - x₀) with hg_def
  have hg : ∀ y ∈ s, HasDerivWithinAt g (ψ' y - a) s y := by
    intro y _
    have hlin : HasDerivAt (fun y : ℝ => a * (y - x₀)) a y := by
      simpa using ((hasDerivAt_id y).sub_const x₀).const_mul a
    exact ((h1 y).sub hlin).hasDerivWithinAt
  have hbound : ∀ y ∈ s, ‖ψ' y - a‖ ≤ |a| / 2 := by
    intro y hy
    have hy' : dist y x₀ < δ' := by
      rw [Real.dist_eq]
      have : |y - x₀| ≤ δ' / 2 := by
        rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
      linarith
    have := hball y hy'
    rw [Real.dist_eq] at this
    rw [Real.norm_eq_abs]
    exact this.le
  have hx0 : x₀ ∈ s := hmem x₀ (by simp; positivity)
  have hxs : x ∈ s := hmem x hx
  have hlip := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hg hbound hx0 hxs
  simp only [hg_def, Real.norm_eq_abs, hzero, sub_self, mul_zero, sub_zero] at hlip
  -- `|ψ x - a (x - x₀)| ≤ |a|/2 |x - x₀|`
  have habs : |a * (x - x₀)| = |a| * |x - x₀| := abs_mul _ _
  constructor
  · have := abs_sub_abs_le_abs_sub (a * (x - x₀)) (ψ x)
    rw [abs_sub_comm (a * (x - x₀)), habs] at this
    nlinarith [abs_nonneg (x - x₀)]
  · have := abs_sub_abs_le_abs_sub (ψ x) (a * (x - x₀))
    rw [habs] at this
    nlinarith [abs_nonneg (x - x₀)]

/-- Near a point where a continuous function is nonzero it stays at least half
its size. -/
theorem continuous_local_abs_lower (f : ℝ → ℝ) (x₀ : ℝ) (hf : Continuous f) (h : f x₀ ≠ 0) :
    ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x₀| / 2 ≤ |f x| := by
  have ha : 0 < |f x₀| := abs_pos.mpr h
  obtain ⟨δ', hδ', hball⟩ := Metric.continuous_iff.mp hf x₀ (|f x₀| / 2) (by positivity)
  refine ⟨δ' / 2, by positivity, fun x hx => ?_⟩
  have hx' : dist x x₀ < δ' := by rw [Real.dist_eq]; linarith
  have := hball x hx'
  rw [Real.dist_eq] at this
  have := abs_sub_abs_le_abs_sub (f x₀) (f x)
  rw [abs_sub_comm] at this
  linarith

/-- **Nodal blow-up of the regularized curvature energy.**  At a simple zero
`x₀` of a real `C²` field with `ψ'' x₀ ≠ 0`, there are `δ, C > 0` such that
for all `0 < ε ≤ δ`, `∫_{x₀-ε}^{x₀+ε} |Θ_ε[ψ]|² ≥ C / ε` (`α ≥ 0`). -/
theorem nodal_curvature_energy_lower_bound (ψ ψ' ψ'' : ℝ → ℝ) (x₀ : ℝ)
    (h1 : ∀ x, HasDerivAt ψ (ψ' x) x) (h2 : ∀ x, HasDerivAt ψ' (ψ'' x) x)
    (hc2 : Continuous ψ'') (hzero : ψ x₀ = 0) (hsimple : ψ' x₀ ≠ 0) (hlap : ψ'' x₀ ≠ 0)
    (α : ℝ) (hα : 0 ≤ α) :
    ∃ δ > 0, ∃ C > 0, ∀ ε, 0 < ε → ε ≤ δ →
      C / ε ≤ ∫ x in (x₀ - ε)..(x₀ + ε), ‖curvatureField (realField ψ) ε α x‖ ^ 2 := by
  have hc1 : Continuous ψ' := continuous_iff_continuousAt.2 fun x => (h2 x).continuousAt
  have hc0 : Continuous ψ := continuous_iff_continuousAt.2 fun x => (h1 x).continuousAt
  obtain ⟨δ₁, hδ₁, hb₁⟩ := simple_zero_local_bounds ψ ψ' x₀ h1 hc1 hzero hsimple
  obtain ⟨δ₂, hδ₂, hb₂⟩ := continuous_local_abs_lower ψ'' x₀ hc2 hlap
  set c := |ψ' x₀| / 2 with hc_def
  set L := 3 * |ψ' x₀| / 2 with hL_def
  set m := |ψ'' x₀| / 2 with hm_def
  have hcpos : 0 < c := by have := abs_pos.mpr hsimple; positivity
  have hmpos : 0 < m := by have := abs_pos.mpr hlap; positivity
  have hL0 : 0 ≤ L := by positivity
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, 2 * m ^ 2 * c ^ 2 / (3 * (L ^ 2 + 1) ^ 2),
    by positivity, ?_⟩
  intro ε hε hεδ
  have hint : ∀ x ∈ Set.Icc (x₀ - ε) (x₀ + ε), |x - x₀| ≤ ε := by
    intro x hx; rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have hcf : ∀ x, curvatureField (realField ψ) ε α x =
      thetaComplex (ψ'' x : ℂ) (ψ x : ℂ) ε α :=
    realField_curvatureField ψ ψ' ψ'' h1 h2 ε α
  simp_rw [hcf]
  have hbound := curvature_energy_node_lower_bound (fun x => (ψ x : ℂ)) (fun x => (ψ'' x : ℂ))
    x₀ ε α c L m (Complex.continuous_ofReal.comp hc0) (Complex.continuous_ofReal.comp hc2)
    hε hα hcpos hmpos hL0
    (fun x hx => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (hb₁ x ((hint x hx).trans (hεδ.trans (min_le_left _ _)))).1)
    (fun x hx => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (hb₁ x ((hint x hx).trans (hεδ.trans (min_le_left _ _)))).2)
    (fun x hx => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hb₂ x ((hint x hx).trans (hεδ.trans (min_le_right _ _))))
  calc 2 * m ^ 2 * c ^ 2 / (3 * (L ^ 2 + 1) ^ 2) / ε =
        2 * m ^ 2 * c ^ 2 / (3 * (L ^ 2 + 1) ^ 2 * ε) := by rw [div_div]
    _ ≤ _ := hbound

/-- On every interval strictly containing such a node, the regularized
curvature energy diverges as `ε → 0⁺`. -/
theorem nodal_curvature_energy_tendsto_atTop (ψ ψ' ψ'' : ℝ → ℝ) (x₀ a b : ℝ)
    (h1 : ∀ x, HasDerivAt ψ (ψ' x) x) (h2 : ∀ x, HasDerivAt ψ' (ψ'' x) x)
    (hc2 : Continuous ψ'') (hzero : ψ x₀ = 0) (hsimple : ψ' x₀ ≠ 0) (hlap : ψ'' x₀ ≠ 0)
    (hax : a < x₀) (hxb : x₀ < b) (α : ℝ) (hα : 0 ≤ α) :
    Tendsto (fun ε => ∫ x in a..b, ‖curvatureField (realField ψ) ε α x‖ ^ 2)
      (𝓝[>] 0) atTop := by
  obtain ⟨δ, hδ, C, hC, hbound⟩ :=
    nodal_curvature_energy_lower_bound ψ ψ' ψ'' x₀ h1 h2 hc2 hzero hsimple hlap α hα
  have hc0 : Continuous ψ := continuous_iff_continuousAt.2 fun x => (h1 x).continuousAt
  have hcf : ∀ ε x, curvatureField (realField ψ) ε α x =
      thetaComplex (ψ'' x : ℂ) (ψ x : ℂ) ε α :=
    fun ε => realField_curvatureField ψ ψ' ψ'' h1 h2 ε α
  have hdiv : Tendsto (fun ε : ℝ => C / ε) (𝓝[>] 0) atTop := by
    simpa [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop hC
  refine tendsto_atTop_mono' _ ?_ hdiv
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < min δ (min (x₀ - a) (b - x₀)) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (lt_min hδ (lt_min (by linarith) (by linarith))))
  filter_upwards [hpos, hsmall] with ε hε hεs
  have hεδ : ε ≤ δ := (hεs.trans_le (min_le_left _ _)).le
  have hεa : ε < x₀ - a := hεs.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεb : ε < b - x₀ := hεs.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine (hbound ε hε hεδ).trans ?_
  have hcont : Continuous fun x => ‖curvatureField (realField ψ) ε α x‖ ^ 2 := by
    simp_rw [hcf ε]
    exact ((continuous_thetaComplex_comp (Complex.continuous_ofReal.comp hc0)
      (Complex.continuous_ofReal.comp hc2) (ne_of_gt hε) α).norm.pow 2)
  exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
    (Eventually.of_forall fun x => sq_nonneg _) (hcont.intervalIntegrable _ _)

/-! ### Concrete smooth periodic witness: `ψ = cos x - 1/2` -/

/-- **Concrete divergence on the periodic model.**  For the smooth
`2π`-periodic field `ψ = cos x - 1/2`, which has a simple node at `π/3` with
`ψ''(π/3) = -1/2`, the maintained curvature energy over one period diverges
as `ε → 0⁺`, for every `α ≥ 0`. -/
theorem cos_sub_half_curvature_energy_tendsto_atTop (α : ℝ) (hα : 0 ≤ α) :
    Tendsto (fun ε => periodCurvatureEnergy (realField fun x => Real.cos x - 1 / 2) ε α)
      (𝓝[>] 0) atTop := by
  have h1 : ∀ x, HasDerivAt (fun x => Real.cos x - 1 / 2) (-Real.sin x) x :=
    fun x => (Real.hasDerivAt_cos x).sub_const _
  have h2 : ∀ x, HasDerivAt (fun x => -Real.sin x) (-Real.cos x) x :=
    fun x => (Real.hasDerivAt_sin x).neg
  have hzero : Real.cos (π / 3) - 1 / 2 = 0 := by rw [Real.cos_pi_div_three]; ring
  have hsimple : -Real.sin (π / 3) ≠ 0 := by
    have : 0 < Real.sin (π / 3) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
    linarith
  have hlap : -Real.cos (π / 3) ≠ 0 := by rw [Real.cos_pi_div_three]; norm_num
  exact nodal_curvature_energy_tendsto_atTop (fun x => Real.cos x - 1 / 2)
    (fun x => -Real.sin x) (fun x => -Real.cos x) (π / 3) 0 (2 * π) h1 h2
    Real.continuous_cos.neg hzero hsimple hlap (by positivity) (by linarith [Real.pi_pos]) α hα

/-! ### Convergence under the multiplicative relation `ψ'' = V ψ` -/

/-- **Energy convergence for multiplicative Laplacians.**  If `ψ'' = V ψ` with
`V` continuous and the nodal set of `ψ` is Lebesgue-null, then for every `α`
the maintained curvature energy converges:
`∫₀^{2π} |Θ_ε[ψ]|² → ∫₀^{2π} V²` as `ε → 0⁺`. -/
theorem curvature_energy_tendsto_of_multiplicative (ψ ψ' ψ'' V : ℝ → ℝ)
    (h1 : ∀ x, HasDerivAt ψ (ψ' x) x) (h2 : ∀ x, HasDerivAt ψ' (ψ'' x) x)
    (hV : Continuous V) (hrel : ∀ x, ψ'' x = V x * ψ x)
    (hnull : volume {x | ψ x = 0} = 0) (α : ℝ) :
    Tendsto (fun ε => periodCurvatureEnergy (realField ψ) ε α) (𝓝[>] 0)
      (𝓝 (∫ x in (0 : ℝ)..(2 * π), V x ^ 2)) := by
  have hc0 : Continuous ψ := continuous_iff_continuousAt.2 fun x => (h1 x).continuousAt
  have hc2 : Continuous ψ'' := by
    have : ψ'' = fun x => V x * ψ x := funext hrel
    rw [this]; exact hV.mul hc0
  have hcf : ∀ ε x, curvatureField (realField ψ) ε α x =
      thetaComplex (ψ'' x : ℂ) (ψ x : ℂ) ε α :=
    fun ε => realField_curvatureField ψ ψ' ψ'' h1 h2 ε α
  -- explicit real form of the energy density
  have hform : ∀ ε x, ‖curvatureField (realField ψ) ε α x‖ ^ 2 =
      (V x * (ψ x * ψ x) / (ψ x * ψ x + ε ^ 2 * Real.exp (-2 * α * (ψ x * ψ x)))) ^ 2 := by
    intro ε x
    rw [hcf, thetaComplex_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      complexRegularizerDenominator_ofReal, hrel]
    ring
  unfold periodCurvatureEnergy
  simp_rw [hform]
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun x => V x ^ 2)
  · -- measurability
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (ε : ℝ) ≠ 0 := ne_of_gt hε
    have hcont : Continuous fun x =>
        (V x * (ψ x * ψ x) / (ψ x * ψ x + ε ^ 2 * Real.exp (-2 * α * (ψ x * ψ x)))) ^ 2 := by
      have hD : ∀ x, ψ x * ψ x + ε ^ 2 * Real.exp (-2 * α * (ψ x * ψ x)) ≠ 0 := by
        intro x
        have h1' : 0 ≤ ψ x * ψ x := mul_self_nonneg _
        have h2' : 0 < ε ^ 2 := by positivity
        have h3' := Real.exp_pos (-2 * α * (ψ x * ψ x))
        nlinarith [mul_pos h2' h3']
      exact (Continuous.div (by fun_prop) (by fun_prop) hD).pow 2
    exact hcont.aestronglyMeasurable
  · -- domination by `V²`
    refine Eventually.of_forall fun ε => Eventually.of_forall fun x _ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hq : |ψ x * ψ x / (ψ x * ψ x + ε ^ 2 * Real.exp (-2 * α * (ψ x * ψ x)))| ≤ 1 := by
      have h1' : 0 ≤ ψ x * ψ x := mul_self_nonneg _
      have h2' : 0 ≤ ε ^ 2 * Real.exp (-2 * α * (ψ x * ψ x)) :=
        mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
      rw [abs_of_nonneg (div_nonneg h1' (add_nonneg h1' h2'))]
      rcases eq_or_lt_of_le (add_nonneg h1' h2') with h | h
      · rw [← h, div_zero]; norm_num
      · rw [div_le_one h]; linarith
    calc (V x * (ψ x * ψ x) / (ψ x * ψ x + ε ^ 2 * Real.exp (-2 * α * (ψ x * ψ x)))) ^ 2
        = V x ^ 2 * (ψ x * ψ x / (ψ x * ψ x + ε ^ 2 * Real.exp (-2 * α * (ψ x * ψ x)))) ^ 2 := by
          ring
      _ ≤ V x ^ 2 * 1 := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          rw [← sq_abs]
          calc |ψ x * ψ x / (ψ x * ψ x + ε ^ 2 * Real.exp (-2 * α * (ψ x * ψ x)))| ^ 2
              ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hq 2
            _ = 1 := one_pow 2
      _ = V x ^ 2 := mul_one _
  · exact (hV.pow 2).intervalIntegrable _ _
  · -- pointwise convergence off the null nodal set
    have hae : ∀ᵐ x ∂volume, x ∉ {x | ψ x = 0} := measure_eq_zero_iff_ae_notMem.mp hnull
    filter_upwards [hae] with x hx _
    have hψx : ψ x ≠ 0 := hx
    have hpp : 0 < ψ x * ψ x := mul_self_pos.mpr hψx
    have hcontε : ContinuousAt (fun ε : ℝ =>
        (V x * (ψ x * ψ x) / (ψ x * ψ x + ε ^ 2 * Real.exp (-2 * α * (ψ x * ψ x)))) ^ 2) 0 := by
      have hden : (ψ x * ψ x + (0 : ℝ) ^ 2 * Real.exp (-2 * α * (ψ x * ψ x))) ≠ 0 := by
        simp; exact hψx
      fun_prop (disch := exact hden)
    have hlim := hcontε.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    have hval : (V x * (ψ x * ψ x) / (ψ x * ψ x + (0 : ℝ) ^ 2 *
        Real.exp (-2 * α * (ψ x * ψ x)))) ^ 2 = V x ^ 2 := by
      have : ψ x * ψ x ≠ 0 := ne_of_gt hpp
      rw [show (0 : ℝ) ^ 2 = 0 by norm_num, zero_mul, add_zero, mul_div_assoc, div_self this,
        mul_one]
    rw [hval] at hlim
    exact hlim

/-- The nodal set of `sin (k x)`, `k ≠ 0`, is countable, hence null. -/
theorem sin_mul_zero_set_null (k : ℝ) (hk : k ≠ 0) :
    volume {x : ℝ | Real.sin (k * x) = 0} = 0 := by
  apply Set.Countable.measure_zero
  apply (Set.countable_range (fun n : ℤ => (n : ℝ) * π / k)).mono
  intro x hx
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hx
  refine ⟨n, ?_⟩
  show (n : ℝ) * π / k = x
  rw [hn]
  field_simp

/-- **Eigenmode convergence.**  For `ψ = sin (k x)` with `k ≠ 0` (so
`ψ'' = -k² ψ` and the Laplacian vanishes on the nodal set), the maintained
curvature energy converges to `2π k⁴` as `ε → 0⁺`, for every `α`. -/
theorem sin_curvature_energy_tendsto (k : ℝ) (hk : k ≠ 0) (α : ℝ) :
    Tendsto (fun ε => periodCurvatureEnergy (realField fun x => Real.sin (k * x)) ε α)
      (𝓝[>] 0) (𝓝 (2 * π * k ^ 4)) := by
  have hkx : ∀ x, HasDerivAt (fun x : ℝ => k * x) k x := by
    intro x; simpa using (hasDerivAt_id x).const_mul k
  have h1 : ∀ x, HasDerivAt (fun x => Real.sin (k * x)) (k * Real.cos (k * x)) x := by
    intro x
    have := (Real.hasDerivAt_sin (k * x)).comp x (hkx x)
    convert this using 1; ring
  have h2 : ∀ x, HasDerivAt (fun x => k * Real.cos (k * x)) (-k ^ 2 * Real.sin (k * x)) x := by
    intro x
    have := ((Real.hasDerivAt_cos (k * x)).comp x (hkx x)).const_mul k
    convert this using 1; ring
  have h := curvature_energy_tendsto_of_multiplicative (fun x => Real.sin (k * x))
    (fun x => k * Real.cos (k * x)) (fun x => -k ^ 2 * Real.sin (k * x)) (fun _ => -k ^ 2)
    h1 h2 continuous_const (fun x => rfl) (sin_mul_zero_set_null k hk) α
  have hval : ∫ x in (0 : ℝ)..(2 * π), (-k ^ 2) ^ 2 = 2 * π * k ^ 4 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  rw [hval] at h
  exact h

end

end WCTLean
