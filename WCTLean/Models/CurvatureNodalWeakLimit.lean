/-
  WCTLean/Models/CurvatureNodalWeakLimit.lean

  Issue #22: which mode of convergence survives the ε → 0 limit at a node.

  For a genuine one-dimensional real field with a simple zero `x₀`
  (`ψ x₀ = 0`, `ψ' x₀ ≠ 0`) carrying nonzero Laplacian (`ψ'' x₀ ≠ 0`), the
  maintained regularized curvature `Θ_ε = -ψ''ψ̄/(|ψ|² + ε² e^{-2α|ψ|²})`
  behaves as follows as `ε → 0⁺`:

  * `L²` (energy): diverges like `1/ε`
    (`Models/CurvatureNodalEnergy.lean`);
  * `L¹`: diverges like `log(1/ε)` (`nodal_curvature_L1_lower_bound`,
    `nodal_curvature_L1_tendsto_atTop`), so there is no strong `L¹_loc`
    limit;
  * **weak (distributional)**: for the regularizer with `α = 0` (the
    closure selected in `Models/ClosureClassification.lean`), the pairing
    `∫_a^b Θ_ε φ` with every `C¹` test function converges
    (`nodal_curvature_weak_limit`), with the explicit limit
    `u(b) log ψ(b)² - u(a) log ψ(a)² - ∫_a^b u' log ψ²`,
    `u = -ψ''φ/(2ψ')`.  This is obtained by integrating by parts against
    `log(ψ² + ε²)`, whose derivative is `2ψψ'/(ψ² + ε²)`.

  Concrete witness: `ψ = cos x - 1/2` on `[π/6, π/2]`
  (`cos_sub_half_nodal_trichotomy`).

  Hypotheses (all explicit): `C³` regularity of `ψ` (with continuous `ψ'''`)
  for the weak limit, `C¹` test functions, a slope floor `|ψ'| ≥ c > 0` on
  `[a, b]`, and a zero strictly inside `(a, b)`.  One-dimensional model only.
-/

import Mathlib
import WCTLean.Models.CurvatureNodalEnergy

namespace WCTLean

open Real Filter Topology MeasureTheory intervalIntegral

noncomputable section

/-! ### L¹ divergence at a simple node -/

/-- **Logarithmic `L¹` lower bound.**  At a simple zero with nonzero
Laplacian there are `δ₀, C > 0` such that for `0 < δ ≤ δ₀` and `0 < ε < δ`,
`∫_{x₀+ε}^{x₀+δ} |Θ_ε[ψ]| ≥ C log(δ/ε)` (`α ≥ 0`). -/
theorem nodal_curvature_L1_lower_bound (ψ ψ' ψ'' : ℝ → ℝ) (x₀ : ℝ)
    (h1 : ∀ x, HasDerivAt ψ (ψ' x) x) (h2 : ∀ x, HasDerivAt ψ' (ψ'' x) x)
    (hc2 : Continuous ψ'') (hzero : ψ x₀ = 0) (hsimple : ψ' x₀ ≠ 0) (hlap : ψ'' x₀ ≠ 0)
    (α : ℝ) (hα : 0 ≤ α) :
    ∃ δ₀ > 0, ∃ C > 0, ∀ δ ε, 0 < δ → δ ≤ δ₀ → 0 < ε → ε < δ →
      C * Real.log (δ / ε) ≤
        ∫ x in (x₀ + ε)..(x₀ + δ), ‖curvatureField (realField ψ) ε α x‖ := by
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
  set K := m * c / (L ^ 2 + 1) with hK_def
  have hK : 0 < K := by positivity
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, K, hK, ?_⟩
  intro δ ε hδ hδδ₀ hε hεδ
  have hcf : ∀ x, curvatureField (realField ψ) ε α x =
      thetaComplex (ψ'' x : ℂ) (ψ x : ℂ) ε α :=
    realField_curvatureField ψ ψ' ψ'' h1 h2 ε α
  have hcont : Continuous fun x => ‖curvatureField (realField ψ) ε α x‖ := by
    simp_rw [hcf]
    exact (continuous_thetaComplex_comp (Complex.continuous_ofReal.comp hc0)
      (Complex.continuous_ofReal.comp hc2) (ne_of_gt hε) α).norm
  -- the comparison function `K / (x - x₀)`
  have hlowInt : ∫ x in (x₀ + ε)..(x₀ + δ), K * (x - x₀)⁻¹ = K * Real.log (δ / ε) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_right (fun x => x⁻¹) x₀]
    simp only [add_sub_cancel_left]
    rw [integral_inv_of_pos hε hδ]
  rw [← hlowInt]
  apply intervalIntegral.integral_mono_on (by linarith)
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have : 0 < x - x₀ := by linarith [hx.1]
    exact this.ne'
  · exact hcont.intervalIntegrable _ _
  · intro x hx
    have ht : 0 < x - x₀ := by linarith [hx.1]
    have hεt : ε ≤ x - x₀ := by linarith [hx.1]
    have hxδ : |x - x₀| ≤ min δ₁ δ₂ := by
      rw [abs_of_pos ht]; linarith [hx.2]
    have hlow := (hb₁ x (hxδ.trans (min_le_left _ _))).1
    have hup := (hb₁ x (hxδ.trans (min_le_left _ _))).2
    have hl := hb₂ x (hxδ.trans (min_le_right _ _))
    rw [abs_of_pos ht] at hlow hup
    rw [hcf, norm_thetaComplex, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    have hD0 : 0 < complexRegularizerDenominator (ψ x : ℂ) ε α := by
      unfold complexRegularizerDenominator
      have h1' : 0 ≤ Complex.normSq (ψ x : ℂ) := Complex.normSq_nonneg _
      have h2' : 0 < ε ^ 2 := by positivity
      have h3' := Real.exp_pos (-2 * α * Complex.normSq (ψ x : ℂ))
      nlinarith [mul_pos h2' h3']
    have hDle : complexRegularizerDenominator (ψ x : ℂ) ε α ≤ (L ^ 2 + 1) * (x - x₀) ^ 2 := by
      have h := complexRegularizerDenominator_le (ψ x : ℂ) ε α hα
      rw [Complex.norm_real, Real.norm_eq_abs] at h
      have hsq : |ψ x| ^ 2 ≤ L ^ 2 * (x - x₀) ^ 2 := by
        calc |ψ x| ^ 2 ≤ (L * (x - x₀)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hup 2
          _ = L ^ 2 * (x - x₀) ^ 2 := by ring
      have hε2 : ε ^ 2 ≤ (x - x₀) ^ 2 := pow_le_pow_left₀ hε.le hεt 2
      nlinarith
    calc K * (x - x₀)⁻¹ = m * (c * (x - x₀)) / ((L ^ 2 + 1) * (x - x₀) ^ 2) := by
          rw [hK_def]; field_simp
      _ ≤ |ψ'' x| * |ψ x| / complexRegularizerDenominator (ψ x : ℂ) ε α :=
          div_le_div₀ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
            (mul_le_mul hl hlow (by positivity) (abs_nonneg _)) hD0 hDle

/-- **No strong `L¹_loc` limit at the node.**  On every interval containing a
simple zero with nonzero Laplacian, `∫_a^b |Θ_ε[ψ]| → +∞` as `ε → 0⁺`. -/
theorem nodal_curvature_L1_tendsto_atTop (ψ ψ' ψ'' : ℝ → ℝ) (x₀ a b : ℝ)
    (h1 : ∀ x, HasDerivAt ψ (ψ' x) x) (h2 : ∀ x, HasDerivAt ψ' (ψ'' x) x)
    (hc2 : Continuous ψ'') (hzero : ψ x₀ = 0) (hsimple : ψ' x₀ ≠ 0) (hlap : ψ'' x₀ ≠ 0)
    (hax : a < x₀) (hxb : x₀ < b) (α : ℝ) (hα : 0 ≤ α) :
    Tendsto (fun ε => ∫ x in a..b, ‖curvatureField (realField ψ) ε α x‖) (𝓝[>] 0) atTop := by
  obtain ⟨δ₀, hδ₀, C, hC, hbound⟩ :=
    nodal_curvature_L1_lower_bound ψ ψ' ψ'' x₀ h1 h2 hc2 hzero hsimple hlap α hα
  have hc0 : Continuous ψ := continuous_iff_continuousAt.2 fun x => (h1 x).continuousAt
  set δ := min δ₀ (b - x₀) with hδ_def
  have hδ : 0 < δ := lt_min hδ₀ (by linarith)
  have hcf : ∀ ε x, curvatureField (realField ψ) ε α x =
      thetaComplex (ψ'' x : ℂ) (ψ x : ℂ) ε α :=
    fun ε => realField_curvatureField ψ ψ' ψ'' h1 h2 ε α
  -- `C log(δ/ε) → ∞`
  have hlog : Tendsto (fun ε : ℝ => C * Real.log (δ / ε)) (𝓝[>] 0) atTop := by
    have hneg : Tendsto (fun ε : ℝ => -Real.log ε) (𝓝[>] 0) atTop :=
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
    have hsum : Tendsto (fun ε : ℝ => Real.log δ + -Real.log ε) (𝓝[>] 0) atTop :=
      tendsto_atTop_add_const_left _ _ hneg
    refine (hsum.const_mul_atTop hC).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [Real.log_div hδ.ne' (ne_of_gt hε)]
    ring
  refine tendsto_atTop_mono' _ ?_ hlog
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds hδ)] with ε hε hεδ
  have hεpos : (0 : ℝ) < ε := hε
  have hεδ' : ε < δ := hεδ
  refine (hbound δ ε hδ (min_le_left _ _) hεpos hεδ').trans ?_
  have hcont : Continuous fun x => ‖curvatureField (realField ψ) ε α x‖ := by
    simp_rw [hcf ε]
    exact (continuous_thetaComplex_comp (Complex.continuous_ofReal.comp hc0)
      (Complex.continuous_ofReal.comp hc2) (ne_of_gt hεpos) α).norm
  have hδb : x₀ + δ ≤ b := by have := min_le_right δ₀ (b - x₀); linarith
  exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) hδb
    (Eventually.of_forall fun x => norm_nonneg _) (hcont.intervalIntegrable _ _)

/-! ### Weak (distributional) limit for the selected regularizer `α = 0` -/

/-- Weight `u = -ψ''φ/(2ψ')` used in the logarithmic integration by parts. -/
def nodalWeight (ψ' ψ'' φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(ψ'' x * φ x) / (2 * ψ' x)

/-- Derivative of `nodalWeight` (quotient rule). -/
def nodalWeightDeriv (ψ' ψ'' ψ''' φ φ' : ℝ → ℝ) (x : ℝ) : ℝ :=
  ((-(ψ''' x * φ x + ψ'' x * φ' x)) * (2 * ψ' x) - (-(ψ'' x * φ x)) * (2 * ψ'' x)) /
    (2 * ψ' x) ^ 2

theorem nodalWeight_hasDerivAt (ψ' ψ'' ψ''' φ φ' : ℝ → ℝ)
    (h2 : ∀ x, HasDerivAt ψ' (ψ'' x) x) (h3 : ∀ x, HasDerivAt ψ'' (ψ''' x) x)
    (hφ : ∀ x, HasDerivAt φ (φ' x) x) {x : ℝ} (hx : ψ' x ≠ 0) :
    HasDerivAt (nodalWeight ψ' ψ'' φ) (nodalWeightDeriv ψ' ψ'' ψ''' φ φ' x) x := by
  have hnum : HasDerivAt (fun y => -(ψ'' y * φ y)) (-(ψ''' x * φ x + ψ'' x * φ' x)) x :=
    ((h3 x).mul (hφ x)).neg
  have hden : HasDerivAt (fun y => 2 * ψ' y) (2 * ψ'' x) x := (h2 x).const_mul 2
  have h2x : 2 * ψ' x ≠ 0 := mul_ne_zero two_ne_zero hx
  exact hnum.div hden h2x

/-- The explicit weak limit `u(b) log ψ(b)² - u(a) log ψ(a)² - ∫ u' log ψ²`. -/
def nodalWeakLimit (ψ ψ' ψ'' ψ''' φ φ' : ℝ → ℝ) (a b : ℝ) : ℝ :=
  nodalWeight ψ' ψ'' φ b * Real.log (ψ b ^ 2) - nodalWeight ψ' ψ'' φ a * Real.log (ψ a ^ 2) -
    ∫ x in a..b, nodalWeightDeriv ψ' ψ'' ψ''' φ φ' x * Real.log (ψ x ^ 2)

/-- A slope floor around a zero gives linear growth away from it. -/
theorem abs_ge_of_slope_floor (ψ ψ' : ℝ → ℝ) (h1 : ∀ x, HasDerivAt ψ (ψ' x) x)
    {a b x₀ c : ℝ} (hslope : ∀ x ∈ Set.Icc a b, c ≤ |ψ' x|) (hx₀ : x₀ ∈ Set.Icc a b)
    (hzero : ψ x₀ = 0) : ∀ x ∈ Set.Icc a b, c * |x - x₀| ≤ |ψ x| := by
  have hc0 : Continuous ψ := continuous_iff_continuousAt.2 fun x => (h1 x).continuousAt
  intro x hx
  rcases lt_trichotomy x x₀ with hlt | heq | hgt
  · obtain ⟨ξ, hξ, hslope'⟩ := exists_hasDerivAt_eq_slope ψ ψ' hlt hc0.continuousOn
      (fun y _ => h1 y)
    have hξab : ξ ∈ Set.Icc a b := ⟨by linarith [hx.1, hξ.1], by linarith [hx₀.2, hξ.2]⟩
    have hpos : 0 < x₀ - x := by linarith
    rw [hzero, zero_sub] at hslope'
    have hψx : |ψ x| = |ψ' ξ| * (x₀ - x) := by
      rw [hslope', abs_div, abs_neg, abs_of_pos hpos]; field_simp
    rw [hψx, abs_sub_comm, abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_right (hslope ξ hξab) hpos.le
  · subst heq; simp [hzero]
  · obtain ⟨ξ, hξ, hslope'⟩ := exists_hasDerivAt_eq_slope ψ ψ' hgt hc0.continuousOn
      (fun y _ => h1 y)
    have hξab : ξ ∈ Set.Icc a b := ⟨by linarith [hx₀.1, hξ.1], by linarith [hx.2, hξ.2]⟩
    have hpos : 0 < x - x₀ := by linarith
    rw [hzero, sub_zero] at hslope'
    have hψx : |ψ x| = |ψ' ξ| * (x - x₀) := by
      rw [hslope', abs_div, abs_of_pos hpos]; field_simp
    rw [hψx, abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_right (hslope ξ hξab) hpos.le

/-- Logarithmic domination: if `c²d² ≤ p²`, `|p| ≤ M`, `0 < ε < 1`, `d ≠ 0`, then
`|log(p² + ε²)| ≤ |log c²| + 2|log d| + |log(M² + 1)|`. -/
theorem log_sq_add_sq_bound {p ε c d M : ℝ} (hd : d ≠ 0) (hc : 0 < c)
    (hlow : c ^ 2 * d ^ 2 ≤ p ^ 2) (hM : |p| ≤ M) (hε0 : 0 < ε) (hε1 : ε < 1) :
    |Real.log (p ^ 2 + ε ^ 2)| ≤
      |Real.log (c ^ 2)| + 2 * |Real.log d| + |Real.log (M ^ 2 + 1)| := by
  have hd2 : 0 < d ^ 2 := by positivity
  have hlowpos : 0 < c ^ 2 * d ^ 2 := by positivity
  have hs_lo : c ^ 2 * d ^ 2 ≤ p ^ 2 + ε ^ 2 := by nlinarith
  have hs_pos : 0 < p ^ 2 + ε ^ 2 := lt_of_lt_of_le hlowpos hs_lo
  have hs_hi : p ^ 2 + ε ^ 2 ≤ M ^ 2 + 1 := by
    have h0 : p ^ 2 ≤ M ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hM 2
    have h1 : ε ^ 2 ≤ 1 := by nlinarith
    linarith
  have hsplit : Real.log (c ^ 2 * d ^ 2) = Real.log (c ^ 2) + 2 * Real.log d := by
    rw [Real.log_mul (by positivity) hd2.ne']
    congr 1
    rw [Real.log_pow]
    push_cast
    ring
  rcases le_or_gt 1 (p ^ 2 + ε ^ 2) with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    have := Real.log_le_log hs_pos hs_hi
    have := le_abs_self (Real.log (M ^ 2 + 1))
    have := abs_nonneg (Real.log (c ^ 2))
    have := abs_nonneg (Real.log d)
    linarith
  · rw [abs_of_neg (Real.log_neg hs_pos h)]
    have hmono := Real.log_le_log hlowpos hs_lo
    rw [hsplit] at hmono
    have := neg_abs_le (Real.log (c ^ 2))
    have := neg_abs_le (Real.log d)
    have := abs_nonneg (Real.log (M ^ 2 + 1))
    linarith

/-- `log(p² + ε²) → log p²` as `ε → 0⁺` when `p ≠ 0`. -/
theorem tendsto_log_sq_add_sq {p : ℝ} (hp : p ≠ 0) :
    Tendsto (fun ε : ℝ => Real.log (p ^ 2 + ε ^ 2)) (𝓝[>] 0) (𝓝 (Real.log (p ^ 2))) := by
  have hcont : Continuous fun ε : ℝ => p ^ 2 + ε ^ 2 := by fun_prop
  have hne : p ^ 2 + (0 : ℝ) ^ 2 ≠ 0 := by
    have : 0 < p ^ 2 := by positivity
    simpa using this.ne'
  have h : Tendsto (fun ε : ℝ => Real.log (p ^ 2 + ε ^ 2)) (𝓝 0)
      (𝓝 (Real.log (p ^ 2 + (0 : ℝ) ^ 2))) :=
    (Real.continuousAt_log hne).tendsto.comp (hcont.tendsto 0)
  rw [show p ^ 2 + (0 : ℝ) ^ 2 = p ^ 2 by ring] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- **Logarithmic integration by parts** for the selected regularizer `α = 0`:
on an interval where `ψ' ≠ 0`, for `ε > 0`,
`∫ Θ_ε φ = [u log(ψ² + ε²)]_a^b - ∫ u' log(ψ² + ε²)`. -/
theorem nodal_ibp_identity (ψ ψ' ψ'' ψ''' φ φ' : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (h1 : ∀ x, HasDerivAt ψ (ψ' x) x) (h2 : ∀ x, HasDerivAt ψ' (ψ'' x) x)
    (h3 : ∀ x, HasDerivAt ψ'' (ψ''' x) x) (hc3 : Continuous ψ''')
    (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hφc : Continuous φ')
    (hψ'ne : ∀ x ∈ Set.Icc a b, ψ' x ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∫ x in a..b, (curvatureField (realField ψ) ε 0 x).re * φ x =
      nodalWeight ψ' ψ'' φ b * Real.log (ψ b ^ 2 + ε ^ 2) -
        nodalWeight ψ' ψ'' φ a * Real.log (ψ a ^ 2 + ε ^ 2) -
        ∫ x in a..b, nodalWeightDeriv ψ' ψ'' ψ''' φ φ' x * Real.log (ψ x ^ 2 + ε ^ 2) := by
  have hc0 : Continuous ψ := continuous_iff_continuousAt.2 fun x => (h1 x).continuousAt
  have hc1 : Continuous ψ' := continuous_iff_continuousAt.2 fun x => (h2 x).continuousAt
  have hc2 : Continuous ψ'' := continuous_iff_continuousAt.2 fun x => (h3 x).continuousAt
  have hφ0 : Continuous φ := continuous_iff_continuousAt.2 fun x => (hφ x).continuousAt
  have hEq : Set.EqOn (fun x => (curvatureField (realField ψ) ε 0 x).re * φ x)
      (fun x => nodalWeight ψ' ψ'' φ x * (2 * ψ x * ψ' x / (ψ x ^ 2 + ε ^ 2)))
      (Set.uIcc a b) := by
    intro x hx
    rw [Set.uIcc_of_le hab.le] at hx
    simp only [nodalWeight]
    rw [realField_curvatureField ψ ψ' ψ'' h1 h2, thetaComplex_ofReal, Complex.ofReal_re,
      complexRegularizerDenominator_ofReal]
    have hp := hψ'ne x hx
    have hD : ψ x * ψ x + ε ^ 2 * Real.exp (-2 * 0 * (ψ x * ψ x)) = ψ x ^ 2 + ε ^ 2 := by
      simp; ring
    rw [hD]
    have hDpos : 0 < ψ x ^ 2 + ε ^ 2 := by positivity
    field_simp
  rw [intervalIntegral.integral_congr hEq]
  have hvd : ∀ x, HasDerivAt (fun y => Real.log (ψ y ^ 2 + ε ^ 2))
      (2 * ψ x * ψ' x / (ψ x ^ 2 + ε ^ 2)) x := by
    intro x
    have hpos : 0 < ψ x ^ 2 + ε ^ 2 := by positivity
    have hf : HasDerivAt (fun y => ψ y ^ 2 + ε ^ 2) (2 * ψ x * ψ' x) x := by
      have := ((h1 x).pow 2).add_const (ε ^ 2)
      convert this using 1; push_cast; ring
    exact hf.log hpos.ne'
  have hu'cont : ContinuousOn (nodalWeightDeriv ψ' ψ'' ψ''' φ φ') (Set.uIcc a b) := by
    unfold nodalWeightDeriv
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    rw [Set.uIcc_of_le hab.le] at hx
    exact pow_ne_zero 2 (mul_ne_zero two_ne_zero (hψ'ne x hx))
  have hcv' : Continuous fun x => 2 * ψ x * ψ' x / (ψ x ^ 2 + ε ^ 2) :=
    Continuous.div (by fun_prop) (by fun_prop) fun x => by positivity
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x hx => nodalWeight_hasDerivAt ψ' ψ'' ψ''' φ φ' h2 h3 hφ
      (hψ'ne x (by rwa [Set.uIcc_of_le hab.le] at hx)))
    (fun x _ => hvd x) hu'cont.intervalIntegrable (hcv'.intervalIntegrable _ _)

/-- **Dominated convergence for the logarithmic term.** -/
theorem nodal_log_integral_tendsto (ψ g : ℝ → ℝ) (a b x₀ c M K : ℝ) (hab : a < b) (hc : 0 < c)
    (hψc : Continuous ψ) (hgc : ContinuousOn g (Set.Icc a b))
    (hK : ∀ x ∈ Set.Icc a b, |g x| ≤ K) (hM : ∀ x ∈ Set.Icc a b, |ψ x| ≤ M)
    (hgrow : ∀ x ∈ Set.Icc a b, c * |x - x₀| ≤ |ψ x|) :
    Tendsto (fun ε => ∫ x in a..b, g x * Real.log (ψ x ^ 2 + ε ^ 2)) (𝓝[>] 0)
      (𝓝 (∫ x in a..b, g x * Real.log (ψ x ^ 2))) := by
  have hae : ∀ᵐ x ∂volume, x ∉ ({x₀} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp (Real.volume_singleton)
  have hIoc : Set.uIoc a b ⊆ Set.Icc a b := by
    rw [Set.uIoc_of_le hab.le]; exact Set.Ioc_subset_Icc_self
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun x => K * (|Real.log (c ^ 2)| + 2 * |Real.log (x - x₀)| + |Real.log (M ^ 2 + 1)|))
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεpos : (0 : ℝ) < ε := hε
    have hcv : Continuous fun x => Real.log (ψ x ^ 2 + ε ^ 2) :=
      Continuous.log (by fun_prop) fun x => by positivity
    exact ((hgc.mono hIoc).aestronglyMeasurable measurableSet_uIoc).mul
      hcv.aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    filter_upwards [hae] with x hx hxab
    have hxI : x ∈ Set.Icc a b := hIoc hxab
    have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
    have hlow : c ^ 2 * (x - x₀) ^ 2 ≤ ψ x ^ 2 := by
      have h0 : 0 ≤ c * |x - x₀| := by positivity
      calc c ^ 2 * (x - x₀) ^ 2 = (c * |x - x₀|) ^ 2 := by rw [mul_pow, sq_abs]
        _ ≤ |ψ x| ^ 2 := pow_le_pow_left₀ h0 (hgrow x hxI) 2
        _ = ψ x ^ 2 := sq_abs _
    have hlog := log_sq_add_sq_bound hd hc hlow (hM x hxI) hε.1 hε.2
    show ‖g x * Real.log (ψ x ^ 2 + ε ^ 2)‖ ≤
      K * (|Real.log (c ^ 2)| + 2 * |Real.log (x - x₀)| + |Real.log (M ^ 2 + 1)|)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hK x hxI) hlog (abs_nonneg _) ((abs_nonneg _).trans (hK x hxI))
  · have hlog0 : IntervalIntegrable (fun x => Real.log (x - x₀)) volume a b := by
      have h := (intervalIntegrable_log' (a := a - x₀) (b := b - x₀)).comp_sub_right x₀
      simpa using h
    have hc1 : IntervalIntegrable (fun _ : ℝ => |Real.log (c ^ 2)|) volume a b :=
      intervalIntegral.intervalIntegrable_const
    have hc2 : IntervalIntegrable (fun x => 2 * |Real.log (x - x₀)|) volume a b :=
      hlog0.abs.const_mul 2
    have hc3 : IntervalIntegrable (fun _ : ℝ => |Real.log (M ^ 2 + 1)|) volume a b :=
      intervalIntegral.intervalIntegrable_const
    exact ((hc1.add hc2).add hc3).const_mul K
  · filter_upwards [hae] with x hx hxab
    have hxI : x ∈ Set.Icc a b := hIoc hxab
    have hψx : ψ x ≠ 0 := by
      intro h
      have := hgrow x hxI
      rw [h, abs_zero] at this
      have : 0 < c * |x - x₀| := mul_pos hc (abs_pos.mpr (sub_ne_zero.mpr hx))
      linarith
    exact (tendsto_log_sq_add_sq hψx).const_mul (g x)

/-- **Weak limit at a simple node.**  For the regularizer `α = 0`, a real
`C³` field with a zero `x₀ ∈ (a, b)` and slope floor `|ψ'| ≥ c > 0` on
`[a, b]`, and every `C¹` test function `φ`,
`∫_a^b Θ_ε[ψ] φ → nodalWeakLimit` as `ε → 0⁺`. -/
theorem nodal_curvature_weak_limit (ψ ψ' ψ'' ψ''' φ φ' : ℝ → ℝ) (a b x₀ c : ℝ)
    (h1 : ∀ x, HasDerivAt ψ (ψ' x) x) (h2 : ∀ x, HasDerivAt ψ' (ψ'' x) x)
    (h3 : ∀ x, HasDerivAt ψ'' (ψ''' x) x) (hc3 : Continuous ψ''')
    (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hφc : Continuous φ')
    (hax : a < x₀) (hxb : x₀ < b) (hzero : ψ x₀ = 0) (hc : 0 < c)
    (hslope : ∀ x ∈ Set.Icc a b, c ≤ |ψ' x|) :
    Tendsto (fun ε => ∫ x in a..b, (curvatureField (realField ψ) ε 0 x).re * φ x) (𝓝[>] 0)
      (𝓝 (nodalWeakLimit ψ ψ' ψ'' ψ''' φ φ' a b)) := by
  have hab : a < b := hax.trans hxb
  have hc0 : Continuous ψ := continuous_iff_continuousAt.2 fun x => (h1 x).continuousAt
  have hc1 : Continuous ψ' := continuous_iff_continuousAt.2 fun x => (h2 x).continuousAt
  have hc2 : Continuous ψ'' := continuous_iff_continuousAt.2 fun x => (h3 x).continuousAt
  have hφ0 : Continuous φ := continuous_iff_continuousAt.2 fun x => (hφ x).continuousAt
  have hgrow := abs_ge_of_slope_floor ψ ψ' h1 hslope ⟨hax.le, hxb.le⟩ hzero
  have hψ'ne : ∀ x ∈ Set.Icc a b, ψ' x ≠ 0 := fun x hx h => by
    have := hslope x hx; rw [h, abs_zero] at this; linarith
  have hψne : ∀ x ∈ Set.Icc a b, x ≠ x₀ → ψ x ≠ 0 := by
    intro x hx hne h
    have := hgrow x hx
    rw [h, abs_zero] at this
    have : 0 < c * |x - x₀| := mul_pos hc (abs_pos.mpr (sub_ne_zero.mpr hne))
    linarith
  have hψa : ψ a ≠ 0 := hψne a ⟨le_rfl, hab.le⟩ hax.ne
  have hψb : ψ b ≠ 0 := hψne b ⟨hab.le, le_rfl⟩ hxb.ne'
  obtain ⟨M, hM⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (hc0.continuousOn (s := Set.Icc a b))
  have hu'cont : ContinuousOn (nodalWeightDeriv ψ' ψ'' ψ''' φ φ') (Set.Icc a b) := by
    unfold nodalWeightDeriv
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    exact pow_ne_zero 2 (mul_ne_zero two_ne_zero (hψ'ne x hx))
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hu'cont
  have hint := nodal_log_integral_tendsto ψ (nodalWeightDeriv ψ' ψ'' ψ''' φ φ') a b x₀ c M K
    hab hc hc0 hu'cont (fun x hx => by simpa [Real.norm_eq_abs] using hK x hx)
    (fun x hx => by simpa [Real.norm_eq_abs] using hM x hx) hgrow
  have hlim := (((tendsto_log_sq_add_sq hψb).const_mul (nodalWeight ψ' ψ'' φ b)).sub
    ((tendsto_log_sq_add_sq hψa).const_mul (nodalWeight ψ' ψ'' φ a))).sub hint
  unfold nodalWeakLimit
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (nodal_ibp_identity ψ ψ' ψ'' ψ''' φ φ' a b hab h1 h2 h3 hc3 hφ hφc hψ'ne hε).symm

/-! ### Concrete witness: `ψ = cos x - 1/2` on `[π/6, π/2]` -/

/-- **Nodal trichotomy for a concrete smooth periodic field.**  For
`ψ = cos x - 1/2` (simple node at `π/3`, `ψ''(π/3) = -1/2`) on `[π/6, π/2]`:
the curvature energy and the `L¹` norm diverge as `ε → 0⁺` (any `α ≥ 0`),
while for `α = 0` the distributional pairing with every `C¹` test function
converges. -/
theorem cos_sub_half_nodal_trichotomy (α : ℝ) (hα : 0 ≤ α) (φ φ' : ℝ → ℝ)
    (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hφc : Continuous φ') :
    Tendsto (fun ε => ∫ x in (π / 6)..(π / 2),
        ‖curvatureField (realField fun x => Real.cos x - 1 / 2) ε α x‖ ^ 2) (𝓝[>] 0) atTop ∧
      Tendsto (fun ε => ∫ x in (π / 6)..(π / 2),
        ‖curvatureField (realField fun x => Real.cos x - 1 / 2) ε α x‖) (𝓝[>] 0) atTop ∧
      ∃ L : ℝ, Tendsto (fun ε => ∫ x in (π / 6)..(π / 2),
        (curvatureField (realField fun x => Real.cos x - 1 / 2) ε 0 x).re * φ x)
        (𝓝[>] 0) (𝓝 L) := by
  have h1 : ∀ x, HasDerivAt (fun x => Real.cos x - 1 / 2) (-Real.sin x) x :=
    fun x => (Real.hasDerivAt_cos x).sub_const _
  have h2 : ∀ x, HasDerivAt (fun x => -Real.sin x) (-Real.cos x) x :=
    fun x => (Real.hasDerivAt_sin x).neg
  have h3 : ∀ x, HasDerivAt (fun x => -Real.cos x) (Real.sin x) x := by
    intro x; simpa using (Real.hasDerivAt_cos x).neg
  have hzero : Real.cos (π / 3) - 1 / 2 = 0 := by rw [Real.cos_pi_div_three]; ring
  have hsin3 : 0 < Real.sin (π / 3) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hsimple : -Real.sin (π / 3) ≠ 0 := by linarith
  have hlap : -Real.cos (π / 3) ≠ 0 := by rw [Real.cos_pi_div_three]; norm_num
  have hpi := Real.pi_pos
  have ha : π / 6 < π / 3 := by linarith
  have hb : π / 3 < π / 2 := by linarith
  refine ⟨nodal_curvature_energy_tendsto_atTop _ _ _ (π / 3) (π / 6) (π / 2) h1 h2
      Real.continuous_cos.neg hzero hsimple hlap ha hb α hα,
    nodal_curvature_L1_tendsto_atTop _ _ _ (π / 3) (π / 6) (π / 2) h1 h2
      Real.continuous_cos.neg hzero hsimple hlap ha hb α hα, ?_⟩
  refine ⟨_, nodal_curvature_weak_limit (fun x => Real.cos x - 1 / 2) (fun x => -Real.sin x)
    (fun x => -Real.cos x) Real.sin φ φ' (π / 6) (π / 2) (π / 3) (1 / 2) h1 h2 h3
    Real.continuous_sin hφ hφc ha hb hzero (by norm_num) ?_⟩
  -- slope floor `|sin x| ≥ 1/2` on `[π/6, π/2]`
  intro x hx
  have hsx : Real.sin (π / 6) ≤ Real.sin x := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hx.2 hx.1
  rw [Real.sin_pi_div_six] at hsx
  rw [abs_neg, abs_of_pos (by linarith)]
  exact hsx

end

end WCTLean
