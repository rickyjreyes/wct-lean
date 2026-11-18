import WCTLean.Models.ComplexCurvatureLimit

/-!
# Quantitative Lp convergence of the maintained complex curvature

For alpha >= 0 and an a.e. field gap |psi| >= delta > 0, the reciprocal
error is at most epsilon^2/delta^3. The full curvature error has this
bound times the Lp seminorm of the supplied Laplacian, including L2 and
L-infinity. A global positive field gap is incompatible with finite mass
on R^d; applications must justify it on a suitable restricted measure.
No passage across nodes, energy convergence or PDE limit is asserted.
-/
namespace WCTLean
open MeasureTheory Filter Topology
open scoped ENNReal

theorem theta_nonnodal_uniform_bound
    (lapPsi psi : ℂ) (epsilon alpha delta : ℝ)
    (hd : 0 < delta) (hpsi : delta ≤ ‖psi‖) :
    ‖thetaComplex lapPsi psi epsilon alpha‖ ≤ (1 / delta) * ‖lapPsi‖ := by
  let r := ‖psi‖
  let D := complexRegularizerDenominator psi epsilon alpha
  have hr : 0 < r := lt_of_lt_of_le hd hpsi
  have hD : r ^ 2 ≤ D := by
    dsimp [D, complexRegularizerDenominator, r]
    rw [Complex.normSq_eq_norm_sq]
    have := mul_nonneg (sq_nonneg epsilon)
      (Real.exp_pos (-2 * alpha * ‖psi‖ ^ 2)).le
    linarith
  have hp : 0 < D := lt_of_lt_of_le (sq_pos_of_pos hr) hD
  have hn : ‖complexRegularizedReciprocal psi epsilon alpha‖ = r / D := by
    simp [complexRegularizedReciprocal, D, r, abs_of_pos hp]
  have hb : r / D ≤ 1 / delta := by
    apply (div_le_div_iff₀ hp hd).mpr
    have : r * delta ≤ r ^ 2 := by nlinarith
    nlinarith
  simpa only [thetaComplex, norm_mul, norm_neg, hn, mul_comm] using
    mul_le_mul_of_nonneg_right hb (norm_nonneg lapPsi)

theorem theta_regularization_memLp
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (p : ℝ≥0∞)
    (psi lapPsi : X → ℂ) (epsilon alpha delta : ℝ)
    (hd : 0 < delta) (hpsi : ∀ᵐ x ∂mu, delta ≤ ‖psi x‖)
    (hm : AEStronglyMeasurable psi mu) (hlap : MemLp lapPsi p mu) :
    MemLp (fun x => thetaComplex (lapPsi x) (psi x) epsilon alpha) p mu := by
  have hden : AEStronglyMeasurable
      (fun x => (complexRegularizerDenominator (psi x) epsilon alpha : ℂ)) mu := by
    have hc : Continuous (fun z : ℂ => (complexRegularizerDenominator z epsilon alpha : ℂ)) := by
      unfold complexRegularizerDenominator
      fun_prop
    exact hc.comp_aestronglyMeasurable hm
  have hmeas : AEStronglyMeasurable
      (fun x => thetaComplex (lapPsi x) (psi x) epsilon alpha) mu := by
    exact (hlap.aestronglyMeasurable.aemeasurable.neg.mul
      ((continuous_star.measurable.comp_aemeasurable hm.aemeasurable).div
        hden.aemeasurable)).aestronglyMeasurable
  apply hlap.of_le_mul hmeas
  filter_upwards [hpsi] with x hx
  exact theta_nonnodal_uniform_bound (lapPsi x) (psi x) epsilon alpha delta hd hx

theorem reciprocal_regularization_error_le
    (psi : ℂ) (epsilon alpha delta : ℝ)
    (ha : 0 ≤ alpha) (hd : 0 < delta) (hpsi : delta ≤ ‖psi‖) :
    ‖complexRegularizedReciprocal psi epsilon alpha -
      complexRegularizedReciprocal psi 0 alpha‖ ≤ epsilon ^ 2 / delta ^ 3 := by
  let r := ‖psi‖
  let q := epsilon ^ 2 * Real.exp (-2 * alpha * Complex.normSq psi)
  let D := complexRegularizerDenominator psi epsilon alpha
  have hr : 0 < r := lt_of_lt_of_le hd hpsi
  have hq : 0 ≤ q := mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hqeps : q ≤ epsilon ^ 2 := by
    have he : Real.exp (-2 * alpha * Complex.normSq psi) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [Complex.normSq_nonneg psi]
    exact (mul_le_mul_of_nonneg_left he (sq_nonneg epsilon)).trans_eq (mul_one _)
  have hD : D = r ^ 2 + q := by
    simp only [D, complexRegularizerDenominator, Complex.normSq_eq_norm_sq, r, q]
  have hDpos : 0 < D := by rw [hD]; positivity
  have hsq : Complex.normSq psi ≠ 0 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_ne_zero 2 hr.ne'
  have hdc : (D : ℂ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hsc : (Complex.normSq psi : ℂ) ≠ 0 := by exact_mod_cast hsq
  have halg : complexRegularizedReciprocal psi epsilon alpha -
      complexRegularizedReciprocal psi 0 alpha =
      -(star psi * (q : ℂ)) / ((D : ℂ) * (Complex.normSq psi : ℂ)) := by
    unfold complexRegularizedReciprocal
    rw [complexRegularizerDenominator_zero_epsilon]
    change star psi / (D : ℂ) - star psi / (Complex.normSq psi : ℂ) = _
    field_simp
    simp only [D, q, complexRegularizerDenominator, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  rw [halg]
  have herr :
      ‖-(star psi * (q : ℂ)) / ((D : ℂ) * (Complex.normSq psi : ℂ))‖ =
      q / (D * r) := by
    rw [norm_div, norm_neg, norm_mul, norm_star, norm_mul,
      Complex.norm_real, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hq, abs_of_pos hDpos, abs_of_nonneg (Complex.normSq_nonneg psi),
      Complex.normSq_eq_norm_sq]
    change r * q / (D * r ^ 2) = q / (D * r)
    field_simp
  rw [herr]
  have hprod : delta ^ 3 ≤ D * r := by
    calc delta ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hd.le hpsi 3
      _ ≤ D * r := by rw [hD]; nlinarith [mul_nonneg hq hr.le]
  exact (div_le_div_of_nonneg_right hqeps (mul_pos hDpos hr).le).trans
    (div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hd 3) hprod)

theorem theta_regularization_error_le
    (lapPsi psi : ℂ) (epsilon alpha delta : ℝ)
    (ha : 0 ≤ alpha) (hd : 0 < delta) (hpsi : delta ≤ ‖psi‖) :
    ‖thetaComplex lapPsi psi epsilon alpha - thetaComplex lapPsi psi 0 alpha‖ ≤
      (epsilon ^ 2 / delta ^ 3) * ‖lapPsi‖ := by
  unfold thetaComplex
  rw [← mul_sub, norm_mul, norm_neg]
  calc ‖lapPsi‖ * ‖complexRegularizedReciprocal psi epsilon alpha -
        complexRegularizedReciprocal psi 0 alpha‖ ≤
      ‖lapPsi‖ * (epsilon ^ 2 / delta ^ 3) :=
        mul_le_mul_of_nonneg_left
          (reciprocal_regularization_error_le psi epsilon alpha delta ha hd hpsi)
          (norm_nonneg _)
    _ = _ := mul_comm _ _

theorem theta_regularization_eLpNorm_le
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (p : ℝ≥0∞)
    (psi lapPsi : X → ℂ) (epsilon alpha delta : ℝ)
    (ha : 0 ≤ alpha) (hd : 0 < delta)
    (hpsi : ∀ᵐ x ∂mu, delta ≤ ‖psi x‖) :
    eLpNorm (fun x => thetaComplex (lapPsi x) (psi x) epsilon alpha -
      thetaComplex (lapPsi x) (psi x) 0 alpha) p mu ≤
      ENNReal.ofReal (epsilon ^ 2 / delta ^ 3) * eLpNorm lapPsi p mu := by
  let C := epsilon ^ 2 / delta ^ 3
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc _ ≤ eLpNorm (C • lapPsi) p mu := by
        apply eLpNorm_mono_ae
        filter_upwards [hpsi] with x hx
        simpa only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
          using theta_regularization_error_le (lapPsi x) (psi x) epsilon alpha delta ha hd hx
    _ = _ := by
        rw [eLpNorm_const_smul]
        simp only [Real.enorm_eq_ofReal_abs, abs_of_nonneg hC, C]

theorem theta_regularization_tendsto_eLpNorm_zero
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (p : ℝ≥0∞)
    (psi lapPsi : X → ℂ) (alpha delta : ℝ)
    (ha : 0 ≤ alpha) (hd : 0 < delta)
    (hpsi : ∀ᵐ x ∂mu, delta ≤ ‖psi x‖) (hlap : MemLp lapPsi p mu) :
    Tendsto (fun epsilon : ℝ =>
      eLpNorm (fun x => thetaComplex (lapPsi x) (psi x) epsilon alpha -
        thetaComplex (lapPsi x) (psi x) 0 alpha) p mu) (nhds 0) (nhds 0) := by
  have hC : Tendsto (fun epsilon : ℝ => ENNReal.ofReal (epsilon ^ 2 / delta ^ 3))
      (nhds 0) (nhds 0) := by
    have hreal : Tendsto (fun epsilon : ℝ => epsilon ^ 2 / delta ^ 3)
        (nhds 0) (nhds 0) := by
      convert ((continuous_id.pow 2).div_const (delta ^ 3)).continuousAt.tendsto using 1 <;> simp
    simpa using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hbound : Tendsto
      (fun epsilon : ℝ => ENNReal.ofReal (epsilon ^ 2 / delta ^ 3) * eLpNorm lapPsi p mu)
      (nhds 0) (nhds 0) := by
    simpa using ENNReal.Tendsto.mul_const hC (Or.inr hlap.eLpNorm_lt_top.ne)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ => bot_le) (fun epsilon =>
      theta_regularization_eLpNorm_le mu p psi lapPsi epsilon alpha delta ha hd hpsi)

theorem theta_regularization_tendsto_unregularized
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (p : ℝ≥0∞)
    (psi lapPsi : X → ℂ) (alpha delta : ℝ)
    (ha : 0 ≤ alpha) (hd : 0 < delta)
    (hpsi : ∀ᵐ x ∂mu, delta ≤ ‖psi x‖) (hlap : MemLp lapPsi p mu) :
    Tendsto (fun epsilon : ℝ =>
      eLpNorm (fun x => thetaComplex (lapPsi x) (psi x) epsilon alpha -
        (-(lapPsi x / psi x))) p mu) (nhds 0) (nhds 0) := by
  have heq (epsilon : ℝ) :
      eLpNorm (fun x => thetaComplex (lapPsi x) (psi x) epsilon alpha -
        (-(lapPsi x / psi x))) p mu =
      eLpNorm (fun x => thetaComplex (lapPsi x) (psi x) epsilon alpha -
        thetaComplex (lapPsi x) (psi x) 0 alpha) p mu := by
    apply eLpNorm_congr_ae
    filter_upwards [hpsi] with x hx
    have hn : psi x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hd hx)
    rw [thetaComplex_zero_epsilon (lapPsi x) (psi x) alpha hn]
  simp_rw [heq]
  exact theta_regularization_tendsto_eLpNorm_zero mu p psi lapPsi alpha delta ha hd hpsi hlap
end WCTLean
