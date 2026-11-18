import WCTLean.Models.CurvatureLpLimit

/-!
# No-gap domination for the unchanged corrected complex curvature

The regularized quotient is globally bounded in modulus by the
totalized unregularized quotient |Δψ/ψ| at every point of a supplied
complex field, even on the zero set. At a node, both the corrected
numerator and the totalized quotient vanish. The conclusion is
independent of epsilon and alpha because the regulator adds a
nonnegative term to the squared-modulus denominator.

This provides a real majorant for dominated-convergence arguments
without a uniform positive field gap. It does NOT assert that this
majorant is integrable for arbitrary WCT solutions, nor that an
arbitrary singular quotient has a classical value at a node. No
global nonlinear PDE or energy limit follows without separately
proved measurability/integrability and weak-form control.
-/

namespace WCTLean

/-- Exact pointwise domination by the (totalized) unregularized complex
quotient, including field nodes and with no global positive gap. -/
theorem theta_no_gap_domination
    (lapPsi psi : ℂ) (epsilon alpha : ℝ) :
    ‖thetaComplex lapPsi psi epsilon alpha‖ ≤ ‖lapPsi / psi‖ := by
  by_cases hpsi : psi = 0
  · subst psi
    simp [thetaComplex, complexRegularizedReciprocal]
  · have hn : 0 < ‖psi‖ := norm_pos_iff.mpr hpsi
    have hb := theta_nonnodal_uniform_bound
      lapPsi psi epsilon alpha ‖psi‖ hn (le_refl _)
    calc
      ‖thetaComplex lapPsi psi epsilon alpha‖
          ≤ (1 / ‖psi‖) * ‖lapPsi‖ := hb
      _ = ‖lapPsi / psi‖ := by
        rw [norm_div]
        ring

/-- Uniform majorant for the pointwise squared curvature energy. This
does not claim the majorant is integrable for arbitrary fields. -/
theorem theta_no_gap_energy_majorant
    (lapPsi psi : ℂ) (epsilon alpha : ℝ) :
    ‖thetaComplex lapPsi psi epsilon alpha‖ ^ 2 ≤
      ‖lapPsi / psi‖ ^ 2 := by
  exact pow_le_pow_left₀ (norm_nonneg _)
    (theta_no_gap_domination lapPsi psi epsilon alpha) 2

/-- Uniform majorant for the regulator-removal error, valid even at nodes
with Lean's zero-division convention. Integrable domination is a separate
hypothesis in subsequent Lp or energy-limit arguments. -/
theorem theta_no_gap_error_majorant
    (lapPsi psi : ℂ) (epsilon alpha : ℝ) :
    ‖thetaComplex lapPsi psi epsilon alpha -
        thetaComplex lapPsi psi 0 alpha‖ ≤ 2 * ‖lapPsi / psi‖ := by
  calc
    ‖thetaComplex lapPsi psi epsilon alpha -
        thetaComplex lapPsi psi 0 alpha‖
      ≤ ‖thetaComplex lapPsi psi epsilon alpha‖ +
          ‖thetaComplex lapPsi psi 0 alpha‖ := norm_sub_le _ _
    _ ≤ ‖lapPsi / psi‖ + ‖lapPsi / psi‖ :=
      add_le_add (theta_no_gap_domination lapPsi psi epsilon alpha)
        (theta_no_gap_domination lapPsi psi 0 alpha)
    _ = 2 * ‖lapPsi / psi‖ := by ring

/-- An exact no-gap Lp seminorm majorant. This is independent of p and
of the measure space, and needs no claim about the near-node denominator. -/
theorem theta_no_gap_eLpNorm_le
    {X : Type*} [MeasurableSpace X] (mu : MeasureTheory.Measure X)
    (p : ℝ≥0∞) (psi lapPsi : X → ℂ) (epsilon alpha : ℝ) :
    MeasureTheory.eLpNorm
      (fun x => thetaComplex (lapPsi x) (psi x) epsilon alpha) p mu ≤
      MeasureTheory.eLpNorm (fun x => lapPsi x / psi x) p mu := by
  apply MeasureTheory.eLpNorm_mono_ae
  filter_upwards [] with x
  exact theta_no_gap_domination (lapPsi x) (psi x) epsilon alpha

/-- The actual corrected curvature belongs to the common Lp space
whenever the singular quotient is in Lp and the supplied field and
Laplacian are a.e. strongly measurable. No uniform nonzero-field gap
is needed. This does not claim all WCT states satisfy the Lp premise. -/
theorem theta_no_gap_memLp
    {X : Type*} [MeasurableSpace X] (mu : MeasureTheory.Measure X)
    (p : ℝ≥0∞) (psi lapPsi : X → ℂ) (epsilon alpha : ℝ)
    (hm : MeasureTheory.AEStronglyMeasurable psi mu)
    (hlap : MeasureTheory.AEStronglyMeasurable lapPsi mu)
    (hquot : MeasureTheory.MemLp (fun x => lapPsi x / psi x) p mu) :
    MeasureTheory.MemLp
      (fun x => thetaComplex (lapPsi x) (psi x) epsilon alpha) p mu := by
  have hden : MeasureTheory.AEStronglyMeasurable
      (fun x => ((complexRegularizerDenominator (psi x) epsilon alpha : ℝ) : ℂ)) mu := by
    have hc : Continuous
        (fun z : ℂ => ((complexRegularizerDenominator z epsilon alpha : ℝ) : ℂ)) := by
      unfold complexRegularizerDenominator
      fun_prop
    exact hc.comp_aestronglyMeasurable hm
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun x => thetaComplex (lapPsi x) (psi x) epsilon alpha) mu := by
    exact (hlap.aemeasurable.neg.mul
      ((continuous_star.measurable.comp_aemeasurable hm.aemeasurable).div
        hden.aemeasurable)).aestronglyMeasurable
  apply hquot.of_le_mul hmeas
  filter_upwards [] with x
  simpa only [one_mul] using theta_no_gap_domination (lapPsi x) (psi x) epsilon alpha


end WCTLean
