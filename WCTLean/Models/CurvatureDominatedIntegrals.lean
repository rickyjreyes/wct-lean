import WCTLean.Models.CurvatureGlobalEnvelope

/-!
# Conditional dominated convergence for the corrected M2/E17 curvature integral

Proves actual Bochner integral and square-energy-density convergence for the
source-matched complex curvature under an independently integrable majorant
built from the unregularized quotient. The integrability and measurability
premises are explicit; they are *not* claimed for every WCT/PDE solution.

At nodes the quotient uses Lean's totalized zero division; we do not
reinterpret it as a classical singular quotient at a zero of psi.
These results do not imply weak-PDE convergence, or any claim that a
self-bound field exists.
-/

namespace WCTLean
open MeasureTheory Filter Topology
open scoped ENNReal

/-- For arbitrary nodal sets, the corrected curvature has the same
regularization limit as the totalized singular quotient, provided the
latter has an integrable absolute majorant. The supplied measurability
and MemLp hypotheses do not assert they hold for arbitrary WCT states. -/
theorem curvature_integral_dominated_limit
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (psi lapPsi : X → ℂ) (alpha : ℝ)
    (hm : AEStronglyMeasurable psi mu)
    (hlap : AEStronglyMeasurable lapPsi mu)
    (hquot : MemLp (fun x => lapPsi x / psi x) 1 mu)
    (hbound : Integrable (fun x => ‖lapPsi x / psi x‖) mu) :
    Tendsto (fun epsilon : ℝ =>
      ∫ x, thetaComplex (lapPsi x) (psi x) epsilon alpha ∂mu)
      (nhds 0) (nhds (∫ x, -(lapPsi x / psi x) ∂mu)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun x => ‖lapPsi x / psi x‖)
  · exact Filter.Eventually.of_forall (fun epsilon =>
      (theta_no_gap_memLp mu 1 psi lapPsi epsilon alpha hm hlap hquot).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall (fun epsilon =>
      Filter.Eventually.of_forall (fun x =>
        theta_no_gap_domination (lapPsi x) (psi x) epsilon alpha))
  · exact hbound
  · apply Filter.Eventually.of_forall
    intro x
    by_cases hx : psi x = 0
    · simp [hx, thetaComplex_field_node]
    · exact thetaComplex_nonzero_limit (lapPsi x) (psi x) alpha hx

/-- The integral of the actual squared complex curvature converges to
the squared norm of the totalized unregularized quotient, if that
quantity has an independently integrable majorant. This is an
energy-density integral theorem, not a convergence theorem for the
complete WCT Hamiltonian or its Euler-Lagrange PDE. -/
theorem curvature_squared_integral_dominated_limit
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (psi lapPsi : X → ℂ) (alpha : ℝ)
    (hm : AEStronglyMeasurable psi mu)
    (hlap : AEStronglyMeasurable lapPsi mu)
    (hquot : MemLp (fun x => lapPsi x / psi x) 2 mu)
    (hbound : Integrable (fun x => ‖lapPsi x / psi x‖ ^ 2) mu) :
    Tendsto (fun epsilon : ℝ =>
      ∫ x, ‖thetaComplex (lapPsi x) (psi x) epsilon alpha‖ ^ 2 ∂mu)
      (nhds 0) (nhds (∫ x, ‖lapPsi x / psi x‖ ^ 2 ∂mu)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun x => ‖lapPsi x / psi x‖ ^ 2)
  · apply Filter.Eventually.of_forall
    intro epsilon
    have hmeas := (theta_no_gap_memLp mu 2 psi lapPsi epsilon alpha hm hlap hquot).aestronglyMeasurable
    have hc : Continuous (fun z : ℂ => (‖z‖ ^ 2 : ℝ)) := by fun_prop
    exact hc.comp_aestronglyMeasurable hmeas
  · apply Filter.Eventually.of_forall
    intro epsilon
    apply Filter.Eventually.of_forall
    intro x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] using
      theta_no_gap_energy_majorant (lapPsi x) (psi x) epsilon alpha
  · exact hbound
  · apply Filter.Eventually.of_forall
    intro x
    have hθ : Tendsto (fun epsilon : ℝ =>
        thetaComplex (lapPsi x) (psi x) epsilon alpha)
        (nhds 0) (nhds (-(lapPsi x / psi x))) := by
      by_cases hx : psi x = 0
      · simp [hx, thetaComplex_field_node]
      · exact thetaComplex_nonzero_limit (lapPsi x) (psi x) alpha hx
    have hc : Continuous (fun z : ℂ => (‖z‖ ^ 2 : ℝ)) := by fun_prop
    simpa only [norm_neg] using (hc.continuousAt.tendsto.comp hθ)

end WCTLean
