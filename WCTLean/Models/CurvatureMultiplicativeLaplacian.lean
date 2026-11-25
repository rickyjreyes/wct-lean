import WCTLean.Models.CurvatureDominatedIntegrals

/-!
# A PDE-structured sufficient condition for the singular quotient (#22)

For a *supplied* multiplicative-Laplacian relation
  lapPsi(x) = V(x) * psi(x),
the totalized singular quotient is bounded pointwise by |V|, including
nodes, and inherits its Lp integrability. Consequently the source-matched
corrected complex curvature has an epsilon-uniform Lp bound.

Unlike assuming `MemLp (lapPsi / psi)` directly, this obtains the majorant
from a mathematically explicit PDE relation and an integrable potential.
It does **not** prove that the maintained fourth-order WCT equation has
this form, that V is integrable for arbitrary WCT solutions, or that
regularized nonlinear PDE solutions converge as epsilon -> 0.
-/

noncomputable section

namespace WCTLean
open MeasureTheory
open scoped ENNReal

/-- An exact multiplicative Laplacian has a quotient bounded by the
potential even at nodes, where Lean's totalized division returns zero. -/
theorem multiplicative_laplacian_quotient_bound
    (V psi : ℂ) :
    ‖(V * psi) / psi‖ ≤ ‖V‖ := by
  by_cases hz : psi = 0
  · simp [hz]
  · have heq : (V * psi) / psi = V := by
      field_simp [hz]
    simp [heq]

/-- For any measure space and exponent, a multiplicative Laplacian with
an Lp potential automatically has an Lp totalized quotient. No
positive lower bound on the field amplitude is required. -/
theorem multiplicative_laplacian_quotient_memLp
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (p : ℝ≥0∞)
    (psi V : X → ℂ)
    (hmpsi : AEStronglyMeasurable psi mu)
    (hV : MemLp V p mu) :
    MemLp (fun x => (V x * psi x) / psi x) p mu := by
  have hmeas : AEStronglyMeasurable
      (fun x => (V x * psi x) / psi x) mu := by
    exact ((hV.aestronglyMeasurable.aemeasurable.mul hmpsi.aemeasurable).div
      hmpsi.aemeasurable).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂mu,
      ‖(V x * psi x) / psi x‖ ≤ (1 : ℝ) * ‖V x‖ := by
    filter_upwards [] with x
    simpa only [one_mul] using multiplicative_laplacian_quotient_bound (V x) (psi x)
  exact hV.of_le_mul hmeas hbound

/-- The corrected M2/E17 complex curvature has a uniform eLpNorm
bound directly from the supplied multiplicative-Laplacian coefficient. -/
theorem theta_multiplicative_laplacian_eLpNorm_le
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (p : ℝ≥0∞)
    (psi V : X → ℂ) (epsilon alpha : ℝ) :
    eLpNorm (fun x => thetaComplex (V x * psi x) (psi x) epsilon alpha) p mu ≤
      eLpNorm V p mu := by
  calc
    eLpNorm (fun x => thetaComplex (V x * psi x) (psi x) epsilon alpha) p mu
        ≤ eLpNorm (fun x => (V x * psi x) / psi x) p mu :=
          theta_no_gap_eLpNorm_le mu p psi (fun x => V x * psi x) epsilon alpha
    _ ≤ eLpNorm V p mu := by
      apply eLpNorm_mono_ae
      filter_upwards [] with x
      exact multiplicative_laplacian_quotient_bound (V x) (psi x)

/-- The regularized curvature lies in Lp when the multiplicative
coefficient V does, with no independent singular-quotient hypothesis. -/
theorem theta_multiplicative_laplacian_memLp
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (p : ℝ≥0∞)
    (psi V : X → ℂ) (epsilon alpha : ℝ)
    (hmpsi : AEStronglyMeasurable psi mu)
    (hV : MemLp V p mu) :
    MemLp (fun x => thetaComplex (V x * psi x) (psi x) epsilon alpha) p mu := by
  have hlap : AEStronglyMeasurable (fun x => V x * psi x) mu := by
    exact (hV.aestronglyMeasurable.aemeasurable.mul
      hmpsi.aemeasurable).aestronglyMeasurable
  exact theta_no_gap_memLp mu p psi (fun x => V x * psi x)
    epsilon alpha hmpsi hlap
    (multiplicative_laplacian_quotient_memLp mu p psi V hmpsi hV)

/-- The same sufficient condition dominates the local squared
curvature density, not merely its first power. -/
theorem theta_multiplicative_laplacian_energy_bound
    (V psi : ℂ) (epsilon alpha : ℝ) :
    ‖thetaComplex (V * psi) psi epsilon alpha‖ ^ 2 ≤ ‖V‖ ^ 2 := by
  calc
    ‖thetaComplex (V * psi) psi epsilon alpha‖ ^ 2
        ≤ ‖(V * psi) / psi‖ ^ 2 :=
          theta_no_gap_energy_majorant (V * psi) psi epsilon alpha
    _ ≤ ‖V‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        (multiplicative_laplacian_quotient_bound V psi) 2

end WCTLean
