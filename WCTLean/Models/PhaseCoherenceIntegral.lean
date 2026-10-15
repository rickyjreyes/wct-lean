import Mathlib
import WCTLean.Models.CoverageExpansion

namespace WCTLean

open MeasureTheory

/-!
# E50: genuine continuum integrability, not merely pointwise algebra

The density is a nonnegative integrable function, the phase-gradient magnitude
is measurable and has an a.e. positive floor delta. This is a theorem on an
arbitrary measured space; it does not assert the WCT field supplies the floor.
-/

/-- E50: the phase-coherence density rho/g is integrable when rho is integrable
and nonnegative a.e., g is measurable, and g >= delta > 0 a.e. This closes
the measurability/integration implication formerly left behind the pointwise
bound, conditional on the named phase-gradient floor. -/
theorem phaseCoherenceIntegrable
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (rho gradient : X → ℝ) (delta : ℝ)
    (hRho : Integrable rho μ)
    (hRhoMeas : Measurable rho) (hGradientMeas : Measurable gradient)
    (hRhoNonneg : ∀ᵐ x ∂μ, 0 ≤ rho x)
    (hDelta : 0 < delta)
    (hGradientFloor : ∀ᵐ x ∂μ, delta ≤ gradient x) :
    Integrable (fun x => phaseCoherenceIntegrand (rho x) (gradient x)) μ := by
  have hmeas : AEStronglyMeasurable (fun x => rho x / gradient x) μ :=
    (hRhoMeas.div hGradientMeas).aestronglyMeasurable
  have hdom : Integrable (fun x => (1 / delta) * rho x) μ :=
    hRho.const_mul (1 / delta)
  unfold phaseCoherenceIntegrand
  refine Integrable.mono' hdom hmeas ?_
  filter_upwards [hRhoNonneg, hGradientFloor] with x hr hg
  have hgPos : 0 < gradient x := lt_of_lt_of_le hDelta hg
  have hquot : 0 ≤ rho x / gradient x := div_nonneg hr (le_of_lt hgPos)
  have hbound : rho x / gradient x ≤ rho x / delta := by
    apply (div_le_div_iff₀ hgPos hDelta).2
    exact mul_le_mul_of_nonneg_left hg hr
  rw [Real.norm_eq_abs, abs_of_nonneg hquot]
  calc
    rho x / gradient x ≤ rho x / delta := hbound
    _ = (1 / delta) * rho x := by ring

end WCTLean
