import Mathlib
import WCTLean.Models.S004BoundaryWeightedEuler
import WCTLean.Models.S004EulerSeparation

/-!
# Corrected S004: first-spatial-derivative periodic test traces

The second-order spatial Green identity requires periodic matching of
both h and its first spatial derivative. A first-order trace was absent
from the previous weighted-residual separation theorem.

Here the weighted residual h(t,x)=w(t) E(t,x) is shown to possess a
GENUINE ordinary spatial derivative, with matching endpoint values,
when E has a classical spatial derivative with periodic first trace.

The resulting separation theorem is stated for this stricter test class
and instantiated with the actual corrected nonlinear S004 Euler residual.
This is not a Sobolev density theorem or full action criticality theorem:
higher regularity, integrability and the action-to-Euler bridge remain
required before closing issues #17 and #18.
-/

open MeasureTheory Set

namespace WCTLean.S004FirstSpatialTraceEuler

open WCTLean.S004BoundaryWeightedEuler
open WCTLean.S004EulerSeparation
open WCTLean.S004FullSpatialJet

/-- Temporal zero-value/zero-first-derivative traces, plus periodic
matching of the variation AND of its actual ordinary first spatial
derivative at the two spatial cell endpoints. -/
def FirstSpatialTraceTest (a b c d : ℝ)
    (h : ℝ → ℝ → ℝ) : Prop :=
  BoundaryPeriodicTest a b c d h ∧
    ∃ hx : ℝ → ℝ → ℝ,
      (∀ t x, HasDerivAt (fun s => h t s) (hx t x) x) ∧
      (∀ t, hx t c = hx t d)

/-- Because w depends only on time, differentiation of w E in
the spatial direction is the ACTUAL classical derivative w ∂x E. -/
theorem weighted_residual_has_spatial_deriv
    (a b : ℝ) (E Ex : ℝ → ℝ → ℝ)
    (hEx : ∀ t x, HasDerivAt (fun s => E t s) (Ex t x) x) :
    ∀ t x, HasDerivAt
      (fun s => E t s * timeWeight a b (t,s))
      (Ex t x * timeWeight a b (t,x)) x := by
  intro t x
  simpa only [timeWeight] using
    (hEx t x).mul_const ((t - a) ^ 2 * (b - t) ^ 2)

/-- The explicitly weighted Euler residual really belongs to the
stronger spatial trace class. Periodicity of ∂x E is supplied as
a genuine property of the residual, not of an unrelated jet. -/
theorem weighted_residual_is_first_spatial_trace_test
    (a b c d : ℝ) (E Ex : ℝ → ℝ → ℝ)
    (hEa : ∀ x, DifferentiableAt ℝ (fun t => E t x) a)
    (hEb : ∀ x, DifferentiableAt ℝ (fun t => E t x) b)
    (hPer : ∀ t, E t c = E t d)
    (hEx : ∀ t x, HasDerivAt (fun s => E t s) (Ex t x) x)
    (hExPer : ∀ t, Ex t c = Ex t d) :
    FirstSpatialTraceTest a b c d
      (fun t x => E t x * timeWeight a b (t,x)) := by
  refine ⟨weighted_residual_is_boundary_periodic_test
      a b c d E hEa hEb hPer,
    ⟨(fun t x => Ex t x * timeWeight a b (t,x)), ?_, ?_⟩⟩
  · exact weighted_residual_has_spatial_deriv a b E Ex hEx
  · intro t
    simpa only [timeWeight] using
      congrArg (fun v : ℝ => v * ((t - a) ^ 2 * (b - t) ^ 2))
        (hExPer t)

/-- A fundamental lemma for periodic cells with the missing FIRST
SPATIAL DERIVATIVE trace included in the admissible test predicate.
The proof constructs the actual w E test and reduces its vanishing
pairing to a nonnegative square integral. -/
theorem first_spatial_trace_critical_forces_ae_euler
    (a b c d : ℝ) (E Ex : ℝ → ℝ → ℝ)
    (hEa : ∀ x, DifferentiableAt ℝ (fun t => E t x) a)
    (hEb : ∀ x, DifferentiableAt ℝ (fun t => E t x) b)
    (hPer : ∀ t, E t c = E t d)
    (hEx : ∀ t x, HasDerivAt (fun s => E t s) (Ex t x) x)
    (hExPer : ∀ t, Ex t c = Ex t d)
    (hInt : Integrable
      (fun z => E z.1 z.2 ^ 2 * timeWeight a b z)
      (interiorVolume a b c d))
    (hCritical : ∀ h : ℝ → ℝ → ℝ,
      FirstSpatialTraceTest a b c d h →
      (∫ z, E z.1 z.2 * h z.1 z.2
        ∂interiorVolume a b c d) = 0) :
    ∀ᵐ z ∂interiorVolume a b c d, E z.1 z.2 = 0 := by
  have hAllowed := weighted_residual_is_first_spatial_trace_test
    a b c d E Ex hEa hEb hPer hEx hExPer
  have hzero := hCritical
    (fun t x => E t x * timeWeight a b (t,x)) hAllowed
  have hweightzero :
      (∫ z, E z.1 z.2 ^ 2 * timeWeight a b z
        ∂interiorVolume a b c d) = 0 := by
    simpa only [pow_two, mul_assoc] using hzero
  exact (weighted_zero_integral_iff_ae_zero a b c d
    (fun z => E z.1 z.2) hInt).mp hweightzero

/-- The stronger fundamental lemma applies specifically to the
nonlinear corrected S004 Euler residual, with F' and all time/spatial
acceleration momenta inherited from correctedEulerResidual. The
residual's spatial derivative and periodicity remain stated explicitly. -/
theorem corrected_euler_first_spatial_trace_critical_forces_ae
    (side : Bool) (a b c d epsilon alpha kappa theta gamma : ℝ)
    (Vprime : ℝ → ℝ → ℝ)
    (u : ℝ → ℝ → Jet 1)
    (time1 accel2 grad1 lap2 Ex : ℝ → ℝ → ℝ)
    (hEa : ∀ x, DifferentiableAt ℝ
      (fun t => correctedEulerResidual side epsilon alpha kappa
        theta gamma Vprime u time1 accel2 grad1 lap2 t x) a)
    (hEb : ∀ x, DifferentiableAt ℝ
      (fun t => correctedEulerResidual side epsilon alpha kappa
        theta gamma Vprime u time1 accel2 grad1 lap2 t x) b)
    (hPer : ∀ t,
      correctedEulerResidual side epsilon alpha kappa theta gamma
        Vprime u time1 accel2 grad1 lap2 t c =
      correctedEulerResidual side epsilon alpha kappa theta gamma
        Vprime u time1 accel2 grad1 lap2 t d)
    (hEx : ∀ t x, HasDerivAt
      (fun s => correctedEulerResidual side epsilon alpha kappa
        theta gamma Vprime u time1 accel2 grad1 lap2 t s)
      (Ex t x) x)
    (hExPer : ∀ t, Ex t c = Ex t d)
    (hInt : Integrable
      (fun z => (correctedEulerResidual side epsilon alpha kappa
        theta gamma Vprime u time1 accel2 grad1 lap2 z.1 z.2) ^ 2 *
        timeWeight a b z) (interiorVolume a b c d))
    (hCritical : ∀ h : ℝ → ℝ → ℝ,
      FirstSpatialTraceTest a b c d h →
      (∫ z, correctedEulerResidual side epsilon alpha kappa
        theta gamma Vprime u time1 accel2 grad1 lap2 z.1 z.2 *
        h z.1 z.2 ∂interiorVolume a b c d) = 0) :
    ∀ᵐ z ∂interiorVolume a b c d,
      correctedEulerResidual side epsilon alpha kappa theta gamma
        Vprime u time1 accel2 grad1 lap2 z.1 z.2 = 0 := by
  exact first_spatial_trace_critical_forces_ae_euler a b c d
    (fun t x => correctedEulerResidual side epsilon alpha kappa
      theta gamma Vprime u time1 accel2 grad1 lap2 t x)
    Ex hEa hEb hPer hEx hExPer hInt hCritical

end WCTLean.S004FirstSpatialTraceEuler
