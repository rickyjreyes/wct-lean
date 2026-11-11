import Mathlib
import WCTLean.Models.S004EulerSeparation
import WCTLean.Models.S004SpacetimeFubini

/-!
# Continuous corrected S004 Euler residuals: no independent L² premise

On an actual finite time × periodic-space rectangle, continuous
nonlinear Euler coefficient functions have square-integrable
residuals, because their squares are continuous on a compact set.
This is a DERIVED analytical input, not an assumed L² estimate.

Combining that property with the proved real two-component integral
separation theorem, all residual pairings against integrable test
directions vanish iff BOTH corrected S004 Euler residuals vanish
almost everywhere on the rectangle.

The test class here still includes all integrable pairings, rather
than only smooth variations vanishing at the time endpoints. A
separate density theorem is required before identifying this
criterion with classical critical points of the original action.
-/

open MeasureTheory Set

namespace WCTLean.S004ContinuousEuler

open WCTLean.S004EulerSeparation
open WCTLean.S004SpacetimeFubini
open WCTLean.S004SpacetimeEuler

/-- Actual Lebesgue volume restricted to a spacetime fundamental
rectangle, not an abstract measure unrelated to the action. -/
noncomputable def rectangleVolume
    (a b c d : ℝ) : Measure (ℝ × ℝ) :=
  (volume : Measure (ℝ × ℝ)).restrict (uIoc a b ×ˢ uIoc c d)

/-- A continuous real Euler residual has integrable square on an
actual compact time × periodic-space fundamental rectangle.
This discharges the L² premise used in weak-test separation. -/
theorem continuous_square_integrable
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (E : ℝ × ℝ → ℝ) (hE : Continuous E) :
    Integrable (fun z => E z ^ 2) (rectangleVolume a b c d) := by
  have hc :
      Continuous (Function.uncurry (fun t x => E (t, x) ^ 2)) := by
    change Continuous (fun z : ℝ × ℝ => E z ^ 2)
    exact hE.pow 2
  have h := continuous_rectangle_integrable
    a b c d hab hcd (fun t x => E (t,x) ^ 2) hc
  change Integrable (fun z => E z ^ 2)
    ((volume : Measure (ℝ × ℝ)).restrict
      (uIoc a b ×ˢ uIoc c d)) at h
  exact h

/-- Complete two-component weak-test separation on the actual
periodic-space spacetime rectangle, with NO manually supplied
L² hypothesis: continuity implies finite square energy. -/
theorem continuous_two_component_probes_iff_ae_zero
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (ER EI : ℝ × ℝ → ℝ)
    (hR : Continuous ER) (hI : Continuous EI) :
    (∀ hR hI : ℝ × ℝ → ℝ,
      Integrable (fun z => ER z * hR z) (rectangleVolume a b c d) →
      Integrable (fun z => EI z * hI z) (rectangleVolume a b c d) →
      (∫ z, ER z * hR z ∂rectangleVolume a b c d) +
        (∫ z, EI z * hI z ∂rectangleVolume a b c d) = 0) ↔
    (∀ᵐ z ∂rectangleVolume a b c d, ER z = 0) ∧
    (∀ᵐ z ∂rectangleVolume a b c d, EI z = 0) := by
  exact two_component_integrable_probes_iff_ae_zero
    (rectangleVolume a b c d) ER EI
    (continuous_square_integrable a b c d hab hcd ER hR)
    (continuous_square_integrable a b c d hab hcd EI hI)

/-- The same separation theorem instantiated with the ACTUAL
nonlinear corrected S004 Euler residuals, including potential
and regulator derivatives and both higher-order momentum terms.
The continuity of those residuals may be established from a
sufficiently smooth field by a further Sobolev/composition theorem. -/
theorem corrected_euler_continuous_probes_iff_ae_equations
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (epsilon alpha kappa theta gamma : ℝ)
    (Vprime : ℝ → ℝ → ℝ)
    (u : ℝ → ℝ → WCTLean.S004FullSpatialJet.Jet 1)
    (timeR1 accelR2 gradR1 lapR2 : ℝ → ℝ → ℝ)
    (timeI1 accelI2 gradI1 lapI2 : ℝ → ℝ → ℝ)
    (hR : Continuous (fun z : ℝ × ℝ =>
      correctedEulerResidual true epsilon alpha kappa theta gamma
        Vprime u timeR1 accelR2 gradR1 lapR2 z.1 z.2))
    (hI : Continuous (fun z : ℝ × ℝ =>
      correctedEulerResidual false epsilon alpha kappa theta gamma
        Vprime u timeI1 accelI2 gradI1 lapI2 z.1 z.2)) :
    (∀ hR hI : ℝ × ℝ → ℝ,
      Integrable (fun z =>
        correctedEulerResidual true epsilon alpha kappa theta gamma
          Vprime u timeR1 accelR2 gradR1 lapR2 z.1 z.2 * hR z)
        (rectangleVolume a b c d) →
      Integrable (fun z =>
        correctedEulerResidual false epsilon alpha kappa theta gamma
          Vprime u timeI1 accelI2 gradI1 lapI2 z.1 z.2 * hI z)
        (rectangleVolume a b c d) →
      (∫ z,
        correctedEulerResidual true epsilon alpha kappa theta gamma
          Vprime u timeR1 accelR2 gradR1 lapR2 z.1 z.2 * hR z
        ∂rectangleVolume a b c d) +
      (∫ z,
        correctedEulerResidual false epsilon alpha kappa theta gamma
          Vprime u timeI1 accelI2 gradI1 lapI2 z.1 z.2 * hI z
        ∂rectangleVolume a b c d) = 0) ↔
    (∀ᵐ z ∂rectangleVolume a b c d,
      correctedEulerResidual true epsilon alpha kappa theta gamma
        Vprime u timeR1 accelR2 gradR1 lapR2 z.1 z.2 = 0) ∧
    (∀ᵐ z ∂rectangleVolume a b c d,
      correctedEulerResidual false epsilon alpha kappa theta gamma
        Vprime u timeI1 accelI2 gradI1 lapI2 z.1 z.2 = 0) := by
  exact corrected_euler_all_probes_iff_ae_equations
    (rectangleVolume a b c d)
    epsilon alpha kappa theta gamma Vprime u
    timeR1 accelR2 gradR1 lapR2
    timeI1 accelI2 gradI1 lapI2
    (continuous_square_integrable a b c d hab hcd _ hR)
    (continuous_square_integrable a b c d hab hcd _ hI)

end WCTLean.S004ContinuousEuler
