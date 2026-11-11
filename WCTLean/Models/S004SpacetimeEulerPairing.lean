import Mathlib
import WCTLean.Models.S004SpacetimeStrongBridge
import WCTLean.Models.S004EulerSeparation

/-!
# Corrected S004: original action derivative equals one Euler pairing

The preceding verified action-to-strong theorem expressed δS as the
two components' five-term strong integral sums. This module establishes
the FINAL integral linearity step:

  δS = ∫_rectangle [E_R(u) h_R + E_I(u) h_I].

The two Euler residuals are the ACTUAL corrected nonlinear S004
residuals, containing the F'(ρ) force and all higher-time,
spatial-gradient and Laplacian-momentum derivatives.

No Euler equation or target integral equality is assumed. Each
physical product-integrability condition is explicit, as are the
original-action domination and full Green trace conditions inherited
from the preceding verified theorem.

This theorem does not establish smooth/Sobolev density, arbitrary
admissible-field jet realization, or critical-point equivalence.
-/

open MeasureTheory Set Filter Topology
open scoped Interval

namespace WCTLean.S004SpacetimeEulerPairing

open WCTLean.S004SpacetimeEuler
open WCTLean.S004EulerSeparation
open WCTLean.S004SpacetimeActionBridge
open WCTLean.S004SpacetimeStrongBridge
open WCTLean.S004ContinuousEuler
open WCTLean.S004FullSpatialJet

/-- Real Lebesgue integral linearity for five signed terms,
with all integrability conditions explicit. -/
theorem integral_five_signed
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (f1 f2 f3 f4 f5 : Ω → ℝ)
    (h1 : Integrable f1 mu) (h2 : Integrable f2 mu)
    (h3 : Integrable f3 mu) (h4 : Integrable f4 mu)
    (h5 : Integrable f5 mu) :
    (∫ z, (f1 - f2 + f3 - f4 + f5) z ∂mu) =
      ((((∫ z, f1 z ∂mu) - (∫ z, f2 z ∂mu)) +
        (∫ z, f3 z ∂mu)) -
       (∫ z, f4 z ∂mu)) +
      (∫ z, f5 z ∂mu) := by
  have h12 :
      (∫ z, (f1 - f2) z ∂mu) =
      (∫ z, f1 z ∂mu) - (∫ z, f2 z ∂mu) :=
    integral_sub h1 h2
  have h123 :
      (∫ z, (f1 - f2 + f3) z ∂mu) =
      (∫ z, (f1 - f2) z ∂mu) + (∫ z, f3 z ∂mu) :=
    integral_add (h1.sub h2) h3
  have h1234 :
      (∫ z, (f1 - f2 + f3 - f4) z ∂mu) =
      (∫ z, (f1 - f2 + f3) z ∂mu) - (∫ z, f4 z ∂mu) :=
    integral_sub ((h1.sub h2).add h3) h4
  have h12345 :
      (∫ z, (f1 - f2 + f3 - f4 + f5) z ∂mu) =
      (∫ z, (f1 - f2 + f3 - f4) z ∂mu) +
      (∫ z, f5 z ∂mu) :=
    integral_add (((h1.sub h2).add h3).sub h4) h5
  calc
    _ = (∫ z, (f1 - f2 + f3 - f4) z ∂mu) +
        (∫ z, f5 z ∂mu) := h12345
    _ = ((∫ z, (f1 - f2 + f3) z ∂mu) -
        (∫ z, f4 z ∂mu)) +
        (∫ z, f5 z ∂mu) := by rw [h1234]
    _ = (((∫ z, (f1 - f2) z ∂mu) +
        (∫ z, f3 z ∂mu)) -
        (∫ z, f4 z ∂mu)) +
        (∫ z, f5 z ∂mu) := by rw [h123]
    _ = ((((∫ z, f1 z ∂mu) - (∫ z, f2 z ∂mu)) +
        (∫ z, f3 z ∂mu)) -
        (∫ z, f4 z ∂mu)) +
        (∫ z, f5 z ∂mu) := by rw [h12]

/-- On the TRUE finite spacetime rectangle, the sum of the five
strong corrected S004 terms is precisely ONE Lebesgue integral of
the explicit corrected Euler residual times the real test component.
The first three product conditions can later be supplied by
ActionRegularity and GreenRegularity; the two remaining strong spatial
product conditions are stated separately. -/
theorem strongComponent_eq_residual_pairing
    (side : Bool)
    (a b c d epsilon alpha kappa theta gamma : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d)
    (Vprime : ℝ → ℝ → ℝ)
    (u h : ℝ → ℝ → Jet 1)
    (time1 accel2 grad1 lap2 : ℝ → ℝ → ℝ)
    (hf : IntegrableOn (Function.uncurry (fun t x =>
      force side epsilon alpha kappa theta gamma (Vprime t x)
        (u t x) * component side (h t x)))
      (uIoc a b ×ˢ uIoc c d))
    (ht : IntegrableOn (Function.uncurry (fun t x =>
      time1 t x * component side (h t x)))
      (uIoc a b ×ˢ uIoc c d))
    (ha : IntegrableOn (Function.uncurry (fun t x =>
      accel2 t x * component side (h t x)))
      (uIoc a b ×ˢ uIoc c d))
    (hg : IntegrableOn (Function.uncurry (fun t x =>
      grad1 t x * component side (h t x)))
      (uIoc a b ×ˢ uIoc c d))
    (hl : IntegrableOn (Function.uncurry (fun t x =>
      lap2 t x * component side (h t x)))
      (uIoc a b ×ˢ uIoc c d)) :
    strongComponent side a b c d epsilon alpha kappa theta gamma
      Vprime u h time1 accel2 grad1 lap2 =
    (∫ z, correctedEulerResidual side epsilon alpha kappa theta gamma
      Vprime u time1 accel2 grad1 lap2 z.1 z.2 *
      component side (h z.1 z.2) ∂rectangleVolume a b c d) := by
  let f1 : ℝ × ℝ → ℝ := fun z =>
    force side epsilon alpha kappa theta gamma
      (Vprime z.1 z.2) (u z.1 z.2) * component side (h z.1 z.2)
  let f2 : ℝ × ℝ → ℝ := fun z =>
    time1 z.1 z.2 * component side (h z.1 z.2)
  let f3 : ℝ × ℝ → ℝ := fun z =>
    accel2 z.1 z.2 * component side (h z.1 z.2)
  let f4 : ℝ × ℝ → ℝ := fun z =>
    grad1 z.1 z.2 * component side (h z.1 z.2)
  let f5 : ℝ × ℝ → ℝ := fun z =>
    lap2 z.1 z.2 * component side (h z.1 z.2)
  have h1 : Integrable f1 (rectangleVolume a b c d) := hf
  have h2 : Integrable f2 (rectangleVolume a b c d) := ht
  have h3 : Integrable f3 (rectangleVolume a b c d) := ha
  have h4 : Integrable f4 (rectangleVolume a b c d) := hg
  have h5 : Integrable f5 (rectangleVolume a b c d) := hl
  have hf1 : (∫ z, f1 z ∂rectangleVolume a b c d) =
      (∫ t in a..b, ∫ x in c..d,
        force side epsilon alpha kappa theta gamma
          (Vprime t x) (u t x) * component side (h t x)) :=
    rectangleVolume_integral_eq_iterated a b c d hab hcd _ hf
  have hf2 : (∫ z, f2 z ∂rectangleVolume a b c d) =
      (∫ t in a..b, ∫ x in c..d,
        time1 t x * component side (h t x)) :=
    rectangleVolume_integral_eq_iterated a b c d hab hcd _ ht
  have hf3 : (∫ z, f3 z ∂rectangleVolume a b c d) =
      (∫ t in a..b, ∫ x in c..d,
        accel2 t x * component side (h t x)) :=
    rectangleVolume_integral_eq_iterated a b c d hab hcd _ ha
  have hf4 : (∫ z, f4 z ∂rectangleVolume a b c d) =
      (∫ t in a..b, ∫ x in c..d,
        grad1 t x * component side (h t x)) :=
    rectangleVolume_integral_eq_iterated a b c d hab hcd _ hg
  have hf5 : (∫ z, f5 z ∂rectangleVolume a b c d) =
      (∫ t in a..b, ∫ x in c..d,
        lap2 t x * component side (h t x)) :=
    rectangleVolume_integral_eq_iterated a b c d hab hcd _ hl
  have hPoint :
      (fun z : ℝ × ℝ =>
        correctedEulerResidual side epsilon alpha kappa theta gamma
          Vprime u time1 accel2 grad1 lap2 z.1 z.2 *
          component side (h z.1 z.2)) =
      (f1 - f2 + f3 - f4 + f5) := by
    funext z
    simp only [correctedEulerResidual, f1, f2, f3, f4, f5,
      Pi.add_apply, Pi.sub_apply]
    ring
  calc
    strongComponent side a b c d epsilon alpha kappa theta gamma
        Vprime u h time1 accel2 grad1 lap2 =
      ((((∫ z, f1 z ∂rectangleVolume a b c d) -
         (∫ z, f2 z ∂rectangleVolume a b c d)) +
        (∫ z, f3 z ∂rectangleVolume a b c d)) -
       (∫ z, f4 z ∂rectangleVolume a b c d)) +
      (∫ z, f5 z ∂rectangleVolume a b c d) := by
        unfold strongComponent
        rw [← hf1, ← hf2, ← hf3, ← hf4, ← hf5]
    _ = (∫ z, (f1 - f2 + f3 - f4 + f5) z
        ∂rectangleVolume a b c d) :=
      (integral_five_signed (rectangleVolume a b c d)
        f1 f2 f3 f4 f5 h1 h2 h3 h4 h5).symm
    _ = (∫ z, correctedEulerResidual side epsilon alpha kappa theta gamma
          Vprime u time1 accel2 grad1 lap2 z.1 z.2 *
          component side (h z.1 z.2) ∂rectangleVolume a b c d) := by
        rw [hPoint]

/-- The exact corrected nonlinear S004 ORIGINAL ACTION first
variation equals the sum of two single spacetime integrals,
one for each REAL component of the physical complex field.

This is the requested single-pairing algebraic/measure-theoretic
closure under explicit differentiation, domination, Green, and
higher-order product-integrability hypotheses. No desired Euler
integral is itself assumed. The admissible smooth/Sobolev-field
space and weak criticality/separation theorem are different open
analytic obligations and are NOT claimed by this theorem. -/
theorem originalAction_hasDerivAt_euler_pairing
    (a b c d epsilon alpha kappa theta gamma : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d)
    (V : ℝ → ℝ) (Vprime : ℝ → ℝ → ℝ)
    (u h : ℝ → ℝ → Jet 1)
    (bound : ℝ × ℝ → ℝ)
    (timeR1 accelR1 accelR2 gradR1 lapR1 lapR2 : ℝ → ℝ → ℝ)
    (timeI1 accelI1 accelI2 gradI1 lapI1 lapI2 : ℝ → ℝ → ℝ)
    (hAct : ActionRegularity a b c d epsilon alpha kappa theta gamma
      V Vprime u h bound)
    (hR : GreenRegularity true a b c d epsilon alpha kappa theta gamma
      u h timeR1 accelR1 accelR2 gradR1 lapR1 lapR2)
    (hI : GreenRegularity false a b c d epsilon alpha kappa theta gamma
      u h timeI1 accelI1 accelI2 gradI1 lapI1 lapI2)
    (hRG : IntegrableOn (Function.uncurry (fun t x =>
      gradR1 t x * component true (h t x)))
      (uIoc a b ×ˢ uIoc c d))
    (hRL : IntegrableOn (Function.uncurry (fun t x =>
      lapR2 t x * component true (h t x)))
      (uIoc a b ×ˢ uIoc c d))
    (hIG : IntegrableOn (Function.uncurry (fun t x =>
      gradI1 t x * component false (h t x)))
      (uIoc a b ×ˢ uIoc c d))
    (hIL : IntegrableOn (Function.uncurry (fun t x =>
      lapI2 t x * component false (h t x)))
      (uIoc a b ×ˢ uIoc c d)) :
    HasDerivAt
      (WCTLean.S004FullSpatialIntegral.action
        (rectangleVolume a b c d) epsilon alpha kappa theta gamma
        V (Function.uncurry u) (Function.uncurry h))
      ((∫ z, correctedEulerResidual true epsilon alpha kappa theta gamma
          Vprime u timeR1 accelR2 gradR1 lapR2 z.1 z.2 *
          component true (h z.1 z.2) ∂rectangleVolume a b c d) +
       (∫ z, correctedEulerResidual false epsilon alpha kappa theta gamma
          Vprime u timeI1 accelI2 gradI1 lapI2 z.1 z.2 *
          component false (h z.1 z.2) ∂rectangleVolume a b c d))
      0 := by
  have hStrong := originalAction_hasDerivAt_strong
    a b c d epsilon alpha kappa theta gamma
    hab hcd V Vprime u h bound
    timeR1 accelR1 accelR2 gradR1 lapR1 lapR2
    timeI1 accelI1 accelI2 gradI1 lapI1 lapI2 hAct hR hI
  have hRP := strongComponent_eq_residual_pairing true
    a b c d epsilon alpha kappa theta gamma hab hcd Vprime u h
    timeR1 accelR2 gradR1 lapR2
    hAct.hReal.forceTerm hR.hgTm hR.hgAcc hRG hRL
  have hIP := strongComponent_eq_residual_pairing false
    a b c d epsilon alpha kappa theta gamma hab hcd Vprime u h
    timeI1 accelI2 gradI1 lapI2
    hAct.hImag.forceTerm hI.hgTm hI.hgAcc hIG hIL
  rw [hRP, hIP] at hStrong
  exact hStrong

end WCTLean.S004SpacetimeEulerPairing
