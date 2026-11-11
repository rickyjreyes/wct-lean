import Mathlib
import WCTLean.Models.S004ContinuousEuler
import WCTLean.Models.S004SpacetimeEuler

/-!
# Original corrected S004 action: product-measure to iterated weak Euler bridge

The existing S004SpacetimeEuler.originalAction_hasDerivAt_two_weak_components
proves a true derivative of the original nonlinear integrated S004
action on an arbitrary measured domain. Its two component integrals
are ordinary Lebesgue integrals over that domain.

Separately, weakComponent_eq_strongComponent proves the complete
higher-order 1+1 time/periodic-space Green identity for a FIVE-term
ITERATED integral. This file proves the missing measure-theoretic
connection, on the actual finite spacetime rectangle, between these
two functionals. No desired first-variation identity is assumed.

FiveTermIntegrability keeps explicit all five physically distinct
real-component integrands. The assumptions are product-measure
integrability and a <= b, c <= d. They are not claimed to follow
automatically from a particular Sobolev class. This proof alone is
not yet the final admissible smooth/Sobolev critical-point theorem.
-/

open MeasureTheory Set Filter Topology
open scoped Interval

namespace WCTLean.S004SpacetimeActionBridge

open WCTLean.S004ContinuousEuler
open WCTLean.S004SpacetimeEuler
open WCTLean.S004FullSpatialJet

/-- Fubini for the ACTUAL volume restriction used by the corrected
S004 action. It converts one product Lebesgue integral to the exact
time-major two-interval integral used by the proved spacetime Green
identity; no abstract integration operator is postulated. -/
theorem rectangleVolume_integral_eq_iterated
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (f : ℝ → ℝ → ℝ)
    (hf : IntegrableOn (Function.uncurry f)
      (uIoc a b ×ˢ uIoc c d)) :
    (∫ z, f z.1 z.2 ∂rectangleVolume a b c d) =
      (∫ t in a..b, ∫ x in c..d, f t x) := by
  have hmeasure :
      rectangleVolume a b c d =
        ((volume : Measure ℝ).restrict (Ioc a b)).prod
          ((volume : Measure ℝ).restrict (Ioc c d)) := by
    simp only [rectangleVolume, uIoc_of_le hab, uIoc_of_le hcd,
      Measure.prod_restrict, ← Measure.volume_eq_prod ℝ ℝ]
  have hprod : Integrable (Function.uncurry f)
      (((volume : Measure ℝ).restrict (Ioc a b)).prod
        ((volume : Measure ℝ).restrict (Ioc c d))) := by
    rw [← hmeasure]
    exact hf
  calc
    (∫ z, f z.1 z.2 ∂rectangleVolume a b c d) =
      ∫ z, Function.uncurry f z
        ∂(((volume : Measure ℝ).restrict (Ioc a b)).prod
          ((volume : Measure ℝ).restrict (Ioc c d))) := by
            rw [hmeasure]
            rfl
    _ = ∫ t, ∫ x, f t x ∂((volume : Measure ℝ).restrict (Ioc c d))
          ∂((volume : Measure ℝ).restrict (Ioc a b)) :=
        integral_prod (Function.uncurry f) hprod
    _ = ∫ t in a..b, ∫ x in c..d, f t x := by
      simp only [intervalIntegral.integral_of_le hab,
        intervalIntegral.integral_of_le hcd]

/-- All five original nonlinear S004 first-variation terms are
product-integrable on the finite 1+1 spacetime rectangle. This is
an explicit analytical condition on the TRUE nonlinear coefficients
and derivative jets, not an independent weak-to-strong identity. -/
structure FiveTermIntegrability (side : Bool)
    (a b c d epsilon alpha kappa theta gamma : ℝ)
    (Vprime : ℝ → ℝ → ℝ)
    (u h : ℝ → ℝ → Jet 1) : Prop where
  forceTerm : IntegrableOn
    (Function.uncurry (fun t x =>
      force side epsilon alpha kappa theta gamma
        (Vprime t x) (u t x) * component side (h t x)))
    (uIoc a b ×ˢ uIoc c d)
  timeTerm : IntegrableOn
    (Function.uncurry (fun t x =>
      timeMomentum side (u t x) * velocity side (h t x)))
    (uIoc a b ×ˢ uIoc c d)
  accelTerm : IntegrableOn
    (Function.uncurry (fun t x =>
      accelerationMomentum side epsilon alpha kappa gamma (u t x) *
        acceleration side (h t x)))
    (uIoc a b ×ˢ uIoc c d)
  gradientTerm : IntegrableOn
    (Function.uncurry (fun t x =>
      gradientMomentum side (u t x) * gradient side (h t x)))
    (uIoc a b ×ˢ uIoc c d)
  laplaceTerm : IntegrableOn
    (Function.uncurry (fun t x =>
      laplacianMomentum side epsilon alpha kappa theta gamma (u t x) *
        laplacian side (h t x)))
    (uIoc a b ×ˢ uIoc c d)

/-- Product-integrability of the five separate terms proves
integrability of their original summed weak density. This
discharges, rather than assumes, the component integrability
premise in the original action-derivative theorem. -/
theorem five_terms_integrable
    (side : Bool) (a b c d epsilon alpha kappa theta gamma : ℝ)
    (Vprime : ℝ → ℝ → ℝ) (u h : ℝ → ℝ → Jet 1)
    (hi : FiveTermIntegrability side a b c d epsilon alpha kappa
      theta gamma Vprime u h) :
    Integrable (fun z =>
      weakPointwiseComponent side epsilon alpha kappa theta gamma
        (Vprime z.1 z.2) (u z.1 z.2) (h z.1 z.2))
      (rectangleVolume a b c d) := by
  change Integrable (fun z : ℝ × ℝ =>
    force side epsilon alpha kappa theta gamma
      (Vprime z.1 z.2) (u z.1 z.2) * component side (h z.1 z.2) +
    timeMomentum side (u z.1 z.2) * velocity side (h z.1 z.2) +
    accelerationMomentum side epsilon alpha kappa gamma (u z.1 z.2) *
      acceleration side (h z.1 z.2) +
    gradientMomentum side (u z.1 z.2) * gradient side (h z.1 z.2) +
    laplacianMomentum side epsilon alpha kappa theta gamma (u z.1 z.2) *
      laplacian side (h z.1 z.2)) (rectangleVolume a b c d)
  exact ((((hi.forceTerm.add hi.timeTerm).add hi.accelTerm).add
    hi.gradientTerm).add hi.laplaceTerm)

/-- The integrated ORIGINAL corrected S004 component density equals
its five-term time-major weak functional on a genuine finite
spacetime rectangle. The proof uses Fubini and Lebesgue integral
linearity, with all five product integrabilities independently
supplied, rather than assuming any Euler or Green equality. -/
theorem weakPointwise_integral_eq_weakComponent
    (side : Bool)
    (a b c d epsilon alpha kappa theta gamma : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d)
    (Vprime : ℝ → ℝ → ℝ)
    (u h : ℝ → ℝ → Jet 1)
    (hi : FiveTermIntegrability side a b c d epsilon alpha kappa
      theta gamma Vprime u h) :
    (∫ z, weakPointwiseComponent side epsilon alpha kappa theta gamma
      (Vprime z.1 z.2) (u z.1 z.2) (h z.1 z.2)
      ∂rectangleVolume a b c d) =
    weakComponent side a b c d epsilon alpha kappa theta gamma
      Vprime u h := by
  have hf : Integrable (fun z : ℝ × ℝ =>
      force side epsilon alpha kappa theta gamma
        (Vprime z.1 z.2) (u z.1 z.2) *
        component side (h z.1 z.2)) (rectangleVolume a b c d) :=
    hi.forceTerm
  have ht : Integrable (fun z : ℝ × ℝ =>
      timeMomentum side (u z.1 z.2) *
        velocity side (h z.1 z.2)) (rectangleVolume a b c d) :=
    hi.timeTerm
  have ha : Integrable (fun z : ℝ × ℝ =>
      accelerationMomentum side epsilon alpha kappa gamma
        (u z.1 z.2) * acceleration side (h z.1 z.2))
        (rectangleVolume a b c d) :=
    hi.accelTerm
  have hg : Integrable (fun z : ℝ × ℝ =>
      gradientMomentum side (u z.1 z.2) *
        gradient side (h z.1 z.2)) (rectangleVolume a b c d) :=
    hi.gradientTerm
  have hl : Integrable (fun z : ℝ × ℝ =>
      laplacianMomentum side epsilon alpha kappa theta gamma
        (u z.1 z.2) * laplacian side (h z.1 z.2))
        (rectangleVolume a b c d) :=
    hi.laplaceTerm
  let f1 : ℝ × ℝ → ℝ := fun z =>
    force side epsilon alpha kappa theta gamma
      (Vprime z.1 z.2) (u z.1 z.2) * component side (h z.1 z.2)
  let f2 : ℝ × ℝ → ℝ := fun z =>
    timeMomentum side (u z.1 z.2) * velocity side (h z.1 z.2)
  let f3 : ℝ × ℝ → ℝ := fun z =>
    accelerationMomentum side epsilon alpha kappa gamma (u z.1 z.2) *
      acceleration side (h z.1 z.2)
  let f4 : ℝ × ℝ → ℝ := fun z =>
    gradientMomentum side (u z.1 z.2) * gradient side (h z.1 z.2)
  let f5 : ℝ × ℝ → ℝ := fun z =>
    laplacianMomentum side epsilon alpha kappa theta gamma (u z.1 z.2) *
      laplacian side (h z.1 z.2)
  change (∫ z, (f1 + f2 + f3 + f4 + f5) z
      ∂rectangleVolume a b c d) =
    weakComponent side a b c d epsilon alpha kappa theta gamma
      Vprime u h
  have h12 : (∫ z, (f1 + f2) z ∂rectangleVolume a b c d) =
      (∫ z, f1 z ∂rectangleVolume a b c d) +
      (∫ z, f2 z ∂rectangleVolume a b c d) :=
    integral_add hf ht
  have h123 : (∫ z, (f1 + f2 + f3) z ∂rectangleVolume a b c d) =
      (∫ z, (f1 + f2) z ∂rectangleVolume a b c d) +
      (∫ z, f3 z ∂rectangleVolume a b c d) :=
    integral_add (hf.add ht) ha
  have h1234 : (∫ z, (f1 + f2 + f3 + f4) z ∂rectangleVolume a b c d) =
      (∫ z, (f1 + f2 + f3) z ∂rectangleVolume a b c d) +
      (∫ z, f4 z ∂rectangleVolume a b c d) :=
    integral_add ((hf.add ht).add ha) hg
  have h12345 : (∫ z, (f1 + f2 + f3 + f4 + f5) z
      ∂rectangleVolume a b c d) =
      (∫ z, (f1 + f2 + f3 + f4) z ∂rectangleVolume a b c d) +
      (∫ z, f5 z ∂rectangleVolume a b c d) :=
    integral_add (((hf.add ht).add ha).add hg) hl
  have hsum :
      (∫ z, (f1 + f2 + f3 + f4 + f5) z ∂rectangleVolume a b c d) =
      ((((∫ z, f1 z ∂rectangleVolume a b c d) +
         (∫ z, f2 z ∂rectangleVolume a b c d)) +
        (∫ z, f3 z ∂rectangleVolume a b c d)) +
       (∫ z, f4 z ∂rectangleVolume a b c d)) +
      (∫ z, f5 z ∂rectangleVolume a b c d) := by
    calc
      _ = (∫ z, (f1 + f2 + f3 + f4) z ∂rectangleVolume a b c d) +
          (∫ z, f5 z ∂rectangleVolume a b c d) := h12345
      _ = ((∫ z, (f1 + f2 + f3) z ∂rectangleVolume a b c d) +
          (∫ z, f4 z ∂rectangleVolume a b c d)) +
          (∫ z, f5 z ∂rectangleVolume a b c d) := by rw [h1234]
      _ = (((∫ z, (f1 + f2) z ∂rectangleVolume a b c d) +
          (∫ z, f3 z ∂rectangleVolume a b c d)) +
          (∫ z, f4 z ∂rectangleVolume a b c d)) +
          (∫ z, f5 z ∂rectangleVolume a b c d) := by rw [h123]
      _ = ((((∫ z, f1 z ∂rectangleVolume a b c d) +
          (∫ z, f2 z ∂rectangleVolume a b c d)) +
          (∫ z, f3 z ∂rectangleVolume a b c d)) +
          (∫ z, f4 z ∂rectangleVolume a b c d)) +
          (∫ z, f5 z ∂rectangleVolume a b c d) := by rw [h12]
  rw [hsum]
  dsimp only [f1, f2, f3, f4, f5, weakComponent]
  rw [rectangleVolume_integral_eq_iterated a b c d hab hcd
       (fun t x => force side epsilon alpha kappa theta gamma
         (Vprime t x) (u t x) * component side (h t x)) hi.forceTerm,
      rectangleVolume_integral_eq_iterated a b c d hab hcd
       (fun t x => timeMomentum side (u t x) *
         velocity side (h t x)) hi.timeTerm,
      rectangleVolume_integral_eq_iterated a b c d hab hcd
       (fun t x => accelerationMomentum side epsilon alpha kappa gamma
         (u t x) * acceleration side (h t x)) hi.accelTerm,
      rectangleVolume_integral_eq_iterated a b c d hab hcd
       (fun t x => gradientMomentum side (u t x) *
         gradient side (h t x)) hi.gradientTerm,
      rectangleVolume_integral_eq_iterated a b c d hab hcd
       (fun t x => laplacianMomentum side epsilon alpha kappa theta gamma
         (u t x) * laplacian side (h t x)) hi.laplaceTerm]

/-- Genuine derivative of the ORIGINAL corrected nonlinear S004
integrated field/jet action expressed as the two five-term 1+1
spacetime weak Euler functionals. The domination and potential
hypotheses are exactly those required for differentiation under the
Lebesgue integral; the five-term integrability conditions discharge
the component integrability hypotheses automatically.

The h-jets still require a concrete derivative-compatible field
realization, and a full strong-Euler formulation uses the already
proved weakComponent_eq_strongComponent with its explicit Green
regularity/traces. No Sobolev or criticality closure is claimed. -/
theorem originalAction_hasDerivAt_iterated_weak
    (a b c d epsilon alpha kappa theta gamma : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d)
    (V : ℝ → ℝ)
    (Vprime : ℝ → ℝ → ℝ)
    (u h : ℝ → ℝ → Jet 1)
    (bound : ℝ × ℝ → ℝ)
    (heps : 0 < epsilon) (ha : 0 ≤ alpha)
    (hV : ∀ᵐ z ∂rectangleVolume a b c d,
      HasDerivAt V (Vprime z.1 z.2)
        (WCTLean.realTwoComponentDensity
          (u z.1 z.2).x (u z.1 z.2).y))
    (hmeas : ∀ᶠ t in 𝓝 (0 : ℝ),
      AEStronglyMeasurable
        (fun z : ℝ × ℝ => fullLocalDensity epsilon alpha kappa theta gamma
          V (shift (u z.1 z.2) (h z.1 z.2) t))
        (rectangleVolume a b c d))
    (hint : Integrable
      (fun z : ℝ × ℝ => fullLocalDensity epsilon alpha kappa theta gamma
        V (shift (u z.1 z.2) (h z.1 z.2) (0 : ℝ)))
      (rectangleVolume a b c d))
    (hdmeas : AEStronglyMeasurable
      (fun z : ℝ × ℝ => fullLocalDirection epsilon alpha kappa theta gamma
        (Vprime z.1 z.2) (u z.1 z.2) (h z.1 z.2))
      (rectangleVolume a b c d))
    (hboundInt : Integrable bound (rectangleVolume a b c d))
    (hlip : ∀ᵐ z ∂rectangleVolume a b c d,
      LipschitzOnWith (Real.nnabs (bound z))
        (fun t : ℝ => fullLocalDensity epsilon alpha kappa theta gamma
          V (shift (u z.1 z.2) (h z.1 z.2) t))
        (Metric.ball (0 : ℝ) 1))
    (hReal : FiveTermIntegrability true a b c d epsilon alpha kappa
      theta gamma Vprime u h)
    (hImag : FiveTermIntegrability false a b c d epsilon alpha kappa
      theta gamma Vprime u h) :
    HasDerivAt
      (WCTLean.S004FullSpatialIntegral.action
        (rectangleVolume a b c d) epsilon alpha kappa theta gamma
        V (Function.uncurry u) (Function.uncurry h))
      (weakComponent true a b c d epsilon alpha kappa theta gamma Vprime u h +
       weakComponent false a b c d epsilon alpha kappa theta gamma Vprime u h)
      0 := by
  have hder := originalAction_hasDerivAt_two_weak_components
    (rectangleVolume a b c d)
    epsilon alpha kappa theta gamma V
    (Function.uncurry u) (Function.uncurry h)
    (Function.uncurry Vprime) bound
    heps ha hV hmeas hint hdmeas hboundInt hlip
    (five_terms_integrable true a b c d epsilon alpha kappa
      theta gamma Vprime u h hReal)
    (five_terms_integrable false a b c d epsilon alpha kappa
      theta gamma Vprime u h hImag)
  simp only [Function.uncurry] at hder
  rw [weakPointwise_integral_eq_weakComponent true a b c d
      epsilon alpha kappa theta gamma hab hcd Vprime u h hReal,
    weakPointwise_integral_eq_weakComponent false a b c d
      epsilon alpha kappa theta gamma hab hcd Vprime u h hImag] at hder
  exact hder

end WCTLean.S004SpacetimeActionBridge
