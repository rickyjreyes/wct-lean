import Mathlib
import WCTLean.Models.S004SpacetimeActionBridge
import WCTLean.Models.S004SpacetimeEuler

/-!
# Original corrected S004 action: one conditional 1+1 strong Euler theorem

This connects the TRUE nonlinear corrected S004 integrated-action
derivative (not independent jet derivatives) to the complete
higher-time-derivative / periodic-spatial-derivative strong
Euler expression for BOTH real components.

The action-side hypotheses are actual differentiation-under-integral
domination plus five independent original-model integrability terms,
bundled in ActionRegularity solely to avoid a 50-line theorem header.

The Green-side hypotheses are EXACTLY the real partial-derivative,
temporal trace, spatial periodic-trace and integrability assumptions
of the existing proved weakComponent_eq_strongComponent theorem.
They are bundled in GreenRegularity and are never substituted with
a desired weak-to-strong identity as a hypothesis.

The result is a rigorous conditional continuum *action-to-strong*
Euler identity on one 1+1 rectangle, not the still-open theorem
that arbitrary smooth/Sobolev admissible fields discharge those
assumptions automatically, nor a criticality/weak-to-classical
equivalence or a nonlinear PDE existence theorem.
-/

open MeasureTheory Set Filter Topology
open scoped Interval

namespace WCTLean.S004SpacetimeStrongBridge

open WCTLean.S004SpacetimeActionBridge
open WCTLean.S004SpacetimeEuler
open WCTLean.S004ContinuousEuler
open WCTLean.S004FullSpatialJet

/-- Explicit original corrected S004 differentiation-under-integral
and separate physical weak-term product-integrability conditions. -/
structure ActionRegularity
    (a b c d epsilon alpha kappa theta gamma : ℝ)
    (V : ℝ → ℝ) (Vprime : ℝ → ℝ → ℝ)
    (u h : ℝ → ℝ → Jet 1) (bound : ℝ × ℝ → ℝ) : Prop where
  heps : 0 < epsilon
  ha : 0 ≤ alpha
  hV : ∀ᵐ z ∂rectangleVolume a b c d,
      HasDerivAt V (Vprime z.1 z.2)
        (WCTLean.realTwoComponentDensity
          (u z.1 z.2).x (u z.1 z.2).y)
  hmeas : ∀ᶠ t in 𝓝 (0 : ℝ),
      AEStronglyMeasurable
        (fun z : ℝ × ℝ => fullLocalDensity epsilon alpha kappa theta gamma
          V (shift (u z.1 z.2) (h z.1 z.2) t))
        (rectangleVolume a b c d)
  hint : Integrable
      (fun z : ℝ × ℝ => fullLocalDensity epsilon alpha kappa theta gamma
        V (shift (u z.1 z.2) (h z.1 z.2) (0 : ℝ)))
      (rectangleVolume a b c d)
  hdmeas : AEStronglyMeasurable
      (fun z : ℝ × ℝ => fullLocalDirection epsilon alpha kappa theta gamma
        (Vprime z.1 z.2) (u z.1 z.2) (h z.1 z.2))
      (rectangleVolume a b c d)
  hboundInt : Integrable bound (rectangleVolume a b c d)
  hlip : ∀ᵐ z ∂rectangleVolume a b c d,
      LipschitzOnWith (Real.nnabs (bound z))
        (fun t : ℝ => fullLocalDensity epsilon alpha kappa theta gamma
          V (shift (u z.1 z.2) (h z.1 z.2) t))
        (Metric.ball (0 : ℝ) 1)
  hReal : FiveTermIntegrability true a b c d epsilon alpha kappa
      theta gamma Vprime u h
  hImag : FiveTermIntegrability false a b c d epsilon alpha kappa
      theta gamma Vprime u h

/-- Verified higher-order temporal/spatial derivative and trace
conditions for one REAL component of the original complex field.
These are the precise analytic premises of the existing Green
theorem, not assumptions of the Euler equation or of its integral. -/
structure GreenRegularity (side : Bool)
    (a b c d epsilon alpha kappa theta gamma : ℝ)
    (u h : ℝ → ℝ → Jet 1)
    (time1 accel1 accel2 grad1 lap1 lap2 : ℝ → ℝ → ℝ) : Prop where
  htm : ∀ x t, t ∈ [[a,b]] →
      HasDerivAt
        (fun s => timeMomentum side (u s x)) (time1 t x) t
  hta : ∀ x t, t ∈ [[a,b]] →
      HasDerivAt
        (fun s => accelerationMomentum side epsilon alpha kappa gamma
          (u s x)) (accel1 t x) t
  hta1 : ∀ x t, t ∈ [[a,b]] →
      HasDerivAt (fun s => accel1 s x) (accel2 t x) t
  hvt : ∀ x t, t ∈ [[a,b]] →
      HasDerivAt (fun s => component side (h s x))
        (velocity side (h t x)) t
  hvt1 : ∀ x t, t ∈ [[a,b]] →
      HasDerivAt (fun s => velocity side (h s x))
        (acceleration side (h t x)) t
  htmInt : ∀ x,
      IntervalIntegrable (fun t => time1 t x) volume a b
  htaInt : ∀ x,
      IntervalIntegrable (fun t => accel1 t x) volume a b
  hta2Int : ∀ x,
      IntervalIntegrable (fun t => accel2 t x) volume a b
  hvtInt : ∀ x,
      IntervalIntegrable (fun t => velocity side (h t x)) volume a b
  hvaInt : ∀ x,
      IntervalIntegrable (fun t => acceleration side (h t x)) volume a b
  hv0a : ∀ x, component side (h a x) = 0
  hv0b : ∀ x, component side (h b x) = 0
  hv1a : ∀ x, velocity side (h a x) = 0
  hv1b : ∀ x, velocity side (h b x) = 0
  hgm : ∀ t x, x ∈ [[c,d]] →
      HasDerivAt
        (fun s => gradientMomentum side (u t s)) (grad1 t x) x
  hlm : ∀ t x, x ∈ [[c,d]] →
      HasDerivAt
        (fun s => laplacianMomentum side epsilon alpha kappa theta gamma
          (u t s)) (lap1 t x) x
  hlm1 : ∀ t x, x ∈ [[c,d]] →
      HasDerivAt (fun s => lap1 t s) (lap2 t x) x
  hvs : ∀ t x, x ∈ [[c,d]] →
      HasDerivAt (fun s => component side (h t s))
        (gradient side (h t x)) x
  hvs1 : ∀ t x, x ∈ [[c,d]] →
      HasDerivAt (fun s => gradient side (h t s))
        (laplacian side (h t x)) x
  hgmInt : ∀ t,
      IntervalIntegrable (fun x => grad1 t x) volume c d
  hlmInt : ∀ t,
      IntervalIntegrable (fun x => lap1 t x) volume c d
  hlm2Int : ∀ t,
      IntervalIntegrable (fun x => lap2 t x) volume c d
  hvsInt : ∀ t,
      IntervalIntegrable (fun x => gradient side (h t x)) volume c d
  hvlInt : ∀ t,
      IntervalIntegrable (fun x => laplacian side (h t x)) volume c d
  hgmPer : ∀ t, gradientMomentum side (u t d) =
      gradientMomentum side (u t c)
  hlmPer : ∀ t,
      laplacianMomentum side epsilon alpha kappa theta gamma (u t d) =
      laplacianMomentum side epsilon alpha kappa theta gamma (u t c)
  hl1Per : ∀ t, lap1 t d = lap1 t c
  hvPer : ∀ t, component side (h t d) = component side (h t c)
  hvgPer : ∀ t, gradient side (h t d) = gradient side (h t c)
  hfTm : IntegrableOn
      (Function.uncurry (fun t x =>
        timeMomentum side (u t x) * velocity side (h t x)))
      (uIoc a b ×ˢ uIoc c d)
  hgTm : IntegrableOn
      (Function.uncurry (fun t x =>
        time1 t x * component side (h t x)))
      (uIoc a b ×ˢ uIoc c d)
  hfAcc : IntegrableOn
      (Function.uncurry (fun t x =>
        accelerationMomentum side epsilon alpha kappa gamma (u t x) *
        acceleration side (h t x)))
      (uIoc a b ×ˢ uIoc c d)
  hgAcc : IntegrableOn
      (Function.uncurry (fun t x =>
        accel2 t x * component side (h t x)))
      (uIoc a b ×ˢ uIoc c d)

/-- All original-model Green premises suffice to DERIVE the
complete 1+1 higher-derivative weak-to-strong identity; the
desired equality is not one of the GreenRegularity fields. -/
theorem green_data_proves_weak_strong
    (side : Bool)
    (a b c d epsilon alpha kappa theta gamma : ℝ)
    (hcd : c ≤ d)
    (Vprime : ℝ → ℝ → ℝ)
    (u h : ℝ → ℝ → Jet 1)
    (time1 accel1 accel2 grad1 lap1 lap2 : ℝ → ℝ → ℝ)
    (g : GreenRegularity side a b c d epsilon alpha kappa theta gamma
      u h time1 accel1 accel2 grad1 lap1 lap2) :
    weakComponent side a b c d epsilon alpha kappa theta gamma Vprime u h =
      strongComponent side a b c d epsilon alpha kappa theta gamma
        Vprime u h time1 accel2 grad1 lap2 := by
  exact weakComponent_eq_strongComponent side a b c d
    epsilon alpha kappa theta gamma hcd Vprime u h
    time1 accel1 accel2 grad1 lap1 lap2
    g.htm     g.hta     g.hta1     g.hvt     g.hvt1     g.htmInt     g.htaInt     g.hta2Int     g.hvtInt     g.hvaInt     g.hv0a     g.hv0b     g.hv1a     g.hv1b     g.hgm     g.hlm     g.hlm1     g.hvs     g.hvs1     g.hgmInt     g.hlmInt     g.hlm2Int     g.hvsInt     g.hvlInt     g.hgmPer     g.hlmPer     g.hl1Per     g.hvPer     g.hvgPer     g.hfTm     g.hgTm     g.hfAcc     g.hgAcc

/-- THE COMPLETE conditional original-action-to-strong 1+1 Euler
first-variation identity: the derivative of the actual original
corrected nonlinear S004 integrated action along one real-two-component
jet variation equals the two complete strong higher-order Euler
expressions. Both parts are derived by the proved product-Fubini,
original density differentiation, and actual Green/FTC theorems.

Still required before claiming the original functional variational
equivalence: identify u,h with the jets of genuine admissible
smooth/Sobolev functions, derive every analytic ActionRegularity and
GreenRegularity field from their function-space hypotheses, establish
one integral of the full Euler residual, and prove the fundamental
lemma on exactly that test class. -/
theorem originalAction_hasDerivAt_strong
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
      u h timeI1 accelI1 accelI2 gradI1 lapI1 lapI2) :
    HasDerivAt
      (WCTLean.S004FullSpatialIntegral.action
        (rectangleVolume a b c d) epsilon alpha kappa theta gamma
        V (Function.uncurry u) (Function.uncurry h))
      (strongComponent true a b c d epsilon alpha kappa theta gamma
        Vprime u h timeR1 accelR2 gradR1 lapR2 +
       strongComponent false a b c d epsilon alpha kappa theta gamma
        Vprime u h timeI1 accelI2 gradI1 lapI2)
      0 := by
  have hWeak := originalAction_hasDerivAt_iterated_weak
    a b c d epsilon alpha kappa theta gamma
    hab hcd V Vprime u h bound
    hAct.heps hAct.ha hAct.hV     hAct.hmeas     hAct.hint     hAct.hdmeas     hAct.hboundInt     hAct.hlip     hAct.hReal     hAct.hImag
  have hRW := green_data_proves_weak_strong true
    a b c d epsilon alpha kappa theta gamma hcd
    Vprime u h timeR1 accelR1 accelR2 gradR1 lapR1 lapR2 hR
  have hIW := green_data_proves_weak_strong false
    a b c d epsilon alpha kappa theta gamma hcd
    Vprime u h timeI1 accelI1 accelI2 gradI1 lapI1 lapI2 hI
  rw [hRW, hIW] at hWeak
  exact hWeak

end WCTLean.S004SpacetimeStrongBridge
