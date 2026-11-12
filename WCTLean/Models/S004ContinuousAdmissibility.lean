import Mathlib
import WCTLean.Models.CorrectedWeightDirection
import WCTLean.Models.S004SpacetimeEulerPairing
import WCTLean.Models.S004SpacetimeFubini

/-!
# Phase XXII: continuous original-model S004 data on a finite rectangle

The corrected S004 two-real-component regulator
  F(rho) = rho / (rho + epsilon² exp(-2 alpha rho))²
is CONTINUOUS through true field nodes. This is proved for genuinely
continuous real-component fields, using the previously kernel-checked
positive regulator floor, not a false global nonvanishing-amplitude
assumption.

A concrete continuous-product analytical class on the compact closed
rectangle discharges ALL TEN original weak first-variation
product-integrability obligations and the FOUR strong spatial
product-integrability obligations in the exact Euler pairing theorem.

The action's neighborhood domination and derivative-jet / periodic
Green trace conditions are still separately required. These are
genuine, identified remaining open analyses: continuous weak
products alone do not imply Sobolev differentiability or domination.

No change to the original corrected S004 action/equations is made.
-/

open MeasureTheory Set Filter Topology
open scoped Interval

namespace WCTLean.S004ContinuousAdmissibility

open WCTLean
open WCTLean.S004FullSpatialJet
open WCTLean.S004SpacetimeActionBridge
open WCTLean.S004SpacetimeStrongBridge
open WCTLean.S004SpacetimeEulerPairing
open WCTLean.S004SpacetimeEuler
open WCTLean.S004ContinuousEuler
open WCTLean.S004SpacetimeFubini

/-- The true corrected S004 quotient is continuous even at
psi=0 for genuinely continuous x and y. No positive amplitude
floor is imposed; the REGULATOR has the positive floor. -/
theorem corrected_weight_continuous_for_field
    (epsilon alpha : ℝ) (heps : 0 < epsilon) (ha : 0 ≤ alpha)
    (x y : ℝ × ℝ → ℝ) (hx : Continuous x) (hy : Continuous y) :
    Continuous (fun z =>
      realTwoComponentWeight epsilon alpha (x z) (y z)) := by
  have hrho : Continuous
      (fun z => realTwoComponentDensity (x z) (y z)) := by
    simpa only [realTwoComponentDensity] using (hx.pow 2).add (hy.pow 2)
  apply continuous_iff_continuousAt.mpr
  intro z
  have hnonneg : 0 ≤ realTwoComponentDensity (x z) (y z) := by
    unfold realTwoComponentDensity
    positivity
  have hdenpos : 0 < correctedRadialDenominator epsilon alpha
      (realTwoComponentDensity (x z) (y z)) := by
    exact lt_of_lt_of_le
      (complexRegulatorFloor_pos epsilon alpha heps)
      (correctedRadialDenominator_floor epsilon alpha
        (realTwoComponentDensity (x z) (y z)) hnonneg heps ha)
  have hcont : ContinuousAt (correctedRadialWeight epsilon alpha)
      (realTwoComponentDensity (x z) (y z)) :=
    (correctedRadialWeight_hasDerivAt epsilon alpha _
      (ne_of_gt hdenpos)).continuousAt
  change ContinuousAt
    (fun w : ℝ × ℝ => correctedRadialWeight epsilon alpha
      (realTwoComponentDensity (x w) (y w))) z
  exact hcont.comp z (hrho.continuousAt)

/-- Continuous original-model regulator fields are actually
Lebesgue integrable over any finite spacetime rectangle. -/
theorem corrected_weight_rectangle_integrable
    (epsilon alpha a b c d : ℝ)
    (heps : 0 < epsilon) (ha : 0 ≤ alpha)
    (hab : a ≤ b) (hcd : c ≤ d)
    (x y : ℝ × ℝ → ℝ) (hx : Continuous x) (hy : Continuous y) :
    IntegrableOn
      (fun z => realTwoComponentWeight epsilon alpha (x z) (y z))
      (uIoc a b ×ˢ uIoc c d) := by
  exact continuous_rectangle_integrable a b c d hab hcd
    (fun t x0 => realTwoComponentWeight epsilon alpha
      (x (t, x0)) (y (t, x0)))
    (corrected_weight_continuous_for_field epsilon alpha heps ha x y hx hy)

/-- Domain-local continuity is sufficient for true Lebesgue
integrability on a finite closed rectangle. Unlike a global
continuity requirement, data outside the fundamental cell
are irrelevant to this theorem. -/
theorem closed_rectangle_continuous_integrable
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (f : ℝ × ℝ → ℝ)
    (hf : ContinuousOn f (Icc a b ×ˢ Icc c d)) :
    IntegrableOn f (uIoc a b ×ˢ uIoc c d) := by
  have hcompact : IsCompact (Icc a b ×ˢ Icc c d) :=
    isCompact_Icc.prod isCompact_Icc
  have hfull : IntegrableOn f (Icc a b ×ˢ Icc c d) :=
    hf.integrableOn_compact hcompact
  apply hfull.mono_set
  rintro ⟨t,x⟩ ⟨ht,hx⟩
  change t ∈ Icc a b ∧ x ∈ Icc c d
  rw [uIoc_of_le hab] at ht
  rw [uIoc_of_le hcd] at hx
  exact ⟨Ioc_subset_Icc_self ht, Ioc_subset_Icc_self hx⟩

/-- Actual physical five-term weak first-variation products for
one real component, continuous ON THE CLOSED RECTANGLE. These
are assumptions of classical local continuity, not assumptions
of their integrability or of the Euler residual equality. -/
structure ContinuousWeakProducts (side : Bool)
    (a b c d epsilon alpha kappa theta gamma : ℝ)
    (Vprime : ℝ → ℝ → ℝ)
    (u h : ℝ → ℝ → Jet 1) : Prop where
  forceTerm : ContinuousOn
    (Function.uncurry (fun t x =>
      force side epsilon alpha kappa theta gamma
        (Vprime t x) (u t x) * component side (h t x)))
    (Icc a b ×ˢ Icc c d)
  timeTerm : ContinuousOn
    (Function.uncurry (fun t x =>
      timeMomentum side (u t x) * velocity side (h t x)))
    (Icc a b ×ˢ Icc c d)
  accelTerm : ContinuousOn
    (Function.uncurry (fun t x =>
      accelerationMomentum side epsilon alpha kappa gamma (u t x) *
        acceleration side (h t x)))
    (Icc a b ×ˢ Icc c d)
  gradientTerm : ContinuousOn
    (Function.uncurry (fun t x =>
      gradientMomentum side (u t x) * gradient side (h t x)))
    (Icc a b ×ˢ Icc c d)
  laplaceTerm : ContinuousOn
    (Function.uncurry (fun t x =>
      laplacianMomentum side epsilon alpha kappa theta gamma (u t x) *
        laplacian side (h t x)))
    (Icc a b ×ˢ Icc c d)

/-- All five true corrected S004 weak-product integrability
requirements are DERIVED from domain-local continuity. -/
theorem continuous_weak_products_integrable
    (side : Bool)
    (a b c d epsilon alpha kappa theta gamma : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d)
    (Vprime : ℝ → ℝ → ℝ) (u h : ℝ → ℝ → Jet 1)
    (hc : ContinuousWeakProducts side a b c d epsilon alpha kappa
      theta gamma Vprime u h) :
    FiveTermIntegrability side a b c d epsilon alpha kappa
      theta gamma Vprime u h := by
  exact {
    forceTerm := closed_rectangle_continuous_integrable
      a b c d hab hcd _ hc.forceTerm
    timeTerm := closed_rectangle_continuous_integrable
      a b c d hab hcd _ hc.timeTerm
    accelTerm := closed_rectangle_continuous_integrable
      a b c d hab hcd _ hc.accelTerm
    gradientTerm := closed_rectangle_continuous_integrable
      a b c d hab hcd _ hc.gradientTerm
    laplaceTerm := closed_rectangle_continuous_integrable
      a b c d hab hcd _ hc.laplaceTerm
  }

/-- The two strong Euler spatial products per real component.
These are classical continuity hypotheses on actual derivative
momenta, not hypotheses on the final Euler equation or its integral. -/
structure ContinuousStrongSpatialProducts (side : Bool)
    (a b c d : ℝ) (h : ℝ → ℝ → Jet 1)
    (grad1 lap2 : ℝ → ℝ → ℝ) : Prop where
  gradientTerm : ContinuousOn
    (Function.uncurry (fun t x =>
      grad1 t x * component side (h t x)))
    (Icc a b ×ˢ Icc c d)
  laplaceTerm : ContinuousOn
    (Function.uncurry (fun t x =>
      lap2 t x * component side (h t x)))
    (Icc a b ×ˢ Icc c d)

/-- The two extra spatial integrability premises in the exact
original-action Euler-pairing theorem follow automatically
from domain-local continuity of the actual strong products. -/
theorem continuous_strong_products_integrable
    (side : Bool) (a b c d : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d)
    (h : ℝ → ℝ → Jet 1) (grad1 lap2 : ℝ → ℝ → ℝ)
    (hc : ContinuousStrongSpatialProducts side a b c d h grad1 lap2) :
    IntegrableOn
      (Function.uncurry (fun t x =>
        grad1 t x * component side (h t x)))
      (uIoc a b ×ˢ uIoc c d) ∧
    IntegrableOn
      (Function.uncurry (fun t x =>
        lap2 t x * component side (h t x)))
      (uIoc a b ×ˢ uIoc c d) := by
  exact ⟨closed_rectangle_continuous_integrable
    a b c d hab hcd _ hc.gradientTerm,
    closed_rectangle_continuous_integrable
    a b c d hab hcd _ hc.laplaceTerm⟩

/-- The non-integrability part of the ORIGINAL nonlinear action
differentiation hypotheses. Integrability of the ten weak terms
will be proved separately by continuous_weak_products_integrable,
so it is NOT smuggled into this structure. Other domination
assumptions remain openly named. -/
structure ActionDomination
    (a b c d epsilon alpha kappa theta gamma : ℝ)
    (V : ℝ → ℝ) (Vprime : ℝ → ℝ → ℝ)
    (u h : ℝ → ℝ → Jet 1) (bound : ℝ × ℝ → ℝ) : Prop where
  heps : 0 < epsilon
  ha : 0 ≤ alpha
  hV : ∀ᵐ z ∂rectangleVolume a b c d,
    HasDerivAt V (Vprime z.1 z.2)
      (realTwoComponentDensity (u z.1 z.2).x (u z.1 z.2).y)
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

/-- Phase XXII strongest new application: in a finite 1+1 cell,
all FOURTEEN independent original S004 weak/strong product
integrability requirements are no longer explicit assumptions.
They follow from continuous classical input data on the closed
rectangle. The remaining original-action domination and
genuine Green-derivative/trace premises are transparently required.

This theorem is NOT an unconditional Sobolev critical-point
equivalence and does not assert nodal ghost freedom. -/
theorem originalAction_hasDerivAt_euler_pairing_of_continuity
    (a b c d epsilon alpha kappa theta gamma : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d)
    (V : ℝ → ℝ) (Vprime : ℝ → ℝ → ℝ)
    (u h : ℝ → ℝ → Jet 1)
    (bound : ℝ × ℝ → ℝ)
    (timeR1 accelR1 accelR2 gradR1 lapR1 lapR2 : ℝ → ℝ → ℝ)
    (timeI1 accelI1 accelI2 gradI1 lapI1 lapI2 : ℝ → ℝ → ℝ)
    (hDom : ActionDomination a b c d epsilon alpha kappa theta gamma
      V Vprime u h bound)
    (hWeakR : ContinuousWeakProducts true a b c d epsilon alpha kappa
      theta gamma Vprime u h)
    (hWeakI : ContinuousWeakProducts false a b c d epsilon alpha kappa
      theta gamma Vprime u h)
    (hGreenR : GreenRegularity true a b c d epsilon alpha kappa theta gamma
      u h timeR1 accelR1 accelR2 gradR1 lapR1 lapR2)
    (hGreenI : GreenRegularity false a b c d epsilon alpha kappa theta gamma
      u h timeI1 accelI1 accelI2 gradI1 lapI1 lapI2)
    (hStrongR : ContinuousStrongSpatialProducts true
      a b c d h gradR1 lapR2)
    (hStrongI : ContinuousStrongSpatialProducts false
      a b c d h gradI1 lapI2) :
    HasDerivAt
      (WCTLean.S004FullSpatialIntegral.action
        (rectangleVolume a b c d) epsilon alpha kappa theta gamma
        V (Function.uncurry u) (Function.uncurry h))
      ((∫ z, WCTLean.S004EulerSeparation.correctedEulerResidual true
          epsilon alpha kappa theta gamma
          Vprime u timeR1 accelR2 gradR1 lapR2 z.1 z.2 *
          component true (h z.1 z.2) ∂rectangleVolume a b c d) +
       (∫ z, WCTLean.S004EulerSeparation.correctedEulerResidual false
          epsilon alpha kappa theta gamma
          Vprime u timeI1 accelI2 gradI1 lapI2 z.1 z.2 *
          component false (h z.1 z.2) ∂rectangleVolume a b c d))
      0 := by
  have hReal := continuous_weak_products_integrable true
    a b c d epsilon alpha kappa theta gamma hab hcd Vprime u h hWeakR
  have hImag := continuous_weak_products_integrable false
    a b c d epsilon alpha kappa theta gamma hab hcd Vprime u h hWeakI
  have hAction : ActionRegularity a b c d epsilon alpha kappa theta gamma
      V Vprime u h bound := {
    heps := hDom.heps
    ha := hDom.ha
    hV := hDom.hV
    hmeas := hDom.hmeas
    hint := hDom.hint
    hdmeas := hDom.hdmeas
    hboundInt := hDom.hboundInt
    hlip := hDom.hlip
    hReal := hReal
    hImag := hImag
  }
  have hR := continuous_strong_products_integrable true
    a b c d hab hcd h gradR1 lapR2 hStrongR
  have hI := continuous_strong_products_integrable false
    a b c d hab hcd h gradI1 lapI2 hStrongI
  exact originalAction_hasDerivAt_euler_pairing
    a b c d epsilon alpha kappa theta gamma hab hcd
    V Vprime u h bound
    timeR1 accelR1 accelR2 gradR1 lapR1 lapR2
    timeI1 accelI1 accelI2 gradI1 lapI1 lapI2
    hAction hGreenR hGreenI hR.1 hR.2 hI.1 hI.2

end WCTLean.S004ContinuousAdmissibility
