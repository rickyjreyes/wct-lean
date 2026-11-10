import Mathlib
import WCTLean.Models.S004TwoComponentVariation

/-!
# Actual integrated variation of the corrected S004 local action density

The underlying integrand is the EXACT two-real-component higher-time-
derivative S004 density from S004TwoComponentVariation, including
F(|psi|²), its nonlinear exponential denominator, arbitrary
differentiable V(|psi|²), and all declared real jet coordinates.

This is a true integral first-variation theorem over ANY measured
spacetime domain (not a finite sum or an assumed derivative), derived
from Mathlib's dominated differentiation-under-integral theorem.

The explicitly stated domination/Lipschitz and measurability
assumptions are ANALYTIC REQUIREMENTS, not facts manufactured about
every WCT Sobolev field. Deriving these hypotheses from concrete
Sobolev norms and proving higher-order integration by parts to
identify the Euler-Lagrange operator remain open obligations.
-/

open MeasureTheory Filter Topology Set

namespace WCTLean.S004IntegratedVariation

open WCTLean.S004TwoComponent
open WCTLean

/-- The original corrected S004 action density evaluated on a family
of spacetime jets. -/
noncomputable def integratedDensity
    {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    (epsilon alpha kappa theta gamma : ℝ) (V : ℝ → ℝ)
    (u h : Ω → Jet) (t : ℝ) : ℝ :=
  ∫ x, localDensity epsilon alpha kappa theta gamma V
    ((u x).shift (h x) t) ∂mu

/-- The exactly computed local Gâteaux coefficient, integrated on
the same spacetime measure domain. -/
noncomputable def integratedDirection
    {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    (epsilon alpha kappa theta gamma : ℝ)
    (Vprime : Ω → ℝ) (u h : Ω → Jet) : ℝ :=
  ∫ x, localDirection epsilon alpha kappa theta gamma
    (Vprime x) (u x) (h x) ∂mu

/-- **Exact S004 integral first variation, under explicit analytic
domination hypotheses.** The pointwise derivative hypothesis comes
from the independently verified real two-component density theorem,
NOT from a postulated derivative of the action.

A common neighborhood (-1,1) and an integrable a.e. Lipschitz bound
ensure the legitimacy of differentiating under the integral.
Consequently the actual action has the stated directional derivative.

This does not yet perform the higher-order IBP needed to identify
the full Euler–Lagrange equation or prove that these hypotheses hold
for an entire Sobolev ball. -/
theorem integratedDensity_hasDerivAt_of_dominated
    {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    (epsilon alpha kappa theta gamma : ℝ) (V : ℝ → ℝ)
    (u h : Ω → Jet) (Vprime bound : Ω → ℝ)
    (heps : 0 < epsilon) (ha : 0 ≤ alpha)
    (hV : ∀ᵐ x ∂mu,
      HasDerivAt V (Vprime x)
        (realTwoComponentDensity (u x).x (u x).y))
    (hmeas : ∀ᶠ t in 𝓝 (0 : ℝ),
      AEStronglyMeasurable
        (fun x => localDensity epsilon alpha kappa theta gamma V
          ((u x).shift (h x) t)) mu)
    (hint : Integrable
      (fun x => localDensity epsilon alpha kappa theta gamma V
        ((u x).shift (h x) (0 : ℝ))) mu)
    (hdmeas : AEStronglyMeasurable
      (fun x => localDirection epsilon alpha kappa theta gamma
        (Vprime x) (u x) (h x)) mu)
    (hbound_int : Integrable bound mu)
    (hlip : ∀ᵐ x ∂mu,
      LipschitzOnWith (Real.nnabs (bound x))
        (fun t : ℝ => localDensity epsilon alpha kappa theta gamma V
          ((u x).shift (h x) t)) (Metric.ball (0 : ℝ) 1)) :
    Integrable (fun x => localDirection epsilon alpha kappa theta gamma
      (Vprime x) (u x) (h x)) mu ∧
    HasDerivAt
      (integratedDensity mu epsilon alpha kappa theta gamma V u h)
      (integratedDirection mu epsilon alpha kappa theta gamma Vprime u h) 0 := by
  have hnbhd : Metric.ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
    Metric.ball_mem_nhds (0 : ℝ) (by norm_num)
  have hdiff : ∀ᵐ x ∂mu,
      HasDerivAt
        (fun t : ℝ => localDensity epsilon alpha kappa theta gamma V
          ((u x).shift (h x) t))
        (localDirection epsilon alpha kappa theta gamma
          (Vprime x) (u x) (h x)) 0 := by
    filter_upwards [hV] with x hVx
    exact localDensity_hasDerivAt epsilon alpha kappa theta gamma
      V (u x) (h x) (Vprime x) heps ha hVx
  have h := hasDerivAt_integral_of_dominated_loc_of_lip
    hnbhd hmeas hint hdmeas hlip hbound_int hdiff
  simpa only [integratedDensity, integratedDirection] using h

end WCTLean.S004IntegratedVariation
