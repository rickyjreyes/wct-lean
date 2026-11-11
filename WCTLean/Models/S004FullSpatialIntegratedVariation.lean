import Mathlib
import WCTLean.Models.S004FullSpatialJet

/-!
# Integrated corrected S004 complex action with all spatial gradients

For a spatial domain with d finite coordinate directions, the exact
two-real-component local S004 density is

  L = -|partial_t psi|² + sum_i |partial_i psi|² - V(|psi|²)
      + F(|psi|²) * [kappa|Delta psi - partial_t² psi|²
                     + theta|Delta psi|²
                     + gamma Re((Delta psi - partial_t² psi)
                                 conj(Delta psi))],

where F(s)=s/(s+epsilon² exp(-2 alpha s))².

This theorem takes the actual spatial-d-component jet model of this
density, proves its first variation after integration over an arbitrary
measured spacetime domain, and derives the integrated exact coefficient
from the verified pointwise full-dimensional theorem.

As required by Mathlib's dominated integral differentiation, a common
neighborhood, a.e. measurability, integrability and a local integrable
Lipschitz majorant are stated as explicit hypotheses. These are not
automatic for arbitrary Sobolev initial data; proving them from a
concrete H^s space, identifying the weak Euler-Lagrange equation and
controlling boundary terms remain separate open obligations.
-/

open MeasureTheory Filter Topology Set

namespace WCTLean.S004FullSpatialIntegral

open WCTLean.S004FullSpatialJet

noncomputable def action {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω)
    (epsilon alpha kappa theta gamma : ℝ) (V : ℝ → ℝ)
    (u h : Ω → Jet d) (t : ℝ) : ℝ :=
  ∫ x, fullLocalDensity epsilon alpha kappa theta gamma
    V (shift (u x) (h x) t) ∂mu

noncomputable def actionDirection
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    (epsilon alpha kappa theta gamma : ℝ)
    (Vprime : Ω → ℝ) (u h : Ω → Jet d) : ℝ :=
  ∫ x, fullLocalDirection epsilon alpha kappa theta gamma
    (Vprime x) (u x) (h x) ∂mu

/-- **Full finite-spatial-gradient S004 integrated first variation.**
Unlike the earlier one-gradient local theorem, this statement contains
all d spatial-gradient summands and integrates the actual corrected
two-real-component quadratic high-derivative model. It is CONDITIONAL
on exact analytic domination, not on the desired first-variation
formula. -/
theorem action_hasDerivAt_of_dominated
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    (epsilon alpha kappa theta gamma : ℝ) (V : ℝ → ℝ)
    (u h : Ω → Jet d) (Vprime bound : Ω → ℝ)
    (heps : 0 < epsilon) (ha : 0 ≤ alpha)
    (hV : ∀ᵐ x ∂mu,
      HasDerivAt V (Vprime x)
        (WCTLean.realTwoComponentDensity (u x).x (u x).y))
    (hmeas : ∀ᶠ t in 𝓝 (0 : ℝ),
      AEStronglyMeasurable
        (fun x => fullLocalDensity epsilon alpha kappa theta gamma
          V (shift (u x) (h x) t)) mu)
    (hint : Integrable
      (fun x => fullLocalDensity epsilon alpha kappa theta gamma
        V (shift (u x) (h x) (0 : ℝ))) mu)
    (hdmeas : AEStronglyMeasurable
      (fun x => fullLocalDirection epsilon alpha kappa theta gamma
        (Vprime x) (u x) (h x)) mu)
    (hbound_int : Integrable bound mu)
    (hlip : ∀ᵐ x ∂mu,
      LipschitzOnWith (Real.nnabs (bound x))
        (fun t : ℝ => fullLocalDensity epsilon alpha kappa theta gamma
          V (shift (u x) (h x) t)) (Metric.ball (0 : ℝ) 1)) :
    Integrable (fun x => fullLocalDirection epsilon alpha kappa theta gamma
      (Vprime x) (u x) (h x)) mu ∧
    HasDerivAt
      (action mu epsilon alpha kappa theta gamma V u h)
      (actionDirection mu epsilon alpha kappa theta gamma Vprime u h) 0 := by
  have hdiff : ∀ᵐ x ∂mu,
      HasDerivAt
        (fun t : ℝ => fullLocalDensity epsilon alpha kappa theta gamma
          V (shift (u x) (h x) t))
        (fullLocalDirection epsilon alpha kappa theta gamma
          (Vprime x) (u x) (h x)) 0 := by
    filter_upwards [hV] with x hVx
    exact fullLocalDensity_hasDerivAt epsilon alpha kappa theta gamma
      V (u x) (h x) (Vprime x) heps ha hVx
  have h := hasDerivAt_integral_of_dominated_loc_of_lip
    (show (0 : ℝ) < 1 by norm_num)
    hmeas hint hdmeas hlip hbound_int hdiff
  simpa only [action, actionDirection] using h

end WCTLean.S004FullSpatialIntegral
