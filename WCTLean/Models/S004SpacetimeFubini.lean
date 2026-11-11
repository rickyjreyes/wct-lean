import Mathlib
import WCTLean.Models.S004TemporalEuler
import WCTLean.Models.S004SpatialEuler

/-!
# Actual Fubini theorem for finite-time, periodic-space S004 action integrals

A decisive analytic step beyond independent temporal/spatial jet identities:
Mathlib's interval-integral Fubini theorem proves that TWO ACTUAL
Lebesgue interval integrals over the same spacetime rectangle can be
interchanged, under the original (not conclusion-shaped) product
integrability assumption on their integrand.

This theorem uses real (continuous) time/space coordinates, rather than
a finite grid, arbitrary bilinear integration axiom, or an abstract
formal adjoint. Periodic one-dimensional space is represented by one
fundamental cell with identified endpoints; the field's periodic
boundary conditions are supplied by the real Green theorems.

The remaining open step is deriving integrability for the full
nonlinear corrected S004 integrands from concrete Sobolev hypotheses.
-/

open MeasureTheory Set
open scoped Interval

namespace WCTLean.S004SpacetimeFubini

/-- Exact Fubini swap for a two-dimensional finite spacetime rectangle
under actual product-measure Lebesgue integrability. -/
theorem rectangle_integral_swap
    (a b c d : ℝ) (f : ℝ → ℝ → ℝ)
    (hcd : c ≤ d)
    (hf : IntegrableOn (Function.uncurry f)
      (Set.uIoc a b ×ˢ Set.uIoc c d)) :
    (∫ t in a..b, ∫ x in c..d, f t x) =
      (∫ x in c..d, ∫ t in a..b, f t x) := by
  have hproduct :
      Integrable (Function.uncurry f)
        ((volume.restrict (uIoc a b)).prod
          (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ ℝ]
    simpa only [IntegrableOn, uIoc_of_le hcd] using hf
  simp_rw [intervalIntegral.integral_of_le hcd]
  exact MeasureTheory.intervalIntegral_integral_swap hproduct

/-- Each corrected S004 local derivative term has the same spacetime
integral in time-major or space-major order, once its real
product-measure integrability is established. -/
theorem corrected_density_direction_swap
    (a b c d : ℝ)
    (epsilon alpha kappa theta gamma : ℝ)
    (Vprime : ℝ → ℝ → ℝ)
    (u h : ℝ → ℝ → WCTLean.S004FullSpatialJet.Jet 1)
    (hcd : c ≤ d)
    (hint : IntegrableOn
      (Function.uncurry (fun t x =>
        WCTLean.S004FullSpatialJet.fullLocalDirection
          epsilon alpha kappa theta gamma
          (Vprime t x) (u t x) (h t x)))
      (Set.uIoc a b ×ˢ Set.uIoc c d)) :
    (∫ t in a..b, ∫ x in c..d,
      WCTLean.S004FullSpatialJet.fullLocalDirection
        epsilon alpha kappa theta gamma
        (Vprime t x) (u t x) (h t x)) =
    (∫ x in c..d, ∫ t in a..b,
      WCTLean.S004FullSpatialJet.fullLocalDirection
        epsilon alpha kappa theta gamma
        (Vprime t x) (u t x) (h t x)) := by
  exact rectangle_integral_swap a b c d _ hcd hint

end WCTLean.S004SpacetimeFubini
