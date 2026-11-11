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

/-! ## Discharging product integrability from actual continuity -/

/-- Continuous nonlinear action densities on a compact spacetime
rectangle are genuinely product-measure integrable. This removes the
independent Fubini-integrability hypothesis when S004 field jets
and the corrected nonlinear quotient are known to be continuous.
The proof uses local finiteness of the actual Lebesgue volume on ℝ²,
not an artificial integrability axiom. -/
theorem continuous_rectangle_integrable
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (Function.uncurry f)) :
    IntegrableOn (Function.uncurry f)
      (uIoc a b ×ˢ uIoc c d) := by
  have hcompact : IsCompact ((Icc a b) ×ˢ (Icc c d)) :=
    isCompact_Icc.prod isCompact_Icc
  have hfull : IntegrableOn (Function.uncurry f)
      ((Icc a b) ×ˢ (Icc c d)) :=
    hf.continuousOn.integrableOn_compact hcompact
  apply hfull.mono_set
  rintro ⟨t,x⟩ ⟨ht,hx⟩
  change t ∈ Icc a b ∧ x ∈ Icc c d
  rw [uIoc_of_le hab] at ht
  rw [uIoc_of_le hcd] at hx
  exact ⟨Ioc_subset_Icc_self ht, Ioc_subset_Icc_self hx⟩

/-- Concrete continuous-field Fubini theorem with NO abstract
integrability premise. Continuous original S004 action integrands
on bounded rectangles fit here once their jet regularity is proved. -/
theorem continuous_rectangle_integral_swap
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d)
    (f : ℝ → ℝ → ℝ)
    (hf : Continuous (Function.uncurry f)) :
    (∫ t in a..b, ∫ x in c..d, f t x) =
      (∫ x in c..d, ∫ t in a..b, f t x) := by
  exact rectangle_integral_swap a b c d f hcd
    (continuous_rectangle_integrable a b c d hab hcd f hf)

end WCTLean.S004SpacetimeFubini
