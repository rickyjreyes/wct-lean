import Mathlib
import WCTLean.Models.S004EulerCoefficients
import WCTLean.Models.S004IntervalGreen

/-!
# Exact one-dimensional periodic spatial Euler contributions for S004

For a one-dimensional periodic spatial cell, the corrected original
S004 jet has gradient g=partial_x psi and Laplacian b=partial_x² psi.
This file proves the integration-by-parts transfer of the genuine
gradient and nonlinear-regulator-weighted Laplacian momenta to the
strong Euler expression:
     -partial_x (2 g) + partial_x² (F(|psi|²) K_b).

The mixed S004 curvature form K and the original denominator are used
through S004EulerCoefficients.lapX/lapY; they are NOT approximated.

All actual derivatives, coefficient regularity, periodic 0th/1st
traces and interval integrability are explicitly required. The
identities are proved by applying the independently verified
interval-integral Green lemmas, not by assuming the desired EL formula.

The two-dimensional spacetime Fubini/adjoint assembly and Sobolev
phase-space justification are still open.
-/

open MeasureTheory Set
open scoped Interval

namespace WCTLean.S004SpatialEuler

open WCTLean.S004FullSpatialJet
open WCTLean.S004EulerCoefficients
open WCTLean.S004IntervalGreen

def gradientMomentumX (u : Jet 1) : ℝ := 2 * u.gx 0
def gradientMomentumY (u : Jet 1) : ℝ := 2 * u.gy 0

/-- True periodic spatial integration by parts for Re psi: the
`gradientMomentumX` and regulator-weighted `lapX` are exactly the
gradient and Laplacian momenta derived from the ORIGINAL S004 action. -/
theorem x_component_periodic_euler
    (a b : ℝ) (u h : ℝ → Jet 1)
    (epsilon alpha kappa theta gamma : ℝ)
    (gradient1 lap1 lap2 : ℝ → ℝ)
    (hgradient : ∀ z ∈ [[a,b]],
      HasDerivAt (fun s : ℝ => gradientMomentumX (u s)) (gradient1 z) z)
    (hlap : ∀ z ∈ [[a,b]],
      HasDerivAt (fun s : ℝ =>
        lapX epsilon alpha kappa theta gamma (u s)) (lap1 z) z)
    (hlap1 : ∀ z ∈ [[a,b]], HasDerivAt lap1 (lap2 z) z)
    (hfield : ∀ z ∈ [[a,b]],
      HasDerivAt (fun s : ℝ => (h s).x) ((h z).gx 0) z)
    (hfield1 : ∀ z ∈ [[a,b]],
      HasDerivAt (fun s : ℝ => (h s).gx 0) ((h z).bx) z)
    (hg1Int : IntervalIntegrable gradient1 volume a b)
    (hl1Int : IntervalIntegrable lap1 volume a b)
    (hl2Int : IntervalIntegrable lap2 volume a b)
    (hgradInt : IntervalIntegrable (fun z => (h z).gx 0) volume a b)
    (hlapInt : IntervalIntegrable (fun z => (h z).bx) volume a b)
    (hgradPer : gradientMomentumX (u b) = gradientMomentumX (u a))
    (hlapPer : lapX epsilon alpha kappa theta gamma (u b) =
      lapX epsilon alpha kappa theta gamma (u a))
    (hlap1Per : lap1 b = lap1 a)
    (hfieldPer : (h b).x = (h a).x)
    (hfield1Per : (h b).gx 0 = (h a).gx 0) :
    (∫ z in a..b, gradientMomentumX (u z) * (h z).gx 0) +
    (∫ z in a..b,
      lapX epsilon alpha kappa theta gamma (u z) * (h z).bx) =
    -(∫ z in a..b, gradient1 z * (h z).x) +
    (∫ z in a..b, lap2 z * (h z).x) := by
  have hfirst := integral_mul_first_deriv_periodic
    a b (fun z => gradientMomentumX (u z)) gradient1
      (fun z => (h z).x) (fun z => (h z).gx 0)
    hgradient hfield hg1Int hgradInt hgradPer hfieldPer
  have hsecond := integral_mul_second_deriv_periodic
    a b (fun z => lapX epsilon alpha kappa theta gamma (u z))
      lap1 lap2
      (fun z => (h z).x) (fun z => (h z).gx 0)
      (fun z => (h z).bx)
    hlap hlap1 hfield hfield1 hl1Int hl2Int hgradInt hlapInt
    hlapPer hlap1Per hfieldPer hfield1Per
  rw [hfirst, hsecond]

/-- Imaginary component of the SAME corrected periodic S004 action,
with the full nonlinear density weight retained in the Laplacian
momentum and genuine periodic trace cancellation. -/
theorem y_component_periodic_euler
    (a b : ℝ) (u h : ℝ → Jet 1)
    (epsilon alpha kappa theta gamma : ℝ)
    (gradient1 lap1 lap2 : ℝ → ℝ)
    (hgradient : ∀ z ∈ [[a,b]],
      HasDerivAt (fun s : ℝ => gradientMomentumY (u s)) (gradient1 z) z)
    (hlap : ∀ z ∈ [[a,b]],
      HasDerivAt (fun s : ℝ =>
        lapY epsilon alpha kappa theta gamma (u s)) (lap1 z) z)
    (hlap1 : ∀ z ∈ [[a,b]], HasDerivAt lap1 (lap2 z) z)
    (hfield : ∀ z ∈ [[a,b]],
      HasDerivAt (fun s : ℝ => (h s).y) ((h z).gy 0) z)
    (hfield1 : ∀ z ∈ [[a,b]],
      HasDerivAt (fun s : ℝ => (h s).gy 0) ((h z).bY) z)
    (hg1Int : IntervalIntegrable gradient1 volume a b)
    (hl1Int : IntervalIntegrable lap1 volume a b)
    (hl2Int : IntervalIntegrable lap2 volume a b)
    (hgradInt : IntervalIntegrable (fun z => (h z).gy 0) volume a b)
    (hlapInt : IntervalIntegrable (fun z => (h z).bY) volume a b)
    (hgradPer : gradientMomentumY (u b) = gradientMomentumY (u a))
    (hlapPer : lapY epsilon alpha kappa theta gamma (u b) =
      lapY epsilon alpha kappa theta gamma (u a))
    (hlap1Per : lap1 b = lap1 a)
    (hfieldPer : (h b).y = (h a).y)
    (hfield1Per : (h b).gy 0 = (h a).gy 0) :
    (∫ z in a..b, gradientMomentumY (u z) * (h z).gy 0) +
    (∫ z in a..b,
      lapY epsilon alpha kappa theta gamma (u z) * (h z).bY) =
    -(∫ z in a..b, gradient1 z * (h z).y) +
    (∫ z in a..b, lap2 z * (h z).y) := by
  have hfirst := integral_mul_first_deriv_periodic
    a b (fun z => gradientMomentumY (u z)) gradient1
      (fun z => (h z).y) (fun z => (h z).gy 0)
    hgradient hfield hg1Int hgradInt hgradPer hfieldPer
  have hsecond := integral_mul_second_deriv_periodic
    a b (fun z => lapY epsilon alpha kappa theta gamma (u z))
      lap1 lap2
      (fun z => (h z).y) (fun z => (h z).gy 0)
      (fun z => (h z).bY)
    hlap hlap1 hfield hfield1 hl1Int hl2Int hgradInt hlapInt
    hlapPer hlap1Per hfieldPer hfield1Per
  rw [hfirst, hsecond]

end WCTLean.S004SpatialEuler
