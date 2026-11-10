import Mathlib
import WCTLean.Models.S004EulerCoefficients
import WCTLean.Models.S004IntervalGreen

/-!
# Exact temporal Euler–Lagrange integration for the corrected S004 action

This module combines TWO independently proved results:
1. the actual corrected S004 first-variation momenta including the
   nonlinear F'(|psi|²) and mixed fourth-order quadratic curvature form;
2. genuine first- and second-order real interval integration by parts
   proved via the fundamental theorem of calculus.

It proves that the velocity and acceleration variations contribute
-deriv(P_t) + deriv²(P_tt) to the strong temporal EL expression for
each real component, with exact boundary trace cancellation.

The test jets are required to be consistent: the variation's velocity
and acceleration coordinates are ACTUAL first and second time
derivatives of one scalar test field on the interval. The coefficient
functions are assumed to possess the required integrable first/second
time derivatives; these are ordinary REGULARITY premises, not the
Euler–Lagrange equation.

This theorem is a genuine 1D temporal integration identity for the
actual nonlinear S004 coefficients. Multidimensional spatial IBP,
Fubini and Sobolev closure remain OPEN; it does not purport to be
the complete spacetime Euler–Lagrange equation.
-/

open MeasureTheory Set
open scoped Interval

namespace WCTLean.S004TemporalEuler

open WCTLean.S004EulerCoefficients
open WCTLean.S004FullSpatialJet

/-- Time momentum from the exact negative velocity-square term. -/
def timeMomentumX {d : ℕ} (u : Jet d) : ℝ := -2 * u.vx
def timeMomentumY {d : ℕ} (u : Jet d) : ℝ := -2 * u.vy

/-- A complete temporal component integration identity, using the
*actual* nonlinear S004 force, first-time momentum and acceleration
momentum. All needed boundary trace and regularity hypotheses are
explicit and independent of the claimed Euler–Lagrange result. -/
theorem x_component_temporal_euler
    {d : ℕ} (a b : ℝ) (u h : ℝ → Jet d)
    (epsilon alpha kappa theta gamma : ℝ) (Vprime : ℝ → ℝ)
    (momentum1 accel1 accel2 : ℝ → ℝ)
    (hmomentum : ∀ t ∈ [[a,b]],
      HasDerivAt (fun s : ℝ => timeMomentumX (u s)) (momentum1 t) t)
    (haccel : ∀ t ∈ [[a,b]],
      HasDerivAt (fun s : ℝ =>
        accelX epsilon alpha kappa gamma (u s)) (accel1 t) t)
    (haccel1 : ∀ t ∈ [[a,b]],
      HasDerivAt accel1 (accel2 t) t)
    (hfield : ∀ t ∈ [[a,b]],
      HasDerivAt (fun s : ℝ => (h s).x) (h t).vx t)
    (hfield1 : ∀ t ∈ [[a,b]],
      HasDerivAt (fun s : ℝ => (h s).vx) (h t).ax t)
    (hmInt : IntervalIntegrable momentum1 volume a b)
    (ha1Int : IntervalIntegrable accel1 volume a b)
    (ha2Int : IntervalIntegrable accel2 volume a b)
    (hvInt : IntervalIntegrable (fun t => (h t).vx) volume a b)
    (haInt : IntervalIntegrable (fun t => (h t).ax) volume a b)
    (hxa : (h a).x = 0) (hxb : (h b).x = 0)
    (hvxa : (h a).vx = 0) (hvxb : (h b).vx = 0) :
    (∫ t in a..b,
       forceX epsilon alpha kappa theta gamma (Vprime t) (u t) * (h t).x) +
    (∫ t in a..b, timeMomentumX (u t) * (h t).vx) +
    (∫ t in a..b,
       accelX epsilon alpha kappa gamma (u t) * (h t).ax) =
    (∫ t in a..b,
       forceX epsilon alpha kappa theta gamma (Vprime t) (u t) * (h t).x) -
    (∫ t in a..b, momentum1 t * (h t).x) +
    (∫ t in a..b, accel2 t * (h t).x) := by
  have hfirst := WCTLean.S004IntervalGreen.integral_mul_first_deriv_eq_neg
    a b (fun t => timeMomentumX (u t)) momentum1
      (fun t => (h t).x) (fun t => (h t).vx)
    hmomentum hfield hmInt hvInt hxa hxb
  have hsecond := WCTLean.S004IntervalGreen.integral_mul_second_deriv_eq
    a b (fun t => accelX epsilon alpha kappa gamma (u t))
      accel1 accel2
      (fun t => (h t).x) (fun t => (h t).vx) (fun t => (h t).ax)
    haccel haccel1 hfield hfield1 ha1Int ha2Int hvInt haInt
    hxa hxb hvxa hvxb
  rw [hfirst, hsecond]
  ring

/-- The second real component has the *same correct signs* and the
same exact nonlinear coupled curvature coefficient, derived by
ordinary temporal integration by parts on the admissible test jet. -/
theorem y_component_temporal_euler
    {d : ℕ} (a b : ℝ) (u h : ℝ → Jet d)
    (epsilon alpha kappa theta gamma : ℝ) (Vprime : ℝ → ℝ)
    (momentum1 accel1 accel2 : ℝ → ℝ)
    (hmomentum : ∀ t ∈ [[a,b]],
      HasDerivAt (fun s : ℝ => timeMomentumY (u s)) (momentum1 t) t)
    (haccel : ∀ t ∈ [[a,b]],
      HasDerivAt (fun s : ℝ =>
        accelY epsilon alpha kappa gamma (u s)) (accel1 t) t)
    (haccel1 : ∀ t ∈ [[a,b]],
      HasDerivAt accel1 (accel2 t) t)
    (hfield : ∀ t ∈ [[a,b]],
      HasDerivAt (fun s : ℝ => (h s).y) (h t).vy t)
    (hfield1 : ∀ t ∈ [[a,b]],
      HasDerivAt (fun s : ℝ => (h s).vy) (h t).ay t)
    (hmInt : IntervalIntegrable momentum1 volume a b)
    (ha1Int : IntervalIntegrable accel1 volume a b)
    (ha2Int : IntervalIntegrable accel2 volume a b)
    (hvInt : IntervalIntegrable (fun t => (h t).vy) volume a b)
    (haInt : IntervalIntegrable (fun t => (h t).ay) volume a b)
    (hya : (h a).y = 0) (hyb : (h b).y = 0)
    (hvya : (h a).vy = 0) (hvyb : (h b).vy = 0) :
    (∫ t in a..b,
       forceY epsilon alpha kappa theta gamma (Vprime t) (u t) * (h t).y) +
    (∫ t in a..b, timeMomentumY (u t) * (h t).vy) +
    (∫ t in a..b,
       accelY epsilon alpha kappa gamma (u t) * (h t).ay) =
    (∫ t in a..b,
       forceY epsilon alpha kappa theta gamma (Vprime t) (u t) * (h t).y) -
    (∫ t in a..b, momentum1 t * (h t).y) +
    (∫ t in a..b, accel2 t * (h t).y) := by
  have hfirst := WCTLean.S004IntervalGreen.integral_mul_first_deriv_eq_neg
    a b (fun t => timeMomentumY (u t)) momentum1
      (fun t => (h t).y) (fun t => (h t).vy)
    hmomentum hfield hmInt hvInt hya hyb
  have hsecond := WCTLean.S004IntervalGreen.integral_mul_second_deriv_eq
    a b (fun t => accelY epsilon alpha kappa gamma (u t))
      accel1 accel2
      (fun t => (h t).y) (fun t => (h t).vy) (fun t => (h t).ay)
    haccel haccel1 hfield hfield1 ha1Int ha2Int hvInt haInt
    hya hyb hvya hvyb
  rw [hfirst, hsecond]
  ring

end WCTLean.S004TemporalEuler
