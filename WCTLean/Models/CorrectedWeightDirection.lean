import Mathlib
import WCTLean.Models.CorrectedWeightCalculus

/-!
# Real two-component direction of the corrected S004 curvature weight

For a complex field psi = x + i y, take the real direction h = a + i b.
The squared amplitude along psi(t) = psi + t h is
  rho(t) = (x+t*a)^2 + (y+t*b)^2,
so rho'(0) = 2*(x*a+y*b).

The true S004 curvature coefficient F(rho) is differentiable along
every such real variation, with derivative
  F'(rho) * 2 Re(conj(psi)*h).

This explicitly handles the non-holomorphic dependence on |psi|^2.
It is a field-point directional derivative, not integration of the
full spacetime action.
-/

namespace WCTLean

noncomputable def realTwoComponentDensity (x y : ℝ) : ℝ :=
  x ^ 2 + y ^ 2

noncomputable def realTwoComponentWeight
    (epsilon alpha x y : ℝ) : ℝ :=
  correctedRadialWeight epsilon alpha (realTwoComponentDensity x y)

/-- Exact real directional derivative of |psi|^2. -/
theorem realTwoComponentDensity_hasDerivAt
    (x y dx dy : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        realTwoComponentDensity (x + t * dx) (y + t * dy))
      (2 * (x * dx + y * dy)) 0 := by
  have hx : HasDerivAt (fun t : ℝ => x + t * dx) dx 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_mul dx).const_add x using 1
    · funext t
      simp only [id_eq]
      ring
    · ring
  have hy : HasDerivAt (fun t : ℝ => y + t * dy) dy 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_mul dy).const_add y using 1
    · funext t
      simp only [id_eq]
      ring
    · ring
  have h := (hx.pow 2).add (hy.pow 2)
  convert h using 1 <;>
    simp [realTwoComponentDensity] <;>
    ring

noncomputable def correctedWeightRadialSlope
    (epsilon alpha s : ℝ) : ℝ :=
  let D := correctedRadialDenominator epsilon alpha s
  (D ^ 2 - s * (2 * D * correctedRadialDenominatorSlope epsilon alpha s)) /
    (D ^ 2) ^ 2

theorem correctedWeightRadialSlope_hasDerivAt
    (epsilon alpha s : ℝ)
    (hD : correctedRadialDenominator epsilon alpha s ≠ 0) :
    HasDerivAt (correctedRadialWeight epsilon alpha)
      (correctedWeightRadialSlope epsilon alpha s) s := by
  simpa only [correctedWeightRadialSlope] using
    correctedRadialWeight_hasDerivAt epsilon alpha s hD

/-- Exact real directional derivative of the corrected S004 weight.
The denominator is nonzero for every field on the full complex plane
when epsilon > 0; no assumption psi != 0 is required. -/
theorem realTwoComponentWeight_hasDerivAt
    (epsilon alpha x y dx dy : ℝ)
    (heps : 0 < epsilon) (ha : 0 ≤ alpha) :
    HasDerivAt
      (fun t : ℝ =>
        realTwoComponentWeight epsilon alpha
          (x + t * dx) (y + t * dy))
      (correctedWeightRadialSlope epsilon alpha
          (realTwoComponentDensity x y) *
        (2 * (x * dx + y * dy))) 0 := by
  have hrhoNonneg : 0 ≤ realTwoComponentDensity x y := by
    unfold realTwoComponentDensity
    positivity
  have hfloor := correctedRadialDenominator_floor epsilon alpha
      (realTwoComponentDensity x y) hrhoNonneg heps ha
  have hD : correctedRadialDenominator epsilon alpha
      (realTwoComponentDensity x y) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le
      (complexRegulatorFloor_pos epsilon alpha heps) hfloor)
  have hF : HasDerivAt (correctedRadialWeight epsilon alpha)
      (correctedWeightRadialSlope epsilon alpha (realTwoComponentDensity x y))
      (realTwoComponentDensity (x + 0 * dx) (y + 0 * dy)) := by
    simpa only [zero_mul, add_zero] using
      correctedWeightRadialSlope_hasDerivAt epsilon alpha
        (realTwoComponentDensity x y) hD
  have hweight := hF.comp 0
    (realTwoComponentDensity_hasDerivAt x y dx dy)
  simpa only [realTwoComponentWeight] using hweight

end WCTLean
