import Mathlib
import WCTLean.Contracts.UniformCurvatureDenominator

/-!
# Exact corrected S004 radial weight calculus

For \`epsilon > 0\` and \`alpha >= 0\`, the exact corrected covariant
curvature weight is

    F(s) = s / (s + epsilon^2 * exp(-2 alpha s))^2.

This module proves its pointwise derivative as an actual Lean \`HasDerivAt\`
statement, not an assumed symbolic slope, and proves an explicit uniform
upper bound valid for all nonnegative s, including field nodes.

The derivative is
    F'(s) = (D(s)-2s D'(s))/D(s)^3
with
    D'(s) = 1-2 alpha epsilon^2 exp(-2 alpha s).

This is a local calculus theorem. Integrating variations on a Sobolev
space still requires integrability, chain rules and boundary control.
-/

namespace WCTLean

noncomputable def correctedRadialDenominator
    (epsilon alpha s : ℝ) : ℝ :=
  s + epsilon ^ 2 * Real.exp (-2 * alpha * s)

noncomputable def correctedRadialDenominatorSlope
    (epsilon alpha s : ℝ) : ℝ :=
  1 - 2 * alpha * epsilon ^ 2 * Real.exp (-2 * alpha * s)

noncomputable def correctedRadialWeight
    (epsilon alpha s : ℝ) : ℝ :=
  s / (correctedRadialDenominator epsilon alpha s) ^ 2

theorem correctedRadialDenominator_eq_complex (epsilon alpha : ℝ) (z : ℂ) :
    correctedRadialDenominator epsilon alpha (Complex.normSq z) =
      complexRegularizerDenominator z epsilon alpha := rfl

/-- The exact derivative of the denominator, including its exponential factor. -/
theorem correctedRadialDenominator_hasDerivAt
    (epsilon alpha s : ℝ) :
    HasDerivAt (correctedRadialDenominator epsilon alpha)
      (correctedRadialDenominatorSlope epsilon alpha s) s := by
  have hlinear : HasDerivAt (fun t : ℝ => -2 * alpha * t) (-2 * alpha) s := by
    convert (hasDerivAt_id s).const_mul (-2 * alpha) using 1 <;> ring
  have hscaled := hlinear.exp |>.const_mul (epsilon ^ 2)
  have hsum := (hasDerivAt_id s).add hscaled
  convert hsum using 1 <;>
    simp [correctedRadialDenominator, correctedRadialDenominatorSlope] <;>
    ring

/-- Exact quotient-rule derivative of the S004 weight, in a form that
tracks both denominator factors without cancellation at a node. -/
theorem correctedRadialWeight_hasDerivAt
    (epsilon alpha s : ℝ)
    (hD : correctedRadialDenominator epsilon alpha s ≠ 0) :
    HasDerivAt (correctedRadialWeight epsilon alpha)
      (((correctedRadialDenominator epsilon alpha s) ^ 2 -
          s * (2 * correctedRadialDenominator epsilon alpha s *
            correctedRadialDenominatorSlope epsilon alpha s)) /
        ((correctedRadialDenominator epsilon alpha s) ^ 2) ^ 2) s := by
  have hderiv := (hasDerivAt_id s).div
      ((correctedRadialDenominator_hasDerivAt epsilon alpha s).pow 2)
      (pow_ne_zero 2 hD)
  convert hderiv using 1 <;>
    simp [correctedRadialWeight] <;>
    ring

/-- The global floor also applies to the radial real representation. -/
theorem correctedRadialDenominator_floor
    (epsilon alpha s : ℝ)
    (hs : 0 ≤ s) (heps : 0 < epsilon) (ha : 0 ≤ alpha) :
    complexRegulatorFloor epsilon alpha ≤
      correctedRadialDenominator epsilon alpha s :=
  radialComplexDenominator_ge_floor s epsilon alpha hs heps ha

/-- The curvature weight has a state-independent positive upper bound,
not merely an almost-everywhere bound for a selected field. -/
theorem correctedRadialWeight_le_invFloor
    (epsilon alpha s : ℝ)
    (hs : 0 ≤ s) (heps : 0 < epsilon) (ha : 0 ≤ alpha) :
    correctedRadialWeight epsilon alpha s ≤
      1 / complexRegulatorFloor epsilon alpha := by
  have hfloor := correctedRadialDenominator_floor epsilon alpha s hs heps ha
  have hfloorPos := complexRegulatorFloor_pos epsilon alpha heps
  have hDpos : 0 < correctedRadialDenominator epsilon alpha s :=
    lt_of_lt_of_le hfloorPos hfloor
  have hsD : s ≤ correctedRadialDenominator epsilon alpha s := by
    unfold correctedRadialDenominator
    have he : 0 ≤ epsilon ^ 2 * Real.exp (-2 * alpha * s) := by
      positivity
    linarith
  have hleft : s * complexRegulatorFloor epsilon alpha ≤
      s * correctedRadialDenominator epsilon alpha s :=
    mul_le_mul_of_nonneg_left hfloor hs
  have hright : s * correctedRadialDenominator epsilon alpha s ≤
      correctedRadialDenominator epsilon alpha s *
        correctedRadialDenominator epsilon alpha s :=
    mul_le_mul_of_nonneg_right hsD hDpos.le
  have hbound := le_trans hleft hright
  unfold correctedRadialWeight
  apply (div_le_div_iff₀ (sq_pos_of_pos hDpos) hfloorPos).mpr
  nlinarith

/-- The genuine complex curvature weight is uniformly bounded for
any point of any complex field, with no assumed L-infinity bound. -/
theorem correctedComplexWeight_le_invFloor
    (z : ℂ) (epsilon alpha : ℝ)
    (heps : 0 < epsilon) (ha : 0 ≤ alpha) :
    Complex.normSq z /
      (complexRegularizerDenominator z epsilon alpha) ^ 2 ≤
      1 / complexRegulatorFloor epsilon alpha := by
  simpa only [correctedRadialDenominator_eq_complex, correctedRadialWeight] using
    correctedRadialWeight_le_invFloor epsilon alpha
      (Complex.normSq z) (Complex.normSq_nonneg z) heps ha

end WCTLean
