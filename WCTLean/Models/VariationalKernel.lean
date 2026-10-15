import Mathlib
import WCTLean.Models.ComplexCurvature

namespace WCTLean

/-!
# M2/E17/M6B: local directional variation of the corrected complex quotient

This covers the exact denominator derivative and formal quotient variation.
The complex numerator's tangent uses the real-linear conjugation map. The
Laplacian/gradient integration-by-parts and function-space first variation of
the full WCT action remain distinct continuum targets (#17).
-/

/-- The radial denominator in the corrected modulus-squared curvature law. -/
noncomputable def radialCurvatureDenominator
    (q epsilon alpha : ℝ) : ℝ :=
  q + epsilon ^ 2 * Real.exp (-2 * alpha * q)

/-- Its exact derivative with respect to squared modulus q. -/
noncomputable def radialCurvatureDenominatorSlope
    (q epsilon alpha : ℝ) : ℝ :=
  1 - 2 * alpha * epsilon ^ 2 * Real.exp (-2 * alpha * q)

/-- Kernel-checked derivative of the exponential regularizer, including its
nonconstant denominator contribution. -/
theorem radialCurvatureDenominator_hasDerivAt
    (q epsilon alpha : ℝ) :
    HasDerivAt (fun s : ℝ => radialCurvatureDenominator s epsilon alpha)
      (radialCurvatureDenominatorSlope q epsilon alpha) q := by
  have hlinear : HasDerivAt (fun s : ℝ => -2 * alpha * s) (-2 * alpha) q := by
    convert (hasDerivAt_id q).const_mul (-2 * alpha) using 1 <;> ring
  have hexp := hlinear.exp
  have hscaled := hexp.const_mul (epsilon ^ 2)
  have hsum := (hasDerivAt_id q).add hscaled
  convert hsum using 1 <;> simp [radialCurvatureDenominator,
    radialCurvatureDenominatorSlope] <;> ring

/-- The corrected denominator is the radial scalar function evaluated at
the exact squared modulus. -/
theorem radialCurvatureDenominator_of_complex
    (psi : ℂ) (epsilon alpha : ℝ) :
    radialCurvatureDenominator (Complex.normSq psi) epsilon alpha =
      complexRegularizerDenominator psi epsilon alpha := rfl

/-- Real directional variation of the squared modulus along h, expressed
without incorrectly assuming complex holomorphic differentiability. -/
def squaredModulusDirection (psi h : ℂ) : ℝ :=
  2 * (star psi * h).re

/-- Tangent contribution of both the squared modulus and exponential
regularizer. The source direction is supplied explicitly. -/
noncomputable def complexDenominatorDirection
    (psi h : ℂ) (epsilon alpha : ℝ) : ℝ :=
  squaredModulusDirection psi h *
    radialCurvatureDenominatorSlope (Complex.normSq psi) epsilon alpha

/-- The full local curvature numerator and its real-direction tangent;
lapH is the supplied Laplacian of the variation h. -/
def curvatureNumerator (lapPsi psi : ℂ) : ℂ := -(lapPsi * star psi)

def curvatureNumeratorDirection (lapPsi lapH psi h : ℂ) : ℂ :=
  -(lapH * star psi + lapPsi * star h)

/-- Quotient-rule tangent: both numerator and denominator must vary. -/
noncomputable def correctedCurvatureDirection
    (lapPsi lapH psi h : ℂ) (epsilon alpha : ℝ) : ℂ :=
  let D := complexRegularizerDenominator psi epsilon alpha
  curvatureNumeratorDirection lapPsi lapH psi h / (D : ℂ) -
    curvatureNumerator lapPsi psi *
      (complexDenominatorDirection psi h epsilon alpha : ℂ) / ((D : ℂ) ^ 2)

/-- The two quotient-rule terms combine to the exact rational first
variation, provided the corrected denominator does not vanish. -/
theorem correctedCurvatureDirection_quotient
    (lapPsi lapH psi h : ℂ) (epsilon alpha : ℝ)
    (hD : complexRegularizerDenominator psi epsilon alpha ≠ 0) :
    correctedCurvatureDirection lapPsi lapH psi h epsilon alpha =
    (curvatureNumeratorDirection lapPsi lapH psi h *
        (complexRegularizerDenominator psi epsilon alpha : ℂ) -
      curvatureNumerator lapPsi psi *
        (complexDenominatorDirection psi h epsilon alpha : ℂ)) /
      (complexRegularizerDenominator psi epsilon alpha : ℂ) ^ 2 := by
  have hDC : (complexRegularizerDenominator psi epsilon alpha : ℂ) ≠ 0 := by
    exact_mod_cast hD
  unfold correctedCurvatureDirection
  dsimp
  field_simp [hDC]
  ring

/-- For epsilon > 0 the exact quotient variation is globally algebraically
well-defined even at nodes. This is a local identity, not integration of
a fourth-order field functional. -/
theorem correctedCurvatureDirection_positive_regulator
    (lapPsi lapH psi h : ℂ) (epsilon alpha : ℝ) (heps : 0 < epsilon) :
    correctedCurvatureDirection lapPsi lapH psi h epsilon alpha =
    (curvatureNumeratorDirection lapPsi lapH psi h *
        (complexRegularizerDenominator psi epsilon alpha : ℂ) -
      curvatureNumerator lapPsi psi *
        (complexDenominatorDirection psi h epsilon alpha : ℂ)) /
      (complexRegularizerDenominator psi epsilon alpha : ℂ) ^ 2 := by
  exact correctedCurvatureDirection_quotient lapPsi lapH psi h epsilon alpha
    (complexRegularizerDenominator_ne_zero psi epsilon alpha heps)

end WCTLean
