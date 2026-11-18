import Mathlib
import WCTLean.Models.ComplexCurvature

/-!
# M2/E17/M6B: exact nonzero-field regularization limit (wct-lean #22)

This module addresses the original, maintained modulus-squared curvature
quotient, not the historically printed scalar denominator.  At a fixed
nonzero complex field value the *full complex curvature quotient* tends
to `-Delta psi / psi` as epsilon tends to zero.  The result is stated
both for unrestricted epsilon -> 0 and the physically relevant
one-sided epsilon downarrow 0.

At field nodes the regularized curvature is zero for every positive
epsilon even when the supplied Laplacian is nonzero.  In particular the
nonzero-field theorem cannot be invoked at a node.  The definition at
epsilon = 0 uses Lean's totalized division and must not be interpreted
as an everywhere-defined classical unregularized quotient.

No convergence in a Sobolev/operator norm, dominated convergence across
a nodal set, or full nonlinear PDE limit is claimed here.
-/

noncomputable section

namespace WCTLean

/-- At epsilon=0 the corrected real denominator is the squared modulus. -/
theorem complexRegularizerDenominator_zero_epsilon
    (psi : ℂ) (alpha : ℝ) :
    complexRegularizerDenominator psi 0 alpha = Complex.normSq psi := by
  simp [complexRegularizerDenominator]

/-- The full *complex* curvature quotient equals -Delta psi / psi
at epsilon=0 whenever the field value does not vanish. -/
theorem thetaComplex_zero_epsilon
    (lapPsi psi : ℂ) (alpha : ℝ) (hpsi : psi ≠ 0) :
    thetaComplex lapPsi psi 0 alpha = -(lapPsi / psi) := by
  have hconj : (starRingEnd ℂ) psi ≠ 0 := by
    simpa using hpsi
  have hnorm : ((Complex.normSq psi : ℝ) : ℂ) =
      psi * (starRingEnd ℂ) psi := by
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [thetaComplex_canonical_formula]
  simp only [complexRegularizerDenominator, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_mul, add_zero]
  rw [hnorm]
  field_simp [hpsi, hconj]
  ring

/-- At a field node the corrected curvature is identically zero for
any supplied Laplacian and any epsilon. This is not a definition of
the singular classical quotient -Delta psi / psi at psi=0. -/
theorem thetaComplex_field_node
    (lapPsi : ℂ) (epsilon alpha : ℝ) :
    thetaComplex lapPsi 0 epsilon alpha = 0 := by
  simp [thetaComplex]

/-- Fixed nonzero complex-field jets admit an ordinary epsilon-to-zero
limit of the actual M2/E17/M6B curvature operator. -/
theorem thetaComplex_nonzero_limit
    (lapPsi psi : ℂ) (alpha : ℝ) (hpsi : psi ≠ 0) :
    Filter.Tendsto (fun epsilon : ℝ => thetaComplex lapPsi psi epsilon alpha)
      (nhds 0) (nhds (-(lapPsi / psi))) := by
  have hnorm : Complex.normSq psi ≠ 0 :=
    (Complex.normSq_pos.mpr hpsi).ne'
  have hden : complexRegularizerDenominator psi 0 alpha ≠ 0 := by
    simpa [complexRegularizerDenominator] using hnorm
  have hdenCont : ContinuousAt
      (fun epsilon : ℝ =>
        ((complexRegularizerDenominator psi epsilon alpha : ℝ) : ℂ)) 0 := by
    unfold complexRegularizerDenominator
    fun_prop
  have hcont : ContinuousAt
      (fun epsilon : ℝ => thetaComplex lapPsi psi epsilon alpha) 0 := by
    unfold thetaComplex complexRegularizedReciprocal
    exact continuousAt_const.mul
      (continuousAt_const.div hdenCont (by exact_mod_cast hden))
  convert hcont.tendsto using 1
  exact congrArg nhds ((thetaComplex_zero_epsilon lapPsi psi alpha hpsi).symm)

/-- The same full complex quotient limit along positive epsilon values. -/
theorem thetaComplex_downarrow_zero
    (lapPsi psi : ℂ) (alpha : ℝ) (hpsi : psi ≠ 0) :
    Filter.Tendsto (fun epsilon : ℝ => thetaComplex lapPsi psi epsilon alpha)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-(lapPsi / psi))) :=
  (thetaComplex_nonzero_limit lapPsi psi alpha hpsi).mono_left
    nhdsWithin_le_nhds

end WCTLean
