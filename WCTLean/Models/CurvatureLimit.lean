import Mathlib
import WCTLean.Models.ComplexCurvature

namespace WCTLean

open Filter Topology

/-!
# M2/E17: vanishing regularization, with the nodal boundary explicit

These are statements about the local quotient with a supplied Laplacian, not
continuum convergence of its PDE energy or weak equation.
-/

/-- At zero regulator amplitude the denominator is the squared modulus. -/
@[simp] theorem complexRegularizerDenominator_zero_regulator
    (psi : ℂ) (alpha : ℝ) :
    complexRegularizerDenominator psi 0 alpha = Complex.normSq psi := by
  simp [complexRegularizerDenominator]

/-- The regularized denominator is continuous in epsilon, including at zero. -/
theorem complexRegularizerDenominator_tendsto_zero
    (psi : ℂ) (alpha : ℝ) :
    Tendsto (fun epsilon : ℝ =>
      complexRegularizerDenominator psi epsilon alpha)
      (nhds 0) (nhds (Complex.normSq psi)) := by
  have hc : Continuous (fun epsilon : ℝ =>
      complexRegularizerDenominator psi epsilon alpha) := by
    unfold complexRegularizerDenominator
    fun_prop
  simpa using hc.continuousAt.tendsto

/-- The reciprocal at epsilon=0 agrees with the unregularized quotient as
a formula. The equality does not assert that this formula is defined at nodes
in the classical (non-totalized) division sense. -/
@[simp] theorem complexRegularizedReciprocal_zero_regulator
    (psi : ℂ) (alpha : ℝ) :
    complexRegularizedReciprocal psi 0 alpha =
      star psi / (Complex.normSq psi : ℂ) := by
  simp [complexRegularizedReciprocal, complexRegularizerDenominator]

/-- The zero-field branch is identically zero for every regulator value;
it cannot be identified with a reciprocal of the zero field. -/
theorem complexRegularizedReciprocal_node_all_epsilon
    (epsilon alpha : ℝ) :
    complexRegularizedReciprocal 0 epsilon alpha = 0 := by
  simp

/-- An exact error identity for the nonzero-denominator sector. -/
theorem complex_quotient_regularization_error
    (z : ℂ) (a b : ℝ) (ha : a ≠ 0) (hab : a + b ≠ 0) :
    z / ((a + b : ℝ) : ℂ) - z / (a : ℂ) =
      -(z * (b : ℂ)) / (((a + b : ℝ) : ℂ) * (a : ℂ)) := by
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have habC : ((a + b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hab
  field_simp [haC, habC]
  ring

/-- Away from nodes, the exact quotient error is the regulator contribution
divided by both nonzero denominators. This is a pointwise algebraic identity;
a norm convergence theorem still needs a lower bound on |psi|. -/
theorem complexRegularizedReciprocal_error
    (psi : ℂ) (epsilon alpha : ℝ)
    (hnorm : Complex.normSq psi ≠ 0)
    (hden : complexRegularizerDenominator psi epsilon alpha ≠ 0) :
    complexRegularizedReciprocal psi epsilon alpha -
      star psi / (Complex.normSq psi : ℂ) =
    -(star psi * ((epsilon ^ 2 *
      Real.exp (-2 * alpha * Complex.normSq psi)) : ℂ)) /
      ((complexRegularizerDenominator psi epsilon alpha : ℂ) *
        (Complex.normSq psi : ℂ)) := by
  simpa [complexRegularizedReciprocal, complexRegularizerDenominator] using
    (complex_quotient_regularization_error (star psi)
      (Complex.normSq psi)
      (epsilon ^ 2 * Real.exp (-2 * alpha * Complex.normSq psi))
      hnorm (by simpa [complexRegularizerDenominator] using hden))

end WCTLean
