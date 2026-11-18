import WCTLean.Models.CurvatureLpLimit

/-!
# No-gap domination for the unchanged corrected complex curvature

The regularized quotient is globally bounded in modulus by the
totalized unregularized quotient |Δψ/ψ| at every point of a supplied
complex field, even on the zero set. At a node, both the corrected
numerator and the totalized quotient vanish. The conclusion is
independent of epsilon and alpha because the regulator adds a
nonnegative term to the squared-modulus denominator.

This provides a real majorant for dominated-convergence arguments
without a uniform positive field gap. It does NOT assert that this
majorant is integrable for arbitrary WCT solutions, nor that an
arbitrary singular quotient has a classical value at a node. No
global nonlinear PDE or energy limit follows without separately
proved measurability/integrability and weak-form control.
-/

namespace WCTLean

/-- Exact pointwise domination by the (totalized) unregularized complex
quotient, including field nodes and with no global positive gap. -/
theorem theta_no_gap_domination
    (lapPsi psi : ℂ) (epsilon alpha : ℝ) :
    ‖thetaComplex lapPsi psi epsilon alpha‖ ≤ ‖lapPsi / psi‖ := by
  by_cases hpsi : psi = 0
  · subst psi
    simp [thetaComplex, complexRegularizedReciprocal]
  · have hn : 0 < ‖psi‖ := norm_pos_iff.mpr hpsi
    have hb := theta_nonnodal_uniform_bound
      lapPsi psi epsilon alpha ‖psi‖ hn (le_refl _)
    calc
      ‖thetaComplex lapPsi psi epsilon alpha‖
          ≤ (1 / ‖psi‖) * ‖lapPsi‖ := hb
      _ = ‖lapPsi / psi‖ := by
        rw [norm_div]
        ring

/-- Uniform majorant for the pointwise squared curvature energy. This
does not claim the majorant is integrable for arbitrary fields. -/
theorem theta_no_gap_energy_majorant
    (lapPsi psi : ℂ) (epsilon alpha : ℝ) :
    ‖thetaComplex lapPsi psi epsilon alpha‖ ^ 2 ≤
      ‖lapPsi / psi‖ ^ 2 := by
  exact pow_le_pow_left₀ (norm_nonneg _)
    (theta_no_gap_domination lapPsi psi epsilon alpha) 2

/-- Uniform majorant for the regulator-removal error, valid even at nodes
with Lean's zero-division convention. Integrable domination is a separate
hypothesis in subsequent Lp or energy-limit arguments. -/
theorem theta_no_gap_error_majorant
    (lapPsi psi : ℂ) (epsilon alpha : ℝ) :
    ‖thetaComplex lapPsi psi epsilon alpha -
        thetaComplex lapPsi psi 0 alpha‖ ≤ 2 * ‖lapPsi / psi‖ := by
  calc
    ‖thetaComplex lapPsi psi epsilon alpha -
        thetaComplex lapPsi psi 0 alpha‖
      ≤ ‖thetaComplex lapPsi psi epsilon alpha‖ +
          ‖thetaComplex lapPsi psi 0 alpha‖ := norm_sub_le _ _
    _ ≤ ‖lapPsi / psi‖ + ‖lapPsi / psi‖ :=
      add_le_add (theta_no_gap_domination lapPsi psi epsilon alpha)
        (theta_no_gap_domination lapPsi psi 0 alpha)
    _ = 2 * ‖lapPsi / psi‖ := by ring

end WCTLean
