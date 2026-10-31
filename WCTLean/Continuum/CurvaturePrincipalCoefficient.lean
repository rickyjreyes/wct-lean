import WCTLean.Models.ComplexCurvature

/-!
# Corrected curvature operator: principal-coefficient degeneracy

These are statements about the exact corrected M2/E17 pointwise operator.
In particular, a positive denominator is not a uniform ellipticity
estimate for the second-order principal multiplier.
-/

namespace WCTLean.Continuum

/-- The curvature quotient vanishes at every field node, regardless of its
prescribed Laplacian. This is a genuine quasilinear degeneracy, but by itself
does not establish that an evolution is ill-posed. -/
theorem corrected_curvature_vanishes_at_field_node
    (lapPsi : ℂ) (epsilon alpha : ℝ) :
    thetaComplex lapPsi 0 epsilon alpha = 0 := by
  simp [thetaComplex]

/-- For fixed psi the corrected curvature operator is additive in the
Laplacian input. The multiplier still depends nonlinearly on psi. -/
theorem corrected_curvature_laplacian_add
    (a b psi : ℂ) (epsilon alpha : ℝ) :
    thetaComplex (a + b) psi epsilon alpha =
      thetaComplex a psi epsilon alpha +
      thetaComplex b psi epsilon alpha := by
  unfold thetaComplex
  ring

/-- For fixed psi the curvature operator is complex-homogeneous in its
Laplacian input. This does not make it a linear differential operator in psi. -/
theorem corrected_curvature_laplacian_smul
    (c a psi : ℂ) (epsilon alpha : ℝ) :
    thetaComplex (c * a) psi epsilon alpha =
      c * thetaComplex a psi epsilon alpha := by
  unfold thetaComplex
  ring

/-- No strictly positive uniform lower bound exists for the modulus of the
*quotient's own* Laplacian coefficient over all field values.
This is not a proof that the full evolution's principal symbol loses
ellipticity, since that depends on all terms of the governing equation. -/
theorem no_positive_uniform_quotient_coefficient_lower_bound
    (epsilon alpha : ℝ) (hepsilon : 0 < epsilon) :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ psi : ℂ, c ≤ ‖complexRegularizedReciprocal psi epsilon alpha‖ := by
  rintro ⟨c, hc, hbound⟩
  have hzero : c ≤ 0 := by
    simpa using hbound 0
  linarith

#print axioms WCTLean.Continuum.corrected_curvature_vanishes_at_field_node
#print axioms WCTLean.Continuum.no_positive_uniform_quotient_coefficient_lower_bound

end WCTLean.Continuum
