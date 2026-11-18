import WCTLean.Models.ComplexCurvatureLimit

/-!
Axiom inspection for the corrected complex curvature vanishing-regulator
theorems (wct-lean issue #22).

Run with the pinned toolchain:
  lake env lean scripts/complex_curvature_limit_axiom_audit.lean
-/

#print axioms WCTLean.complexRegularizerDenominator_zero_epsilon
#print axioms WCTLean.thetaComplex_zero_epsilon
#print axioms WCTLean.thetaComplex_field_node
#print axioms WCTLean.thetaComplex_nonzero_limit
#print axioms WCTLean.thetaComplex_downarrow_zero
