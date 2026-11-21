import WCTLean.Models.M7Smoothing

/-!
Axiom inspection for issue #19: parabolic `L² → Ḣ²` smoothing of the linear
M7 evolution on `L²(AddCircle T)` (spectral Laplacian).

Run with the pinned toolchain:
  lake env lean scripts/m7_smoothing_axiom_audit.lean
Checked fail-closed by:
  python3 scripts/check_axiom_log.py m7-smoothing-axioms.log 6 "m7-smoothing"
-/

#print axioms WCTLean.sq_mul_exp_neg_le
#print axioms WCTLean.m7Symbol_coercive
#print axioms WCTLean.evolution_H2_smoothing
#print axioms WCTLean.m7Symbol_coercive_circle
#print axioms WCTLean.m7_H2_smoothing
#print axioms WCTLean.smoothing_rate_integrable
