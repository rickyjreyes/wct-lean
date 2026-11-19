import WCTLean.Models.CurveLocking

/-!
Axiom inspection for issue #24: curve-integral locking and winding
quantization from the logarithmic line integral `∮ dψ/ψ`.

Run with the pinned toolchain:
  lake env lean scripts/curve_locking_axiom_audit.lean
Checked fail-closed by:
  python3 scripts/check_axiom_log.py curve-locking-axioms.log 15 "curve-locking"
-/

#print axioms WCTLean.exp_logCurveIntegral
#print axioms WCTLean.winding_quantized
#print axioms WCTLean.phaseCirculation_windingQuantized
#print axioms WCTLean.amplitude_return_zero
#print axioms WCTLean.logCurveIntegral_of_global_log
#print axioms WCTLean.logCurveIntegral_exp_int
#print axioms WCTLean.exp_int_loop_closed
#print axioms WCTLean.logCurveIntegral_eq_zero_of_global_log
#print axioms WCTLean.no_global_log_of_winding_ne_zero
#print axioms WCTLean.exp_int_loop_no_global_log
#print axioms WCTLean.polar_phaseCirculation
#print axioms WCTLean.logCurveIntegral_mul
#print axioms WCTLean.product_loop_windingQuantized
#print axioms WCTLean.field_loop_winding_quantized
#print axioms WCTLean.alpha_determined_by_winding
