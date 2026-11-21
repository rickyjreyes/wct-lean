import WCTLean.Models.ContinuumObligations

/-!
Axiom inspection for issue #28: continuum obligations closed with Mathlib
(core improper-integral threshold, E50 integration step, function-level
Cole–Hopf chain rule) and the typed inventory of the remaining ones.

Run with the pinned toolchain:
  lake env lean scripts/continuum_obligations_axiom_audit.lean
Checked fail-closed by:
  python3 scripts/check_axiom_log.py continuum-obligations-axioms.log 9 "continuum-obligations"
-/

#print axioms WCTLean.coreIntegrability_improper_iff
#print axioms WCTLean.coreIntegrability_integral
#print axioms WCTLean.coreIntegrability_not_integrable
#print axioms WCTLean.phaseCoherence_integral_bound
#print axioms WCTLean.phaseCoherence_finite_of_memLp
#print axioms WCTLean.coleHopf_log_derivatives
#print axioms WCTLean.coleHopf_function_bridge
#print axioms WCTLean.coleHopf_heat_iff_log_flow
#print axioms WCTLean.continuumObligations_closed_count
