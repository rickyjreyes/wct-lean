import WCTLean.Models.CurvatureNodalWeakLimit

/-!
Axiom inspection for issue #22: L¹ divergence and weak (distributional)
convergence of the maintained regularized curvature at simple nodes.

Run with the pinned toolchain:
  lake env lean scripts/curvature_nodal_weak_limit_axiom_audit.lean
Checked fail-closed by:
  python3 scripts/check_axiom_log.py nodal-weak-limit-axioms.log 10 "nodal-weak-limit"
-/

#print axioms WCTLean.nodal_curvature_L1_lower_bound
#print axioms WCTLean.nodal_curvature_L1_tendsto_atTop
#print axioms WCTLean.nodalWeight_hasDerivAt
#print axioms WCTLean.abs_ge_of_slope_floor
#print axioms WCTLean.log_sq_add_sq_bound
#print axioms WCTLean.tendsto_log_sq_add_sq
#print axioms WCTLean.nodal_ibp_identity
#print axioms WCTLean.nodal_log_integral_tendsto
#print axioms WCTLean.nodal_curvature_weak_limit
#print axioms WCTLean.cos_sub_half_nodal_trichotomy
