import WCTLean.Models.CurvatureNodalEnergy

/-!
Axiom inspection for issue #22: ε → 0 behaviour of the maintained curvature
energy at nodes of genuine one-dimensional `C²` fields.

Run with the pinned toolchain:
  lake env lean scripts/curvature_nodal_energy_axiom_audit.lean
Checked fail-closed by:
  python3 scripts/check_axiom_log.py curvature-nodal-energy-axioms.log 12 "nodal-energy"
-/

#print axioms WCTLean.norm_thetaComplex
#print axioms WCTLean.complexRegularizerDenominator_le
#print axioms WCTLean.continuous_thetaComplex_comp
#print axioms WCTLean.curvature_energy_node_lower_bound
#print axioms WCTLean.simple_zero_local_bounds
#print axioms WCTLean.nodal_curvature_energy_lower_bound
#print axioms WCTLean.nodal_curvature_energy_tendsto_atTop
#print axioms WCTLean.cos_sub_half_curvature_energy_tendsto_atTop
#print axioms WCTLean.curvature_energy_tendsto_of_multiplicative
#print axioms WCTLean.sin_mul_zero_set_null
#print axioms WCTLean.sin_curvature_energy_tendsto
#print axioms WCTLean.integral_sq_sub_center
