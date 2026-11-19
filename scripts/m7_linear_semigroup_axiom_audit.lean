import WCTLean.Models.M7LinearSemigroup

/-!
Axiom inspection for issues #19/#21: the linear M7 evolution operator on
`L²(AddCircle T)` (well-posedness, strong continuity, Fourier-mild
uniqueness, linearized spectrum).  The nonlinear curvature term is not
covered.

Run with the pinned toolchain:
  lake env lean scripts/m7_linear_semigroup_axiom_audit.lean
Checked fail-closed by:
  python3 scripts/check_axiom_log.py m7-linear-axioms.log 18 "m7-linear-semigroup"
-/

#print axioms WCTLean.L2Circle_ext
#print axioms WCTLean.fourierCoeff_evolution
#print axioms WCTLean.evolution_zero
#print axioms WCTLean.evolution_add_time
#print axioms WCTLean.evolution_sub
#print axioms WCTLean.evolution_smul
#print axioms WCTLean.norm_evolution_le
#print axioms WCTLean.norm_evolution_sub_le
#print axioms WCTLean.tendsto_evolution_zero
#print axioms WCTLean.evolution_fourier_mild
#print axioms WCTLean.fourier_mild_unique
#print axioms WCTLean.evolution_fourierMode
#print axioms WCTLean.evolution_exponentially_stable
#print axioms WCTLean.evolution_mode_unbounded
#print axioms WCTLean.m7SymbolAtWavenumber_le
#print axioms WCTLean.m7_linear_well_posed
#print axioms WCTLean.swiftHohenberg_shell_unstable
#print axioms WCTLean.swiftHohenberg_subcritical_stable
