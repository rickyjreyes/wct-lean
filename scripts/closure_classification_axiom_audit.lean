import WCTLean.Models.ClosureClassification

/-!
Axiom inspection for issue #26: classification of admissible pointwise
curvature closures, non-uniqueness, and uniqueness under explicit extra
principles (operator selection only; not PDE solution uniqueness).

Run with the pinned toolchain:
  lake env lean scripts/closure_classification_axiom_audit.lean
Checked fail-closed by:
  python3 scripts/check_axiom_log.py closure-classification-axioms.log 17 "closure-classification"
-/

#print axioms WCTLean.radialClosure_homogeneous
#print axioms WCTLean.radialClosure_phaseInvariant
#print axioms WCTLean.closure_classification
#print axioms WCTLean.denominatorClosure_structural
#print axioms WCTLean.denominatorClosure_maintained
#print axioms WCTLean.denominatorClosure_unit_invariant
#print axioms WCTLean.admissible_profile
#print axioms WCTLean.admissible_profile_asymptotic
#print axioms WCTLean.profileRegularizer_admissible
#print axioms WCTLean.shift_profile_admissible
#print axioms WCTLean.admissible_closures_infinite
#print axioms WCTLean.maintainedDenominator_not_unitCovariant
#print axioms WCTLean.maintained_scaled_eq_profile
#print axioms WCTLean.maintained_scaled_profile_admissible
#print axioms WCTLean.closure_unique_affine_normalized
#print axioms WCTLean.selected_regularizer_satisfies_principles
#print axioms WCTLean.extra_principles_independent
