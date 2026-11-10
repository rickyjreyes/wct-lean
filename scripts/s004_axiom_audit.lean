import WCTLean.Models.S004TwoComponentVariation
import WCTLean.Models.S004FullSpatialJet
import WCTLean.Models.S004FullSpatialIntegratedVariation
import WCTLean.Models.S004IntegratedVariation
import WCTLean.Models.S004AmplitudeAnnulus
import WCTLean.Models.S004PrincipalDegeneracy

/-!
S004 corrected-action theorem-specific axiom reproducibility.
The printed statements distinguish:
- exact real two-component density derivative;
- complete finite spatial-gradient local derivative;
- genuine integrated derivatives conditional on analytic domination;
- positive annulus coefficient bounds and global degeneracy obstructions.

Run: lake env lean scripts/s004_axiom_audit.lean
Only standard Lean logical axioms may occur.
-/

#print axioms WCTLean.S004TwoComponent.localDensity_hasDerivAt
#print axioms WCTLean.S004FullSpatialJet.gradient_sum_hasDerivAt
#print axioms WCTLean.S004FullSpatialJet.fullLocalDensity_hasDerivAt
#print axioms WCTLean.S004IntegratedVariation.integratedDensity_hasDerivAt_of_dominated
#print axioms WCTLean.S004FullSpatialIntegral.action_hasDerivAt_of_dominated
#print axioms WCTLean.curvatureWeight_ge_on_amplitude_annulus
#print axioms WCTLean.complexWeight_ae_lower_bound
#print axioms WCTLean.curvatureEnergyDensity_ae_lower_bound
#print axioms WCTLean.no_uniform_positive_curvature_weight
#print axioms WCTLean.arbitrarily_small_weight_high_density
