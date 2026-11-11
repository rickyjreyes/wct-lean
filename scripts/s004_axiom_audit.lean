import WCTLean.Models.S004EulerSeparation
import WCTLean.Models.S004ContinuousEuler
import WCTLean.Models.S004BoundaryWeightedEuler
import WCTLean.Models.S004FirstSpatialTraceEuler
import WCTLean.Models.S004SpacetimeFubini
import WCTLean.Models.S004SpacetimeGreen
import WCTLean.Models.S004SpacetimeEuler
import WCTLean.Models.S004SpacetimeActionBridge
import WCTLean.Models.S004EulerCoefficients
import WCTLean.Models.S004IntervalGreen
import WCTLean.Models.S004CompatibleFields
import WCTLean.Models.S004TemporalEuler
import WCTLean.Models.S004SpatialEuler
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

-- Exact corrected S004 high-derivative momenta and all-gradient variation.
#print axioms WCTLean.S004EulerCoefficients.curvature_direction_coefficients
#print axioms WCTLean.S004EulerCoefficients.fullLocalDirection_coefficients
#print axioms WCTLean.S004EulerCoefficients.fullLocalDensity_hasDerivAt_coefficients

-- REAL interval/Fundamental-Theorem-of-Calculus integration by parts:
-- zero-boundary temporal and matched-trace periodic spatial.
#print axioms WCTLean.S004IntervalGreen.integral_mul_first_deriv_eq_neg
#print axioms WCTLean.S004IntervalGreen.integral_mul_first_deriv_periodic
#print axioms WCTLean.S004IntervalGreen.integral_mul_second_deriv_eq
#print axioms WCTLean.S004IntervalGreen.integral_mul_second_deriv_periodic

-- Genuine single-field variation; time² and spatial Laplacian forced by
-- iterations of first-order linear differential operators.
#print axioms WCTLean.S004CompatibleFields.time2_shift
#print axioms WCTLean.S004CompatibleFields.laplacian_shift
#print axioms WCTLean.S004CompatibleFields.jetOf_fieldShift
#print axioms WCTLean.S004CompatibleFields.fieldAction_eq_jetAction
#print axioms WCTLean.S004CompatibleFields.fieldAction_hasDerivAt_of_dominated

-- Corrected coefficient temporal second-order Euler contributions.
#print axioms WCTLean.S004TemporalEuler.x_component_temporal_euler
#print axioms WCTLean.S004TemporalEuler.y_component_temporal_euler

-- Corrected coefficient periodic spatial gradient/Laplacian Euler terms.
#print axioms WCTLean.S004SpatialEuler.x_component_periodic_euler
#print axioms WCTLean.S004SpatialEuler.y_component_periodic_euler

-- Phase XIX: genuine continuum spacetime Fubini, Green and reassembly.
#print axioms WCTLean.S004SpacetimeFubini.rectangle_integral_swap
#print axioms WCTLean.S004SpacetimeFubini.corrected_density_direction_swap
#print axioms WCTLean.S004SpacetimeFubini.continuous_rectangle_integrable
#print axioms WCTLean.S004SpacetimeFubini.continuous_rectangle_integral_swap
#print axioms WCTLean.S004SpacetimeGreen.temporal_first_spacetime
#print axioms WCTLean.S004SpacetimeGreen.temporal_second_spacetime
#print axioms WCTLean.S004SpacetimeGreen.spatial_first_spacetime
#print axioms WCTLean.S004SpacetimeGreen.spatial_second_spacetime
#print axioms WCTLean.S004SpacetimeEuler.weakComponent_eq_strongComponent
#print axioms WCTLean.S004SpacetimeEuler.fullLocalDirection_eq_component_sum
#print axioms WCTLean.S004SpacetimeEuler.integrated_fullLocalDirection_component_split

#print axioms WCTLean.S004SpacetimeEuler.originalAction_hasDerivAt_two_weak_components

-- Phase XX: genuine L2 and boundary-weighted Euler separation.
#print axioms WCTLean.S004EulerSeparation.all_integrable_probes_zero_iff_ae_zero
#print axioms WCTLean.S004EulerSeparation.two_component_integrable_probes_iff_ae_zero
#print axioms WCTLean.S004EulerSeparation.corrected_euler_all_probes_iff_ae_equations
#print axioms WCTLean.S004ContinuousEuler.continuous_square_integrable
#print axioms WCTLean.S004ContinuousEuler.continuous_two_component_probes_iff_ae_zero
#print axioms WCTLean.S004ContinuousEuler.corrected_euler_continuous_probes_iff_ae_equations
#print axioms WCTLean.S004BoundaryWeightedEuler.timeWeight_nonneg
#print axioms WCTLean.S004BoundaryWeightedEuler.timeWeight_pos_of_mem
#print axioms WCTLean.S004BoundaryWeightedEuler.weighted_zero_integral_iff_ae_zero
#print axioms WCTLean.S004BoundaryWeightedEuler.zero_variation_on_boundary_test_forces_ae_euler
#print axioms WCTLean.S004BoundaryWeightedEuler.timeWeight_hasDerivAt
#print axioms WCTLean.S004BoundaryWeightedEuler.timeWeight_zero_endpoints
#print axioms WCTLean.S004BoundaryWeightedEuler.weighted_test_zero_temporal_traces
#print axioms WCTLean.S004BoundaryWeightedEuler.weighted_test_periodic_values
#print axioms WCTLean.S004BoundaryWeightedEuler.weighted_residual_is_boundary_periodic_test
#print axioms WCTLean.S004BoundaryWeightedEuler.boundary_periodic_test_critical_forces_ae_euler

-- First-spatial-derivative periodic traces, actual corrected S004 Euler residual.
#print axioms WCTLean.S004FirstSpatialTraceEuler.weighted_residual_has_spatial_deriv
#print axioms WCTLean.S004FirstSpatialTraceEuler.weighted_residual_is_first_spatial_trace_test
#print axioms WCTLean.S004FirstSpatialTraceEuler.first_spatial_trace_critical_forces_ae_euler
#print axioms WCTLean.S004FirstSpatialTraceEuler.corrected_euler_first_spatial_trace_critical_forces_ae

-- Actual product-volume to five-term time-major original-action variation.
#print axioms WCTLean.S004SpacetimeActionBridge.rectangleVolume_integral_eq_iterated
#print axioms WCTLean.S004SpacetimeActionBridge.five_terms_integrable
#print axioms WCTLean.S004SpacetimeActionBridge.weakPointwise_integral_eq_weakComponent
#print axioms WCTLean.S004SpacetimeActionBridge.originalAction_hasDerivAt_iterated_weak
