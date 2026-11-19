import WCTLean.Fourier
import WCTLean.FourierSpectral
import WCTLean.Models.FisherCurvature

/-!
Axiom inspection for issue #23: real trigonometric orthogonality on
`[0, 2π]`, the `L²(AddCircle T)` Fourier spectral projection, and the E78
curvature–Fisher results.

Run with the pinned toolchain:
  lake env lean scripts/fourier_e78_axiom_audit.lean
Checked fail-closed by:
  python3 scripts/check_axiom_log.py fourier-e78-axioms.log 44 "Fourier/E78"
-/

-- WCTLean/Fourier.lean (12)
#print axioms WCTLean.integral_cos_int_mul_period
#print axioms WCTLean.integral_sin_int_mul_period
#print axioms WCTLean.integral_cos_mul_cos_of_natAbs_ne
#print axioms WCTLean.integral_cos_mul_cos_nat_of_ne
#print axioms WCTLean.integral_sin_mul_sin_of_natAbs_ne
#print axioms WCTLean.integral_sin_mul_sin_nat_of_ne
#print axioms WCTLean.integral_sin_mul_cos_int
#print axioms WCTLean.integral_cos_mul_cos_self
#print axioms WCTLean.integral_sin_mul_sin_self
#print axioms WCTLean.integral_cos_mul_cos_int
#print axioms WCTLean.cos_orthogonality_TODO_false
#print axioms WCTLean.cos_orthogonality_corrected_holds

-- WCTLean/FourierSpectral.lean (21)
#print axioms WCTLean.spectralProjection_eq_starProjection
#print axioms WCTLean.spectralProjection_idem
#print axioms WCTLean.spectralProjection_inner_symm
#print axioms WCTLean.fourierCoeff_spectralProjection
#print axioms WCTLean.norm_sq_spectralProjection
#print axioms WCTLean.norm_sq_eq_spectralProjection_add_remainder
#print axioms WCTLean.norm_sq_sub_spectralProjection
#print axioms WCTLean.sum_norm_sq_fourierCoeff_le
#print axioms WCTLean.norm_spectralProjection_le
#print axioms WCTLean.norm_sub_spectralProjection_le
#print axioms WCTLean.tendsto_spectralProjection
#print axioms WCTLean.tendsto_symmetric_spectralProjection
#print axioms WCTLean.tendsto_norm_sub_symmetric_spectralProjection
#print axioms WCTLean.hasSum_norm_sq_fourierCoeff
#print axioms WCTLean.tsum_tail_eq_norm_sq_sub_spectralProjection
#print axioms WCTLean.bandMultiplier_fourierMode
#print axioms WCTLean.inner_bandMultiplier_self
#print axioms WCTLean.re_inner_bandMultiplier_le
#print axioms WCTLean.norm_bandMultiplier_le
#print axioms WCTLean.swiftHohenbergMultiplier_energy_le
#print axioms WCTLean.quarticGrowthMultiplier_energy_le

-- WCTLean/Models/FisherCurvature.lean (11)
#print axioms WCTLean.e78Probe_fisher
#print axioms WCTLean.e78Probe_mass
#print axioms WCTLean.e78Probe_curvatureEnergy_ge
#print axioms WCTLean.e78Probe_fisher_and_energy
#print axioms WCTLean.e78_no_universal_constant
#print axioms WCTLean.e78_universal_bound_false
#print axioms WCTLean.periodic_integral_mul_second_deriv
#print axioms WCTLean.fisher_sq_eq_four_dirichlet
#print axioms WCTLean.e78_fisher_curvature_identity
#print axioms WCTLean.interval_cauchy_schwarz
#print axioms WCTLean.e78_fisher_sq_le_curvature_energy
