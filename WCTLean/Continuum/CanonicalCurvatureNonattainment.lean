import MathProofs.CurvatureNonattainment

/-!
# Whole-space obstruction for the positive corrected curvature energy

This module uses the actual H²(ℝ²; ℂ) weak-Sobolev state space imported
from the pinned ReyesMath package. For ε > 0 and α ≥ 0 the energy

    E(u) = ∫ |∇u|² + ∫ F(ε, α, |u|²) |Δu|²

has F(ε,α,s) = s/(s + ε² exp(-2αs))². This is the positive M2
curvature-energy candidate, not the independent CQ Hamiltonian.
It cannot have a nonzero fixed-mass whole-space minimizer. No claim about
local well-posedness of the full M7 evolution follows from this obstruction.
-/

namespace WCTLean.Continuum

abbrev CanonicalPlaneState := ReyesMath.Sobolev.H2 2

/-- The exact positive curvature-energy candidate on the genuine weak H²
space, with gradient and corrected squared-curvature integrals. -/
noncomputable abbrev canonicalPositiveEnergy
    (epsilon alpha : ℝ) (u : CanonicalPlaneState) : ℝ :=
  ReyesMath.Curvature.Ec 1 1 epsilon alpha u

/-- The constrained positive curvature-energy infimum on the whole plane. -/
noncomputable abbrev canonicalPositiveInfimum
    (epsilon alpha m : ℝ) : ℝ :=
  ReyesMath.Curvature.Id 1 1 epsilon alpha 2 m

/-- On the whole plane, positive fixed mass and the corrected positive
curvature-energy integrand imply constrained infimum zero. This is a proved
nonattainment mechanism, not a numerical zero or box effect. -/
theorem canonical_positive_energy_infimum_zero
    (epsilon alpha m : ℝ) (he : 0 < epsilon) (ha : 0 ≤ alpha)
    (hm : 0 < m) :
    canonicalPositiveInfimum epsilon alpha m = 0 := by
  exact (ReyesMath.Curvature.global_nonattainment
    (d := 2) (c₁ := (1 : ℝ)) (c₂ := (1 : ℝ))
    (ε := epsilon) (α := alpha) (m := m)
    (by omega) (by norm_num) (by norm_num) he ha hm).2.2.1

/-- No constrained minimum is attained by any fixed nonzero-mass field:
a direct theorem on H²(ℝ²; ℂ), not an added assumption. -/
theorem canonical_positive_energy_nonattainment
    (epsilon alpha m : ℝ) (he : 0 < epsilon) (ha : 0 ≤ alpha)
    (hm : 0 < m) :
    {u : CanonicalPlaneState |
      ReyesMath.Sobolev.H2.M u = m ∧
      ∀ v : CanonicalPlaneState, ReyesMath.Sobolev.H2.M v = m →
        canonicalPositiveEnergy epsilon alpha u ≤
          canonicalPositiveEnergy epsilon alpha v} = ∅ := by
  exact (ReyesMath.Curvature.global_nonattainment
    (d := 2) (c₁ := (1 : ℝ)) (c₂ := (1 : ℝ))
    (ε := epsilon) (α := alpha) (m := m)
    (by omega) (by norm_num) (by norm_num) he ha hm).2.2.2

/-- No positive-mass H² field is a local constrained minimizer of the
positive curvature energy: nearby mass-preserving dilations reduce it. -/
theorem canonical_positive_energy_no_local_minimizer
    (epsilon alpha m : ℝ) (he : 0 < epsilon) (ha : 0 ≤ alpha)
    (hm : 0 < m) (u : CanonicalPlaneState)
    (hu : ReyesMath.Sobolev.H2.M u = m)
    (radius : ℝ) (hr : 0 < radius) :
    ∃ v : CanonicalPlaneState,
      ReyesMath.Sobolev.H2.M v = m ∧
      ReyesMath.Sobolev.H2.distH2 v u < radius ∧
      canonicalPositiveEnergy epsilon alpha v <
        canonicalPositiveEnergy epsilon alpha u := by
  exact ReyesMath.Curvature.no_local_minimizer
    (d := 2) (c₁ := (1 : ℝ)) (c₂ := (1 : ℝ))
    (ε := epsilon) (α := alpha) (m := m) (U := u) (δ := radius)
    (by omega) (by omega) (by norm_num) (by norm_num)
    he ha hm hu hr

#print axioms WCTLean.Continuum.canonical_positive_energy_infimum_zero
#print axioms WCTLean.Continuum.canonical_positive_energy_nonattainment
#print axioms WCTLean.Continuum.canonical_positive_energy_no_local_minimizer

end WCTLean.Continuum
