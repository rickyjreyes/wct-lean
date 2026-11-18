import WCTLean.Models.M6BFamilyLimit

/-!
# Global U(1)-phase invariance does not select the corrected M6B closure

For any complex phase factor u with norm one, and for every real
regularizer-family parameter lambda, the full complex M6B curvature
scalar is invariant under simultaneous rotation of the supplied field
and Laplacian jets. This is the physical global U(1) transformation,
not local gauge covariance.

Combined with the previously verified distinct-positive-closure
and common-zero-regulator-limit results, even global phase invariance,
positive denominators, node safety and the common pointwise
unregularized limit fail to select a unique M6B regularizer.

Not proved: uniqueness among all covariant closure operators, local
gauge invariance, variational origin, or source-PDE convergence.
-/

noncomputable section

namespace WCTLean

/-- Simultaneous unit-phase rotation preserves the intensity entering
every member of the M6B regularizer family. -/
theorem m6b_unit_phase_intensity_invariant
    (u psi : ℂ) (hu : ‖u‖ = 1) :
    Complex.normSq (u * psi) = Complex.normSq psi := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  rw [norm_mul, hu, one_mul]

/-- For unit phase, the complex jet numerator Laplacian * conjugate
field is invariant under a common phase rotation. -/
theorem m6b_unit_phase_numerator_invariant
    (u psi lapPsi : ℂ) (hu : ‖u‖ = 1) :
    (u * lapPsi) * star (u * psi) = lapPsi * star psi := by
  have hnormSq : Complex.normSq u = 1 := by
    rw [Complex.normSq_eq_norm_sq, hu]
    norm_num
  have hconj : u * star u = (1 : ℂ) := by
    have h : ((Complex.normSq u : ℝ) : ℂ) = u * star u := by
      rw [Complex.normSq_eq_conj_mul_self]
      ring
    calc
      u * star u = ((Complex.normSq u : ℝ) : ℂ) := h.symm
      _ = 1 := by rw [hnormSq]; norm_num
  rw [star_mul]
  calc
    (u * lapPsi) * (star psi * star u) =
        (u * star u) * (lapPsi * star psi) := by ring
    _ = lapPsi * star psi := by rw [hconj, one_mul]

/-- Full M6B pointwise curvature scalar is invariant under a global
U(1) rotation of both inputs, for arbitrary real family parameter. -/
theorem m6b_unit_phase_curvature_invariant
    (epsilon alpha lam S : ℝ) (u psi lapPsi : ℂ)
    (hu : ‖u‖ = 1) :
    m6bCurvature epsilon alpha lam S (u * psi) (u * lapPsi) =
      m6bCurvature epsilon alpha lam S psi lapPsi := by
  have hnorm := m6b_unit_phase_intensity_invariant u psi hu
  have hnum := m6b_unit_phase_numerator_invariant u psi lapPsi hu
  unfold m6bCurvature
  rw [hnorm, hnum]

/-- The canonical maintained curvature operator shares the U(1)
invariance of all the explicitly parameterized M6B alternatives. -/
theorem thetaComplex_unit_phase_invariant
    (epsilon alpha : ℝ) (u psi lapPsi : ℂ)
    (hu : ‖u‖ = 1) :
    thetaComplex (u * lapPsi) (u * psi) epsilon alpha =
      thetaComplex lapPsi psi epsilon alpha := by
  calc
    thetaComplex (u * lapPsi) (u * psi) epsilon alpha =
        m6bCurvature epsilon alpha 0 1 (u * psi) (u * lapPsi) := by
          rw [m6bCurvature_canonical]
    _ = m6bCurvature epsilon alpha 0 1 psi lapPsi :=
      m6b_unit_phase_curvature_invariant epsilon alpha 0 1 u psi lapPsi hu
    _ = thetaComplex lapPsi psi epsilon alpha :=
      m6bCurvature_canonical epsilon alpha 1 psi lapPsi

/-- Two different positive-denominator closures are both global
U(1)-invariant and remain different at a nonzero complex jet. This
exhibits a source-faithful nonuniqueness even after imposing global
phase symmetry; it does not address local gauge transformations. -/
theorem m6b_global_phase_invariant_nonuniqueness
    (epsilon alpha S : ℝ)
    (hepsilon : 0 < epsilon) (hS : 0 < S) :
    (∀ u psi lapPsi : ℂ, ‖u‖ = 1 →
      m6bCurvature epsilon alpha 0 S (u * psi) (u * lapPsi) =
        m6bCurvature epsilon alpha 0 S psi lapPsi) ∧
    (∀ u psi lapPsi : ℂ, ‖u‖ = 1 →
      m6bCurvature epsilon alpha 1 S (u * psi) (u * lapPsi) =
        m6bCurvature epsilon alpha 1 S psi lapPsi) ∧
    m6bCurvature epsilon alpha 0 S 1 1 ≠
      m6bCurvature epsilon alpha 1 S 1 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro u psi lapPsi hu
    exact m6b_unit_phase_curvature_invariant epsilon alpha 0 S u psi lapPsi hu
  · intro u psi lapPsi hu
    exact m6b_unit_phase_curvature_invariant epsilon alpha 1 S u psi lapPsi hu
  · exact m6bCurvature_pairwise_distinct epsilon alpha S 0 1
      hepsilon hS (by norm_num)

end WCTLean
