import WCTLean.Models.ComplexClosureNonuniqueness
import WCTLean.Models.ComplexCurvatureLimit

/-!
# M6B: a common unregularized limit does not select a closure

For every fixed nonzero complex two-jet and every family parameter `lam`,
the source-matched M6B regularizations have the same epsilon -> 0 limit,
namely `-(lapPsi / psi)`. Yet two members are distinct for positive
epsilon (already proved in `m6bCurvature_pairwise_distinct`).

Thus denominator positivity, node safety, and agreement with the
unregularized nonnodal limit do not determine the maintained closure.
This is a *pointwise two-jet* counterexample to operator selection, not
a result about convergence of PDE solutions, covariance of the full action,
or the physical uniqueness of a WCT field equation.
-/

noncomputable section

namespace WCTLean

/-- Every member of the M6B family agrees with the canonical curvature
at epsilon=0, including nodes in Lean's totalized-division convention. -/
theorem m6bCurvature_zero_regulator_agrees
    (alpha lam S : ℝ) (psi lapPsi : ℂ) :
    m6bCurvature 0 alpha lam S psi lapPsi =
      thetaComplex lapPsi psi 0 alpha := by
  calc
    m6bCurvature 0 alpha lam S psi lapPsi =
        m6bCurvature 0 alpha 0 S psi lapPsi := by
          simp [m6bCurvature, m6bDenominator]
    _ = thetaComplex lapPsi psi 0 alpha :=
      m6bCurvature_canonical 0 alpha S psi lapPsi

/-- Away from zeros of the supplied field, the common epsilon=0 value
is the ordinary complex singular quotient. No statement is made about
that classical quotient at a node. -/
theorem m6bCurvature_zero_regulator_quotient
    (alpha lam S : ℝ) (psi lapPsi : ℂ) (hpsi : psi ≠ 0) :
    m6bCurvature 0 alpha lam S psi lapPsi = -(lapPsi / psi) := by
  rw [m6bCurvature_zero_regulator_agrees]
  exact thetaComplex_zero_epsilon lapPsi psi alpha hpsi

/-- For every real lambda and S, the *full* M6B complex curvature has
the same nonnodal epsilon -> 0 limit. Neither positivity away from
epsilon=0 nor any PDE-level convergence is inferred. -/
theorem m6bCurvature_common_nonnodal_limit
    (alpha lam S : ℝ) (psi lapPsi : ℂ) (hpsi : psi ≠ 0) :
    Filter.Tendsto (fun epsilon : ℝ =>
      m6bCurvature epsilon alpha lam S psi lapPsi)
      (nhds 0) (nhds (-(lapPsi / psi))) := by
  have hnorm : Complex.normSq psi ≠ 0 :=
    (Complex.normSq_pos.mpr hpsi).ne'
  have hden : m6bDenominator 0 alpha lam S (Complex.normSq psi) ≠ 0 := by
    simpa [m6bDenominator] using hnorm
  have hdenC :
      ((m6bDenominator 0 alpha lam S (Complex.normSq psi) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hden
  have hdenCont : ContinuousAt
      (fun epsilon : ℝ =>
        ((m6bDenominator epsilon alpha lam S (Complex.normSq psi) : ℝ) : ℂ)) 0 := by
    unfold m6bDenominator
    fun_prop
  have hcont : ContinuousAt
      (fun epsilon : ℝ =>
        m6bCurvature epsilon alpha lam S psi lapPsi) 0 := by
    unfold m6bCurvature
    exact continuousAt_const.div hdenCont hdenC
  convert hcont.tendsto using 1
  exact congrArg nhds
    ((m6bCurvature_zero_regulator_quotient alpha lam S psi lapPsi hpsi).symm)

/-- The identical limit holds for the physically relevant positive
regulator values approaching zero. -/
theorem m6bCurvature_common_positive_limit
    (alpha lam S : ℝ) (psi lapPsi : ℂ) (hpsi : psi ≠ 0) :
    Filter.Tendsto (fun epsilon : ℝ =>
      m6bCurvature epsilon alpha lam S psi lapPsi)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-(lapPsi / psi))) :=
  (m6bCurvature_common_nonnodal_limit alpha lam S psi lapPsi hpsi).mono_left
    nhdsWithin_le_nhds

/-- Distinct node-safe positive-regulator M6B operators remain
indistinguishable by their fixed nonnodal zero-regulator limit.
An additional selection principle is therefore necessary *within this
family*; the theorem does not classify all covariant operators. -/
theorem m6b_distinct_closures_same_nonnodal_limit
    (epsilon alpha S : ℝ) (hepsilon : 0 < epsilon) (hS : 0 < S) :
    m6bCurvature epsilon alpha 0 S 1 1 ≠
        m6bCurvature epsilon alpha 1 S 1 1 ∧
      (∀ psi lapPsi : ℂ, psi ≠ 0 →
        Filter.Tendsto (fun eta : ℝ =>
          m6bCurvature eta alpha 0 S psi lapPsi)
          (nhds 0) (nhds (-(lapPsi / psi))) ∧
        Filter.Tendsto (fun eta : ℝ =>
          m6bCurvature eta alpha 1 S psi lapPsi)
          (nhds 0) (nhds (-(lapPsi / psi)))) := by
  constructor
  · exact m6bCurvature_pairwise_distinct epsilon alpha S 0 1
      hepsilon hS (by norm_num)
  · intro psi lapPsi hpsi
    exact ⟨m6bCurvature_common_nonnodal_limit alpha 0 S psi lapPsi hpsi,
      m6bCurvature_common_nonnodal_limit alpha 1 S psi lapPsi hpsi⟩

end WCTLean
