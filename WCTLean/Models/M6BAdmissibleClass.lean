import WCTLean.Models.M6BGlobalPhase

/-!
# Explicit admissible M6B subclass and nonuniqueness (#26)

This file defines a genuine predicate/class of corrected curvature
regularizers obeying four independently checkable constraints:
positive denominator on every nonnegative intensity for every
positive regulator, node safety, global U(1) phase invariance of the
full complex two-jet quotient, and agreement with the fixed nonnodal
epsilon-to-zero limit.

The maintained M6B family has at least two distinct members in this
class. Thus these four conditions, considered together, are
insufficient for closure selection. The independently imposed
one-intensity calibration selects lambda=0 *within this family*.

This is NOT the class of all dimensionally/covariantly admissible
operators derived from a corrected parent WCT action. Local gauge
covariance, variational integrability, PDE-solution convergence,
and model-wide physical selection remain unproved.
-/

noncomputable section

namespace WCTLean

/-- A quantified structural admissibility contract for the explicit
M6B denominator family. Importantly, lambda does not occur in the
definition only as a type marker: each property constrains the
actual source-compatible quotient formula. -/
structure M6BBasicAdmissible (alpha S lam : ℝ) : Prop where
  positive_denominator :
    ∀ epsilon s : ℝ, 0 < epsilon → 0 ≤ s →
      0 < m6bDenominator epsilon alpha lam S s
  safe_at_nodes :
    ∀ epsilon : ℝ, ∀ lapPsi : ℂ,
      m6bCurvature epsilon alpha lam S 0 lapPsi = 0
  invariant_under_global_phase :
    ∀ epsilon : ℝ, ∀ u psi lapPsi : ℂ, ‖u‖ = 1 →
      m6bCurvature epsilon alpha lam S (u * psi) (u * lapPsi) =
        m6bCurvature epsilon alpha lam S psi lapPsi
  common_nonnodal_limit :
    ∀ psi lapPsi : ℂ, psi ≠ 0 →
      Filter.Tendsto
        (fun epsilon : ℝ =>
          m6bCurvature epsilon alpha lam S psi lapPsi)
        (nhds 0) (nhds (-(lapPsi / psi)))

/-- Every nonnegative parameter is in the stated structural
admissibility class. This is an actual conjunction of proofs of the
four requirements rather than a renamed positivity hypothesis. -/
theorem m6b_nonnegative_basic_admissible
    (alpha lam S : ℝ) (hS : 0 < S) (hlam : 0 ≤ lam) :
    M6BBasicAdmissible alpha S lam := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro epsilon s hepsilon hs
    exact m6bDenominator_positive epsilon alpha lam S s
      hepsilon hlam hS hs
  · intro epsilon lapPsi
    exact m6bCurvature_at_node epsilon alpha lam S lapPsi
  · intro epsilon u psi lapPsi hu
    exact m6b_unit_phase_curvature_invariant epsilon alpha lam S
      u psi lapPsi hu
  · intro psi lapPsi hpsi
    exact m6bCurvature_common_nonnodal_limit alpha lam S
      psi lapPsi hpsi

/-- Nonuniqueness over the explicitly defined, positive, node-safe,
globally phase-invariant, common-limit class: two members disagree at a
nonzero jet for EVERY positive epsilon. -/
theorem m6b_basic_admissible_nonunique
    (alpha S : ℝ) (hS : 0 < S) :
    ∃ lam₀ lam₁ : ℝ,
      lam₀ ≠ lam₁ ∧
      M6BBasicAdmissible alpha S lam₀ ∧
      M6BBasicAdmissible alpha S lam₁ ∧
      (∀ epsilon : ℝ, 0 < epsilon →
        m6bCurvature epsilon alpha lam₀ S 1 1 ≠
          m6bCurvature epsilon alpha lam₁ S 1 1) := by
  refine ⟨0, 1, by norm_num, ?_, ?_, ?_⟩
  · exact m6b_nonnegative_basic_admissible alpha 0 S hS (by norm_num)
  · exact m6b_nonnegative_basic_admissible alpha 1 S hS (by norm_num)
  · intro epsilon hepsilon
    exact m6bCurvature_pairwise_distinct epsilon alpha S 0 1
      hepsilon hS (by norm_num)

/-- An independently imposed reference-intensity denominator
condition removes this nonuniqueness inside the explicit family.
The condition is NOT derived from a variational action. -/
theorem m6b_basic_class_reference_anchor_selects_canonical
    (epsilon alpha lam S : ℝ)
    (hepsilon : 0 < epsilon) (hS : 0 < S)
    (_hadmissible : M6BBasicAdmissible alpha S lam)
    (hanchor : m6bDenominator epsilon alpha lam S 1 =
      complexRegularizerDenominator (1 : ℂ) epsilon alpha) :
    lam = 0 :=
  m6b_reference_intensity_selects_canonical epsilon alpha lam S
    hepsilon hS hanchor

end WCTLean
