import Mathlib
import WCTLean.Models.ComplexCurvature

/-!
# M6B: local nonuniqueness of the maintained complex curvature closure (#26)

The canonical corrected WCT regularizer is the lambda=0 member of an
explicit family, varying lambda while preserving the positive nodal
regularizer and the same unregularized pointwise quotient off nodes.

This is an exact complex two-jet result, not uniqueness/nonuniqueness
of nonlinear PDE solutions. The complete C-infinity and continuum
Dirichlet-field witness proofs are also formalized independently in
ReyesMath.M6B; this module proves the source-matched bridge for the
maintained WCTLean operator without importing a second Lean project.
-/

noncomputable section

namespace WCTLean

/-- M6B one-parameter denominator family; the original quotient is
obtained at lambda = 0. -/
def m6bDenominator (epsilon alpha lam S s : ℝ) : ℝ :=
  s + epsilon ^ 2 * Real.exp (-2 * alpha * s) *
    (1 + lam * s / (S + s))

/-- A complex jet curvature corresponding to the M6B denominator family. -/
def m6bCurvature (epsilon alpha lam S : ℝ) (psi lapPsi : ℂ) : ℂ :=
  -(lapPsi * (starRingEnd ℂ) psi) /
    ((m6bDenominator epsilon alpha lam S (Complex.normSq psi) : ℝ) : ℂ)

/-- For nonnegative lambda, every denominator is strictly positive
at every nonnegative intensity, with no sign assumption on alpha. -/
theorem m6bDenominator_positive (epsilon alpha lam S s : ℝ)
    (hepsilon : 0 < epsilon) (hlam : 0 ≤ lam)
    (hS : 0 < S) (hs : 0 ≤ s) :
    0 < m6bDenominator epsilon alpha lam S s := by
  have hsum : 0 < S + s := by linarith
  have hfrac : 0 ≤ lam * s / (S + s) :=
    div_nonneg (mul_nonneg hlam hs) (le_of_lt hsum)
  have hfac : 0 < 1 + lam * s / (S + s) := by linarith
  have hbase : 0 < epsilon ^ 2 * Real.exp (-2 * alpha * s) := by positivity
  unfold m6bDenominator
  have hterm : 0 < epsilon ^ 2 * Real.exp (-2 * alpha * s) *
      (1 + lam * s / (S + s)) := mul_pos hbase hfac
  linarith

/-- Exact formula-level correspondence to the maintained canonical denominator. -/
theorem m6bDenominator_canonical
    (epsilon alpha S : ℝ) (psi : ℂ) :
    m6bDenominator epsilon alpha 0 S (Complex.normSq psi) =
      complexRegularizerDenominator psi epsilon alpha := by
  simp [m6bDenominator, complexRegularizerDenominator]

/-- The canonical WCTLean corrected operator is exactly lambda=0,
not merely a similar-looking abstract closure. -/
theorem m6bCurvature_canonical
    (epsilon alpha S : ℝ) (psi lapPsi : ℂ) :
    m6bCurvature epsilon alpha 0 S psi lapPsi =
      thetaComplex lapPsi psi epsilon alpha := by
  rw [thetaComplex_canonical_formula]
  simp [m6bCurvature, m6bDenominator, complexRegularizerDenominator] <;> ring

/-- Node safety is shared by the full family, independent of lapPsi. -/
theorem m6bCurvature_at_node (epsilon alpha lam S : ℝ) (lapPsi : ℂ) :
    m6bCurvature epsilon alpha lam S 0 lapPsi = 0 := by
  simp [m6bCurvature]

/-- The family parameter is identifiable already from the denominator
at the physical nonzero intensity s=1. -/
theorem m6bDenominator_injective_at_one (epsilon alpha S : ℝ)
    (hepsilon : 0 < epsilon) (hS : 0 < S) :
    Function.Injective (fun lam : ℝ =>
      m6bDenominator epsilon alpha lam S 1) := by
  intro lam mu heq
  have hs : S + 1 ≠ 0 := ne_of_gt (by linarith)
  have he : epsilon ^ 2 * Real.exp (-2 * alpha) ≠ 0 :=
    ne_of_gt (by positivity)
  have hh : 1 + (epsilon ^ 2 * Real.exp (-2 * alpha)) *
        (1 + lam / (S + 1)) =
      1 + (epsilon ^ 2 * Real.exp (-2 * alpha)) *
        (1 + mu / (S + 1)) := by
    simpa [m6bDenominator] using heq
  have hm : (epsilon ^ 2 * Real.exp (-2 * alpha)) *
        (1 + lam / (S + 1)) =
      (epsilon ^ 2 * Real.exp (-2 * alpha)) *
        (1 + mu / (S + 1)) := add_left_cancel hh
  have hfac : 1 + lam / (S + 1) = 1 + mu / (S + 1) :=
    mul_left_cancel₀ he hm
  have hdiv : lam / (S + 1) = mu / (S + 1) := by linarith
  have hfinal := congrArg (fun a : ℝ => a * (S + 1)) hdiv
  field_simp [hs] at hfinal
  exact hfinal

/-- No two parameter values give the same complex curvature at the
concrete nonzero jet (psi,lapPsi)=(1,1). -/
theorem m6bCurvature_pairwise_distinct
    (epsilon alpha S lam mu : ℝ)
    (hepsilon : 0 < epsilon) (hS : 0 < S) (hne : lam ≠ mu) :
    m6bCurvature epsilon alpha lam S 1 1 ≠
      m6bCurvature epsilon alpha mu S 1 1 := by
  intro heq
  have hinv :
      (((m6bDenominator epsilon alpha lam S 1 : ℝ) : ℂ)⁻¹) =
      (((m6bDenominator epsilon alpha mu S 1 : ℝ) : ℂ)⁻¹) := by
    simpa [m6bCurvature, div_eq_mul_inv] using heq
  have hdenC : ((m6bDenominator epsilon alpha lam S 1 : ℝ) : ℂ) =
      ((m6bDenominator epsilon alpha mu S 1 : ℝ) : ℂ) := by
    have h := congrArg (fun z : ℂ => z⁻¹) hinv
    simpa using h
  have hdenR : m6bDenominator epsilon alpha lam S 1 =
      m6bDenominator epsilon alpha mu S 1 := by
    exact_mod_cast hdenC
  exact hne (m6bDenominator_injective_at_one epsilon alpha S
    hepsilon hS hdenR)

/-- There are infinitely many distinct pointwise complex-curvature
regularizations with the canonical lambda=0 member. -/
theorem m6bInfinitelyManyClosures (epsilon alpha S : ℝ)
    (hepsilon : 0 < epsilon) (hS : 0 < S) :
    Set.Infinite (Set.range
      (fun k : ℕ => (fun p : ℂ × ℂ =>
        m6bCurvature epsilon alpha (k : ℝ) S p.1 p.2))) := by
  apply Set.infinite_range_of_injective
  intro k l h
  have heq : m6bCurvature epsilon alpha (k : ℝ) S 1 1 =
      m6bCurvature epsilon alpha (l : ℝ) S 1 1 := by
    exact congrArg (fun f : ℂ × ℂ → ℂ => f (1, 1)) h
  have hcast : (k : ℝ) = (l : ℝ) := by
    by_contra hne
    exact m6bCurvature_pairwise_distinct epsilon alpha S
      (k : ℝ) (l : ℝ) hepsilon hS hne heq
  exact_mod_cast hcast

end WCTLean
