import Mathlib
import WCTLean.Models.ComplexCurvature

namespace WCTLean

/-!
# M6B: a precise non-uniqueness witness for the regularized closure

The following is operator-selection non-uniqueness, NOT non-uniqueness of PDE
solutions. Positivity, node normalization, and agreement at epsilon = 0 do not
by themselves uniquely choose the canonical denominator. Additional physics
or an independently justified selection principle is required.
-/

/-- A concrete, strictly larger family depending only on the field modulus,
with a nonnegative dimensionless coefficient `beta`. -/
noncomputable def modifiedRegularizerDenominator
    (beta : ℝ) (psi : ℂ) (epsilon alpha : ℝ) : ℝ :=
  complexRegularizerDenominator psi epsilon alpha +
    beta * epsilon ^ 2 * Complex.normSq psi

/-- All nonnegative coefficients preserve the strict node-safe positivity of
the canonical regularizer at every positive epsilon. -/
theorem modifiedRegularizerDenominator_positive
    (beta : ℝ) (psi : ℂ) (epsilon alpha : ℝ)
    (hbeta : 0 ≤ beta) (hepsilon : 0 < epsilon) :
    0 < modifiedRegularizerDenominator beta psi epsilon alpha := by
  unfold modifiedRegularizerDenominator
  have hcorrection : 0 ≤ beta * epsilon ^ 2 * Complex.normSq psi :=
    mul_nonneg (mul_nonneg hbeta (sq_nonneg _)) (Complex.normSq_nonneg psi)
  exact add_pos_of_pos_of_nonneg
    (complexRegularizerDenominator_positive psi epsilon alpha hepsilon)
    hcorrection

/-- The beta family preserves the exact original node normalization. -/
@[simp] theorem modifiedRegularizerDenominator_at_node
    (beta epsilon alpha : ℝ) :
    modifiedRegularizerDenominator beta 0 epsilon alpha = epsilon ^ 2 := by
  simp [modifiedRegularizerDenominator]

/-- The beta family has precisely the same zero-regulator denominator. -/
@[simp] theorem modifiedRegularizerDenominator_at_zero_epsilon
    (beta alpha : ℝ) (psi : ℂ) :
    modifiedRegularizerDenominator beta psi 0 alpha = Complex.normSq psi := by
  simp [modifiedRegularizerDenominator, complexRegularizerDenominator]

/-- The zero member is definitionally the original canonical choice. -/
@[simp] theorem modifiedRegularizerDenominator_beta_zero
    (psi : ℂ) (epsilon alpha : ℝ) :
    modifiedRegularizerDenominator 0 psi epsilon alpha =
      complexRegularizerDenominator psi epsilon alpha := by
  simp [modifiedRegularizerDenominator]

/-- The three weak selection requirements that are often conflated with
uniqueness. This is deliberately a mathematical predicate on operators. -/
structure BasicRegulatorConstraints
    (D : ℂ → ℝ → ℝ → ℝ) : Prop where
  positive : ∀ psi epsilon alpha, 0 < epsilon → 0 < D psi epsilon alpha
  node : ∀ epsilon alpha, D 0 epsilon alpha = epsilon ^ 2
  zeroReg : ∀ psi alpha, D psi 0 alpha = Complex.normSq psi

theorem canonical_has_basic_constraints :
    BasicRegulatorConstraints complexRegularizerDenominator := by
  refine ⟨?_, ?_, ?_⟩
  · intro psi epsilon alpha hepsilon
    exact complexRegularizerDenominator_positive psi epsilon alpha hepsilon
  · intro epsilon alpha
    exact complexRegularizerDenominator_at_zero epsilon alpha
  · intro psi alpha
    simp [complexRegularizerDenominator]

theorem modified_has_basic_constraints (beta : ℝ) (hbeta : 0 ≤ beta) :
    BasicRegulatorConstraints (modifiedRegularizerDenominator beta) := by
  refine ⟨?_, ?_, ?_⟩
  · intro psi epsilon alpha hepsilon
    exact modifiedRegularizerDenominator_positive beta psi epsilon alpha hbeta hepsilon
  · intro epsilon alpha
    exact modifiedRegularizerDenominator_at_node beta epsilon alpha
  · intro psi alpha
    exact modifiedRegularizerDenominator_at_zero_epsilon beta alpha psi

/-- Explicit separation: beta=1 gives denominator 3, while the canonical
beta=0 gives denominator 2, at psi=1, epsilon=1, alpha=0. -/
theorem modified_denominator_differs_from_canonical :
    modifiedRegularizerDenominator 1 1 1 0 ≠
      complexRegularizerDenominator 1 1 0 := by
  norm_num [modifiedRegularizerDenominator, complexRegularizerDenominator]

/-- M6B: the three basic structural constraints cannot imply uniqueness.
This result does not rule out uniqueness within a more restrictive class. -/
theorem basic_regulator_constraints_nonunique :
    ∃ D₁ D₂ : ℂ → ℝ → ℝ → ℝ,
      BasicRegulatorConstraints D₁ ∧
      BasicRegulatorConstraints D₂ ∧ D₁ ≠ D₂ := by
  refine ⟨complexRegularizerDenominator, modifiedRegularizerDenominator 1,
    canonical_has_basic_constraints, modified_has_basic_constraints 1 (by norm_num), ?_⟩
  intro heq
  have h := congrFun (congrFun (congrFun heq (1 : ℂ)) (1 : ℝ)) (0 : ℝ)
  exact modified_denominator_differs_from_canonical h.symm

end WCTLean
