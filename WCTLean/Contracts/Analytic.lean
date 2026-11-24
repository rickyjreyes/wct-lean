import Mathlib

open MeasureTheory
open scoped BigOperators

namespace WCTLean

/-- Arithmetic form of the H^2 subcritical dimensional threshold. -/
def h2SubcriticalDimension (n : ℕ) : Prop := n < 4

@[simp] theorem h2Subcritical_iff_le_three (n : ℕ) :
    h2SubcriticalDimension n ↔ n ≤ 3 := by
  unfold h2SubcriticalDimension
  omega

/-- Concrete real-valued test fields on finite-dimensional Euclidean space,
using its standard coordinates and product Lebesgue measure. -/
abbrev CoordinateSpace (n : ℕ) := Fin n → ℝ

/-- Squared H²-type norm on smooth compactly supported test functions.
The derivative norms are those induced by the finite-dimensional normed
space; this is an equivalent test norm, not a construction of the completed
Sobolev space. -/
noncomputable def h2TestNormSq {n : ℕ} (f : CoordinateSpace n → ℝ) : ℝ :=
  ∫ x : CoordinateSpace n,
    ‖f x‖ ^ 2 + ‖fderiv ℝ f x‖ ^ 2 +
      ‖fderiv ℝ (fderiv ℝ f) x‖ ^ 2

/-- Open Sobolev embedding estimate on test functions. Extending it to the
completed Sobolev space and identifying representatives is a separate task. -/
def H2EmbeddingEstimate (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ f : CoordinateSpace n → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
      ∀ x : CoordinateSpace n, ‖f x‖ ^ 2 ≤ C * h2TestNormSq f

def coordinateVector {n : ℕ} (i : Fin n) : CoordinateSpace n :=
  fun j => if j = i then 1 else 0

/-- Coordinate Laplacian of a twice differentiable real field. -/
noncomputable def testLaplacian {n : ℕ}
    (f : CoordinateSpace n → ℝ) (x : CoordinateSpace n) : ℝ :=
  ∑ i : Fin n, fderiv ℝ
    (fun y : CoordinateSpace n => fderiv ℝ f y (coordinateVector i))
    x (coordinateVector i)

/-- Open pointwise curvature bound for a specified real field and parameters.
The denominator must be nonzero; H² embedding alone does not imply this
bound or control the pointwise Laplacian. -/
def RegularizedCurvatureBound {n : ℕ}
    (f : CoordinateSpace n → ℝ) (eps alpha C : ℝ) : Prop :=
  0 ≤ C ∧ 0 < eps ∧ 0 < alpha ∧ ContDiff ℝ 2 f ∧
    ∀ x : CoordinateSpace n,
      (f x + eps * Real.exp (-alpha * (f x)^2) ≠ 0) ∧
      |-(testLaplacian f x) / (f x + eps * Real.exp (-alpha * (f x)^2))| ≤ C

/-- Two independent open analytic obligations; no dimension biconditional
or proof of either property is supplied. -/
def SobolevCurvatureContract (n : ℕ)
    (f : CoordinateSpace n → ℝ) (eps alpha C : ℝ) : Prop :=
  H2EmbeddingEstimate n ∧ RegularizedCurvatureBound f eps alpha C

/-- E25/E65: critical Sobolev exponent, defined for real-valued n. -/
noncomputable def criticalSobolevExponent (n : ℝ) : ℝ := (n + 2) / (n - 2)

/-- E27: finite-energy confinement is represented as a predicate on the two
nonnegative integral contributions. -/
def FiniteConfinementEnergy (gradientEnergy curvatureEnergy : ℝ) : Prop :=
  0 ≤ gradientEnergy ∧ 0 ≤ curvatureEnergy

/-- E66: Gagliardo-Nirenberg is an analytic hypothesis in this package. -/
def GagliardoNirenbergBound
    (lp gradL2 l2 constant theta : ℝ) : Prop :=
  lp ≤ constant * Real.rpow gradL2 theta * Real.rpow l2 (1 - theta)

/-- E68: localized energy estimate as an explicit proposition. -/
def LocalEnergyBound
    (localGradientEnergy constant radius h1NormSq : ℝ) (n : ℕ) : Prop :=
  localGradientEnergy ≤ constant * Real.rpow radius ((n : ℝ) - 2) * h1NormSq

/-- E70: proposed analytic prerequisites, not a stability theorem.
A proof that these hypotheses imply any dynamical stability result (or
restrict the dimension) remains open. -/
def DimensionalStabilityCriterion
    (n : ℕ) (subcriticalNonlinearity : Prop) : Prop :=
  H2EmbeddingEstimate n ∧ subcriticalNonlinearity

/-- The scaling factor in the biharmonic norm is lambda^(4-n). -/
noncomputable def biharmonicScalingFactor (lambda : ℝ) (n : ℕ) : ℝ :=
  Real.rpow lambda (4 - (n : ℝ))

/-- At n = 4 the printed scaling factor is exactly scale-invariant, not divergent. -/
@[simp] theorem biharmonic_scaling_dimension_four (lambda : ℝ) :
    biharmonicScalingFactor lambda 4 = 1 := by
  simp [biharmonicScalingFactor]

end WCTLean
