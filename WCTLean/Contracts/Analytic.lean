import Mathlib
import WCTLean.Models.ComplexCurvature

open MeasureTheory
open scoped ENNReal

namespace WCTLean

/-- Arithmetic form of the H^2 subcritical dimensional threshold. -/
def h2SubcriticalDimension (n : ℕ) : Prop := n < 4

@[simp] theorem h2Subcritical_iff_le_three (n : ℕ) :
    h2SubcriticalDimension n ↔ n ≤ 3 := by
  unfold h2SubcriticalDimension
  omega

/-- E24/E67: the continuous embedding obligation for a supplied class of
fields and its supplied Sobolev norm. A concrete instantiation must identify
the class and norm with the actual Sobolev space on the stated domain.
No dimension biconditional is built into this definition. -/
def SobolevEmbeddingStatement {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (H2 : Set (X → ℂ)) (H2norm : (X → ℂ) → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ H2, ∀ᵐ x ∂μ, ‖ψ x‖ ≤ C * H2norm ψ

/-- E69: the missing high-regularity embedding step, expressed on a supplied
scale of field classes and supplied Laplacian. Its interpretation as a
Sobolev theorem requires an independent identification of these data.
In particular H^2 alone does not give the required Laplacian sup bound. -/
def E69LaplacianEmbeddingObligation {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (n : ℕ) (Hs : ℝ → Set (X → ℂ))
    (laplacian : (X → ℂ) → X → ℂ) : Prop :=
  ∀ (s : ℝ) (ψ : X → ℂ), (n : ℝ) / 2 + 2 < s → ψ ∈ Hs s →
    ∃ L : ℝ, 0 ≤ L ∧ ∀ᵐ x ∂μ, ‖laplacian ψ x‖ ≤ L

/-- The exact corrected curvature quotient inherits an a.e. bound from
a Laplacian bound and a bound on the regularized reciprocal. This is the
product estimate, not a proof of the preceding Sobolev obligation. -/
theorem thetaComplex_ae_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ψ lapPsi : X → ℂ) (epsilon alpha L B : ℝ)
    (hL : 0 ≤ L)
    (hLap : ∀ᵐ x ∂μ, ‖lapPsi x‖ ≤ L)
    (hRec : ∀ᵐ x ∂μ, ‖complexRegularizedReciprocal (ψ x) epsilon alpha‖ ≤ B) :
    ∀ᵐ x ∂μ, ‖thetaComplex (lapPsi x) (ψ x) epsilon alpha‖ ≤ L * B := by
  filter_upwards [hLap, hRec] with x hx hy
  rw [thetaComplex, norm_mul, norm_neg]
  exact mul_le_mul hx hy (norm_nonneg _) hL

/-- E25/E65: critical Sobolev exponent formula, physically used for n > 2. -/
noncomputable def criticalSobolevExponent (n : ℝ) : ℝ := (n + 2) / (n - 2)

/-- E27: finiteness of the sum of two nonnegative extended-real integral
contributions. Unlike real-valued nonnegativity this excludes infinite energy. -/
def FiniteConfinementEnergy (gradientEnergy curvatureEnergy : ℝ≥0∞) : Prop :=
  gradientEnergy + curvatureEnergy < ⊤

/-- E27 at field level, with the integration measure, gradient and exact
curvature operator supplied. Identifying the gradient and Laplacian with
weak derivatives of a field remains a separate analytical obligation. -/
def FiniteFieldConfinementEnergy {X G : Type*} [MeasurableSpace X]
    [Norm G] (μ : Measure X) (ψ lapPsi : X → ℂ) (gradPsi : X → G)
    (epsilon alpha : ℝ) : Prop :=
  (∫⁻ x, ENNReal.ofReal
    (‖gradPsi x‖ ^ 2 + ‖thetaComplex (lapPsi x) (ψ x) epsilon alpha‖ ^ 2) ∂μ) < ⊤

theorem infinite_gradient_energy_not_finite :
    ¬ FiniteConfinementEnergy ⊤ 0 := by
  simp [FiniteConfinementEnergy]

/-- E66: Gagliardo-Nirenberg is an analytic hypothesis in this package. -/
def GagliardoNirenbergBound
    (lp gradL2 l2 constant theta : ℝ) : Prop :=
  lp ≤ constant * Real.rpow gradL2 theta * Real.rpow l2 (1 - theta)

/-- E68: use a signed exponent; natural subtraction would truncate n - 2. -/
noncomputable def localEnergyScale (radius : ℝ) (n : ℕ) : ℝ :=
  radius ^ ((n : ℤ) - 2)

/-- E68: localized energy estimate on a positive-radius domain, as an open
proposition. No universal constant or analytical inequality is asserted. -/
def LocalEnergyBound
    (localGradientEnergy constant radius h1NormSq : ℝ) (n : ℕ) : Prop :=
  0 < radius ∧
    localGradientEnergy ≤ constant * localEnergyScale radius n * h1NormSq

/-- Regression: dimension one must give inverse radius, not radius^0. -/
theorem localEnergyScale_one (radius : ℝ) :
    localEnergyScale radius 1 = radius⁻¹ := by
  norm_num [localEnergyScale]

/-- Regression: dimension two is scale invariant in this formula. -/
theorem localEnergyScale_two (radius : ℝ) :
    localEnergyScale radius 2 = 1 := by
  norm_num [localEnergyScale]

/-- E70: the three proposed hypotheses, not a definition of dynamical
stability. The former projection of the dimension assumption is not
retained as a stability theorem. -/
def DimensionalStabilityHypotheses
    (n : ℕ) (embedding subcriticalNonlinearity : Prop) : Prop :=
  n ≤ 3 ∧ embedding ∧ subcriticalNonlinearity

/-- The scaling factor in the biharmonic norm is lambda^(4-n). -/
noncomputable def biharmonicScalingFactor (lambda : ℝ) (n : ℕ) : ℝ :=
  Real.rpow lambda (4 - (n : ℝ))

/-- At n = 4 the printed scaling factor is exactly scale-invariant, not divergent. -/
@[simp] theorem biharmonic_scaling_dimension_four (lambda : ℝ) :
    biharmonicScalingFactor lambda 4 = 1 := by
  simp [biharmonicScalingFactor]

end WCTLean
