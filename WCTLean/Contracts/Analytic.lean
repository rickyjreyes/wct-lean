import Mathlib

namespace WCTLean

/-- Arithmetic form of the H^2 subcritical dimensional threshold. -/
def h2SubcriticalDimension (n : ℕ) : Prop := n < 4

@[simp] theorem h2Subcritical_iff_le_three (n : ℕ) :
    h2SubcriticalDimension n ↔ n ≤ 3 := by
  unfold h2SubcriticalDimension
  omega

/-- E24/E26/E67/E69: analytic facts are packaged as a contract so downstream
proofs expose exactly which theorem is still required from Sobolev analysis. -/
structure SobolevCurvatureContract where
  H2 : Type
  Linfty : Type
  embeds : ℕ → Prop
  curvatureBounded : ℕ → Prop
  embedding_iff : ∀ n, embeds n ↔ h2SubcriticalDimension n
  curvature_iff : ∀ n, curvatureBounded n ↔ h2SubcriticalDimension n

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
  localGradientEnergy ≤ constant * radius ^ (n - 2) * h1NormSq

/-- E70: precise separation of arithmetic dimension and analytic hypotheses. -/
def DimensionalStabilityCriterion
    (n : ℕ) (embedding subcriticalNonlinearity : Prop) : Prop :=
  n ≤ 3 ∧ embedding ∧ subcriticalNonlinearity

/-- A downstream n ≤ 3 result follows immediately once the criterion is established. -/
theorem dimensional_stability_implies_le_three
    (n : ℕ) (embedding subcriticalNonlinearity : Prop)
    (h : DimensionalStabilityCriterion n embedding subcriticalNonlinearity) :
    n ≤ 3 := h.1

/-- The scaling factor in the biharmonic norm is lambda^(4-n). -/
noncomputable def biharmonicScalingFactor (lambda : ℝ) (n : ℕ) : ℝ :=
  Real.rpow lambda (4 - (n : ℝ))

/-- At n = 4 the printed scaling factor is exactly scale-invariant, not divergent. -/
@[simp] theorem biharmonic_scaling_dimension_four (lambda : ℝ) :
    biharmonicScalingFactor lambda 4 = 1 := by
  simp [biharmonicScalingFactor]

end WCTLean
