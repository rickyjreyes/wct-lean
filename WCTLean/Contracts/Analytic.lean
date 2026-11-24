import Mathlib
import WCTLean.Models.ComplexCurvature

open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform

namespace WCTLean

/-- Arithmetic form of the H^2 subcritical dimensional threshold. -/
def h2SubcriticalDimension (n : ℕ) : Prop := n < 4

@[simp] theorem h2Subcritical_iff_le_three (n : ℕ) :
    h2SubcriticalDimension n ↔ n ≤ 3 := by
  unfold h2SubcriticalDimension
  omega

/-- Whole-space Sobolev graph, using the same Schwartz approximation model
as ReyesMath.Sobolev.H2 in the math repository. All derivatives are tied
to one approximating sequence in actual L2 spaces. -/
abbrev SobolevDomain (n : ℕ) := EuclideanSpace ℝ (Fin n)
noncomputable abbrev SobolevL2 (n : ℕ) :=
  Lp ℂ 2 (volume : Measure (SobolevDomain n))

noncomputable def sobolevToL2 {n : ℕ} :
    SchwartzMap (SobolevDomain n) ℂ →L[ℂ] SobolevL2 n :=
  SchwartzMap.toLpCLM ℂ ℂ 2 volume

noncomputable def sobolevPartial {n : ℕ} (i : Fin n) :
    SchwartzMap (SobolevDomain n) ℂ →L[ℂ] SchwartzMap (SobolevDomain n) ℂ :=
  SchwartzMap.pderivCLM ℂ (EuclideanSpace.single i (1 : ℝ))

noncomputable def sobolevLap {n : ℕ} :
    SchwartzMap (SobolevDomain n) ℂ →L[ℂ] SchwartzMap (SobolevDomain n) ℂ :=
  ∑ i : Fin n, (sobolevPartial i).comp (sobolevPartial i)

structure SobolevH2 (n : ℕ) where
  val : SobolevL2 n
  grad : Fin n → SobolevL2 n
  lap : SobolevL2 n
  approx : ∃ φ : ℕ → SchwartzMap (SobolevDomain n) ℂ,
    Tendsto (fun j => sobolevToL2 (φ j)) atTop (𝓝 val) ∧
    (∀ i, Tendsto (fun j => sobolevToL2 (sobolevPartial i (φ j))) atTop (𝓝 (grad i))) ∧
    Tendsto (fun j => sobolevToL2 (sobolevLap (φ j))) atTop (𝓝 lap)

noncomputable def sobolevH2Norm {n : ℕ} (u : SobolevH2 n) : ℝ :=
  ‖u.val‖ + (∑ i, ‖u.grad i‖) + ‖u.lap‖

/-- E24/E67: actual L2 graph to essential-supremum embedding statement
on whole space. The threshold theorem remains open in this library. -/
def SobolevEmbeddingStatement (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevH2 n,
    ∀ᵐ x ∂(volume : Measure (SobolevDomain n)), ‖u.val x‖ ≤ C * sobolevH2Norm u

/-- Squared weighted Fourier distance of two Schwartz functions.
The real order s occurs in the Bessel-potential weight. -/
noncomputable def sobolevFourierDistanceSq {n : ℕ} (s : ℝ)
    (φ χ : SchwartzMap (SobolevDomain n) ℂ) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal
    (Real.rpow (1 + (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) s *
      ‖(𝓕 (⇑φ : SobolevDomain n → ℂ)) ξ - (𝓕 (⇑χ : SobolevDomain n → ℂ)) ξ‖ ^ 2)

/-- Higher-order whole-space Sobolev completion data: the same sequence
approximates the function, gradient and Laplacian in L2 and is Cauchy for
the weighted Fourier norm. Identification with a particular external
Sobolev library and proof of its embedding theorem remain separate. -/
def SobolevHigherRegularity {n : ℕ} (s : ℝ) (u : SobolevH2 n) : Prop :=
  ∃ φ : ℕ → SchwartzMap (SobolevDomain n) ℂ,
    Tendsto (fun j => sobolevToL2 (φ j)) atTop (𝓝 u.val) ∧
    (∀ i, Tendsto (fun j => sobolevToL2 (sobolevPartial i (φ j))) atTop (𝓝 (u.grad i))) ∧
    Tendsto (fun j => sobolevToL2 (sobolevLap (φ j))) atTop (𝓝 u.lap) ∧
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ j k : ℕ, N ≤ j → N ≤ k →
      sobolevFourierDistanceSq s (φ j) (φ k) < ENNReal.ofReal δ

/-- E69: the actual higher-regularity Laplacian embedding obligation.
It is not replaced by a dimension biconditional or an assumed field. -/
def E69LaplacianEmbeddingObligation (n : ℕ) : Prop :=
  ∀ (s : ℝ) (u : SobolevH2 n), (n : ℝ) / 2 + 2 < s →
    SobolevHigherRegularity s u →
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ᵐ x ∂(volume : Measure (SobolevDomain n)), ‖u.lap x‖ ≤ L

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

/-- E70: analytical hypotheses only. The dimension bound is deliberately
not part of the definition. For n > 2 use the published finite critical
exponent; lower dimensions require a separately justified regime.
This is not a predicate of dynamical stability. -/
def DimensionalStabilityCriterion (n : ℕ) (p : ℝ) : Prop :=
  SobolevEmbeddingStatement n ∧ 1 < p ∧
    (2 < n → p < criticalSobolevExponent (n : ℝ))

/-- The proposed dimension implication is retained as an open obligation,
not as a theorem. Its relation to actual stable PDE solutions is open. -/
def E70DimensionObligation : Prop :=
  ∀ n : ℕ, ∀ p : ℝ, DimensionalStabilityCriterion n p → n ≤ 3

/-- The scaling factor in the biharmonic norm is lambda^(4-n). -/
noncomputable def biharmonicScalingFactor (lambda : ℝ) (n : ℕ) : ℝ :=
  Real.rpow lambda (4 - (n : ℝ))

/-- At n = 4 the printed scaling factor is exactly scale-invariant, not divergent. -/
@[simp] theorem biharmonic_scaling_dimension_four (lambda : ℝ) :
    biharmonicScalingFactor lambda 4 = 1 := by
  simp [biharmonicScalingFactor]

end WCTLean
