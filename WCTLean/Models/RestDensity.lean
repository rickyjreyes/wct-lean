import Mathlib

namespace WCTLean

def densityWeightedAverage {ι : Type*} [Fintype ι]
    (density observable : ι → ℝ) : ℝ :=
  (∑ i, density i * observable i) / (∑ i, density i)

def lockingMismatch {ι : Type*} [Fintype ι]
    (density phaseGradient sigma : ι → ℝ) : ℝ :=
  ∑ i, density i * (phaseGradient i - sigma i) ^ 2

theorem lockingMismatch_zero
    {ι : Type*} [Fintype ι]
    (density phaseGradient sigma : ι → ℝ)
    (h : ∀ i, phaseGradient i = sigma i) :
    lockingMismatch density phaseGradient sigma = 0 := by
  unfold lockingMismatch
  simp [h]

end WCTLean
