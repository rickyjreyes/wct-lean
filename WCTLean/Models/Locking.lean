import Mathlib

namespace WCTLean

/-!
# Curvature-phase locking algebra

Finite and integrated algebraic forms supporting M1 and E3-E8.  These results
state the nonzero-weight and nonzero-denominator hypotheses explicitly; they do
not assert existence of a stationary field solution.
-/

/-- E4 integration constant from winding closure. -/
noncomputable def alphaLock
    (winding : ℤ) (integratedSigma integratedReciprocalWeight : ℝ) : ℝ :=
  (2 * Real.pi * (winding : ℝ) - integratedSigma) /
    integratedReciprocalWeight

/-- E4: the stated integration constant solves the scalar closure equation. -/
theorem alphaLock_closure
    (winding : ℤ) (integratedSigma integratedReciprocalWeight : ℝ)
    (hden : integratedReciprocalWeight ≠ 0) :
    alphaLock winding integratedSigma integratedReciprocalWeight *
        integratedReciprocalWeight + integratedSigma =
      2 * Real.pi * (winding : ℝ) := by
  unfold alphaLock
  field_simp [hden]
  ring

/-- Pointwise locking formula used in E4. -/
def PointwiseLocked
    (phaseGradient sigma weight alpha : ℝ) : Prop :=
  phaseGradient = sigma + alpha / weight

/-- Multiplying the pointwise E4 solution by a nonzero weight removes the
reciprocal and produces the corrected local E8 contribution. -/
theorem pointwiseLocked_weighted
    (phaseGradient sigma weight alpha : ℝ)
    (hweight : weight ≠ 0)
    (hlock : PointwiseLocked phaseGradient sigma weight alpha) :
    weight * phaseGradient = weight * sigma + alpha := by
  unfold PointwiseLocked at hlock
  rw [hlock]
  field_simp [hweight]

/-- Finite analogue of the corrected E8 identity:
`sum w phi' = sum w sigma + alpha L`, where the counting measure has total
length equal to the number of samples. -/
theorem correctedWeightedLockIdentity
    {ι : Type*} [Fintype ι]
    (phaseGradient sigma weight : ι → ℝ) (alpha : ℝ)
    (hweight : ∀ i, weight i ≠ 0)
    (hlock : ∀ i, PointwiseLocked (phaseGradient i) (sigma i) (weight i) alpha) :
    (∑ i, weight i * phaseGradient i) =
      (∑ i, weight i * sigma i) + alpha * Fintype.card ι := by
  calc
    (∑ i, weight i * phaseGradient i) =
        ∑ i, (weight i * sigma i + alpha) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact pointwiseLocked_weighted
        (phaseGradient i) (sigma i) (weight i) alpha (hweight i) (hlock i)
    _ = (∑ i, weight i * sigma i) + alpha * Fintype.card ι := by
      rw [Finset.sum_add_distrib]
      simp

/-- E3 finite mismatch action. -/
def finiteLockingAction
    {ι : Type*} [Fintype ι]
    (weight phaseGradient sigma : ι → ℝ) : ℝ :=
  ∑ i, weight i * (phaseGradient i - sigma i) ^ 2

/-- E3: nonnegative weights make the finite locking action nonnegative. -/
theorem finiteLockingAction_nonnegative
    {ι : Type*} [Fintype ι]
    (weight phaseGradient sigma : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    0 ≤ finiteLockingAction weight phaseGradient sigma := by
  unfold finiteLockingAction
  exact Finset.sum_nonneg fun i hi => mul_nonneg (hweight i) (sq_nonneg _)

/-- Exact pointwise lock makes the finite mismatch action vanish. -/
theorem finiteLockingAction_zero
    {ι : Type*} [Fintype ι]
    (weight phaseGradient sigma : ι → ℝ)
    (hlock : ∀ i, phaseGradient i = sigma i) :
    finiteLockingAction weight phaseGradient sigma = 0 := by
  unfold finiteLockingAction
  simp [hlock]

end WCTLean
