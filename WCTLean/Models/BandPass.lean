import Mathlib

namespace WCTLean

/-!
# Finite-band spectral selector

Algebraic support for M3, M7, E12-E16, E57, E61, and E64.  Theorems here
verify the Fourier symbol and its sign; they do not establish PDE existence or
nonlinear pattern selection.
-/

/-- Negative fourth-order shell penalty. -/
def finiteBandPenalty (b k kStar : ℝ) : ℝ :=
  -b * (k ^ 2 - kStar ^ 2) ^ 2

/-- Linear Swift-Hohenberg growth symbol. -/
def swiftHohenbergLinearSymbol (mu b k kStar : ℝ) : ℝ :=
  mu + finiteBandPenalty b k kStar

/-- M3/M7: nonnegative fourth-order coefficient makes the shell penalty
nonpositive at every wavenumber. -/
theorem finiteBandPenalty_nonpositive
    (b k kStar : ℝ) (hb : 0 ≤ b) :
    finiteBandPenalty b k kStar ≤ 0 := by
  unfold finiteBandPenalty
  exact neg_nonpos.mpr (mul_nonneg hb (sq_nonneg _))

/-- The fourth-order penalty vanishes on the selected shell. -/
@[simp] theorem finiteBandPenalty_at_shell (b kStar : ℝ) :
    finiteBandPenalty b kStar kStar = 0 := by
  simp [finiteBandPenalty]

/-- Off shell, a positive fourth-order coefficient gives strict damping. -/
theorem finiteBandPenalty_strict_off_shell
    (b k kStar : ℝ) (hb : 0 < b) (hoff : k ^ 2 ≠ kStar ^ 2) :
    finiteBandPenalty b k kStar < 0 := by
  unfold finiteBandPenalty
  have hdiff : k ^ 2 - kStar ^ 2 ≠ 0 := sub_ne_zero.mpr hoff
  have hsq : 0 < (k ^ 2 - kStar ^ 2) ^ 2 := sq_pos_of_ne_zero hdiff
  exact neg_lt_zero.mpr (mul_pos hb hsq)

/-- The linear growth rate never exceeds its on-shell value `mu`. -/
theorem swiftHohenbergLinearSymbol_le_mu
    (mu b k kStar : ℝ) (hb : 0 ≤ b) :
    swiftHohenbergLinearSymbol mu b k kStar ≤ mu := by
  unfold swiftHohenbergLinearSymbol
  linarith [finiteBandPenalty_nonpositive b k kStar hb]

/-- The selected shell attains the linear growth value `mu`. -/
@[simp] theorem swiftHohenbergLinearSymbol_at_shell
    (mu b kStar : ℝ) :
    swiftHohenbergLinearSymbol mu b kStar kStar = mu := by
  simp [swiftHohenbergLinearSymbol]

/-- E61: a positive onset parameter makes the selected shell linearly
unstable in the scalar symbol. -/
theorem selectedShell_positive_at_onset
    (mu b kStar : ℝ) (hmu : 0 < mu) :
    0 < swiftHohenbergLinearSymbol mu b kStar kStar := by
  simpa using hmu

/-- E12 scalar growth polynomial `r + a k^2 - b k^4`. -/
def quarticGrowthSymbol (r a b k : ℝ) : ℝ :=
  r + a * k ^ 2 - b * k ^ 4

/-- E12/E64: exact completed-square representation of the quartic growth
symbol when `b` is nonzero. -/
theorem quarticGrowthSymbol_completedSquare
    (r a b k : ℝ) (hb : b ≠ 0) :
    quarticGrowthSymbol r a b k =
      (r + a ^ 2 / (4 * b)) - b * (k ^ 2 - a / (2 * b)) ^ 2 := by
  unfold quarticGrowthSymbol
  field_simp [hb]
  ring

/-- Preferred squared wavenumber of the quartic symbol. -/
noncomputable def selectedWavenumberSq (a b : ℝ) : ℝ :=
  a / (2 * b)

/-- Corrected selected wavelength `2 pi sqrt(2 b / a)`. -/
noncomputable def selectedWavelength (a b : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt (2 * b / a)

/-- Positive coefficients make the corrected selected wavelength positive. -/
theorem selectedWavelength_positive
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 < selectedWavelength a b := by
  unfold selectedWavelength
  have hratio : 0 < 2 * b / a := div_pos (mul_pos (by norm_num) hb) ha
  exact mul_pos (mul_pos (by positivity) Real.pi_pos) (Real.sqrt_pos.2 hratio)

end WCTLean
