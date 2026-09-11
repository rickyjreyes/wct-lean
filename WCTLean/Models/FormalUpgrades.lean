import Mathlib

namespace WCTLean

/-!
# September 2026 formal upgrades

Narrow kernel-checkable certificates for several high-value WCT derivations.
The theorems below establish exact algebraic implications only. They do not
assert PDE existence, nonlinear stability, particle-spectrum completeness, or
physical validity beyond the displayed hypotheses.
-/

/-- Squared denominator factor entering the toroidal Willmore expression
`pi^2 / (eta * sqrt (1-eta^2))`. -/
def torusShapeSq (eta : ℝ) : ℝ :=
  eta ^ 2 * (1 - eta ^ 2)

/-- The toroidal shape factor is globally bounded above by `1/4`.
This is the algebraic certificate behind the `eta^2 = 1/2` selector. -/
theorem torusShapeSq_le_quarter (eta : ℝ) :
    torusShapeSq eta ≤ (1 / 4 : ℝ) := by
  unfold torusShapeSq
  nlinarith [sq_nonneg (eta ^ 2 - (1 / 2 : ℝ))]

/-- Equality in the toroidal shape-factor bound occurs exactly at
`eta^2 = 1/2`. On the physical branch `0 < eta < 1`, this selects
`eta = 1/sqrt 2`. -/
theorem torusShapeSq_eq_quarter_iff (eta : ℝ) :
    torusShapeSq eta = (1 / 4 : ℝ) ↔ eta ^ 2 = (1 / 2 : ℝ) := by
  unfold torusShapeSq
  constructor
  · intro h
    nlinarith [sq_nonneg (eta ^ 2 - (1 / 2 : ℝ))]
  · intro h
    nlinarith

/-- Generic finite-band growth law. `R` is the destabilizing quadratic
coefficient and `q>0` is the stabilizing quartic coefficient. -/
def finiteBandGrowth (R q k : ℝ) : ℝ :=
  R * k ^ 2 - q * k ^ 4

/-- Exact completed-square form of the finite-band growth law. -/
theorem finiteBandGrowth_completedSquare
    (R q k : ℝ) (hq : q ≠ 0) :
    finiteBandGrowth R q k =
      R ^ 2 / (4 * q) - q * (k ^ 2 - R / (2 * q)) ^ 2 := by
  unfold finiteBandGrowth
  field_simp [hq]
  ring

/-- For positive quartic stiffness, the finite-band growth law has the global
upper bound `R^2/(4q)`. -/
theorem finiteBandGrowth_le_max
    (R q k : ℝ) (hq : 0 < q) :
    finiteBandGrowth R q k ≤ R ^ 2 / (4 * q) := by
  rw [finiteBandGrowth_completedSquare R q k (ne_of_gt hq)]
  have hnonneg :
      0 ≤ q * (k ^ 2 - R / (2 * q)) ^ 2 :=
    mul_nonneg (le_of_lt hq) (sq_nonneg _)
  linarith

/-- Equality in the finite-band upper bound occurs exactly on the selected
shell `k^2 = R/(2q)`. With `q=d^-2`, this is
`k_star^2 = R d^2 / 2`. -/
theorem finiteBandGrowth_eq_max_iff
    (R q k : ℝ) (hq : 0 < q) :
    finiteBandGrowth R q k = R ^ 2 / (4 * q) ↔
      k ^ 2 = R / (2 * q) := by
  rw [finiteBandGrowth_completedSquare R q k (ne_of_gt hq)]
  constructor
  · intro h
    have hzero : q * (k ^ 2 - R / (2 * q)) ^ 2 = 0 := by
      linarith
    have hsquare : (k ^ 2 - R / (2 * q)) ^ 2 = 0 :=
      (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hq)
    nlinarith
  · intro hk
    rw [hk]
    ring

/-- Curvature of a circular helix with radius `R` and pitch parameter `p`. -/
noncomputable def helixCurvature (R p : ℝ) : ℝ :=
  R / (R ^ 2 + p ^ 2)

/-- Torsion of the same circular helix. -/
noncomputable def helixTorsion (R p : ℝ) : ℝ :=
  p / (R ^ 2 + p ^ 2)

/-- Exact squared curvature-torsion scale of a helix. This avoids taking a
square root and therefore isolates the algebraic content cleanly. -/
theorem helixCurvatureSq_add_torsionSq
    (R p : ℝ) (hden : R ^ 2 + p ^ 2 ≠ 0) :
    helixCurvature R p ^ 2 + helixTorsion R p ^ 2 =
      1 / (R ^ 2 + p ^ 2) := by
  unfold helixCurvature helixTorsion
  field_simp [hden]

/-- Substituting `p = n eta R` gives the aspect-ratio form of the inverse
squared curvature scale. -/
theorem helixAspectScaleSq_identity (R eta n : ℝ) :
    1 / (R ^ 2 + (n * eta * R) ^ 2) =
      1 / (R ^ 2 * (1 + n ^ 2 * eta ^ 2)) := by
  have hden :
      R ^ 2 + (n * eta * R) ^ 2 =
        R ^ 2 * (1 + n ^ 2 * eta ^ 2) := by
    ring
  rw [hden]

/-- The radial-core power law `r^(2p-2)` is locally integrable at zero exactly
when its exponent is greater than `-1`, equivalently `p>1/2`. This theorem
formalizes the threshold reduction; the analytic improper-integral theorem is
kept as a separate continuum obligation. -/
theorem coreIntegrabilityExponent_iff (p : ℝ) :
    2 * p - 2 > -1 ↔ p > (1 / 2 : ℝ) := by
  constructor <;> intro h <;> linarith

/-- Pointwise stationarity residual for the constrained locking density
`w (phi'-sigma)^2 + lambda phi'`. -/
def curvatureLockStationarity
    (w phasePrime sigma multiplier : ℝ) : ℝ :=
  2 * w * (phasePrime - sigma) + multiplier

/-- A constrained locking stationary point obeys the exact relation
`phi' = sigma - lambda/(2w)` whenever the weight is nonzero. Thus the winding
constraint generally introduces a multiplier correction rather than exact
pointwise locking. -/
theorem curvatureLockStationarity_iff
    (w phasePrime sigma multiplier : ℝ) (hw : w ≠ 0) :
    curvatureLockStationarity w phasePrime sigma multiplier = 0 ↔
      phasePrime = sigma - multiplier / (2 * w) := by
  unfold curvatureLockStationarity
  constructor
  · intro h
    field_simp [hw]
    nlinarith
  · intro h
    rw [h]
    field_simp [hw]
    ring

/-- Exact pointwise locking is stationary precisely when the local multiplier
vanishes. Global compatibility is what can force this multiplier to zero. -/
theorem curvatureLock_exact_stationary_iff
    (w sigma multiplier : ℝ) :
    curvatureLockStationarity w sigma sigma multiplier = 0 ↔ multiplier = 0 := by
  simp [curvatureLockStationarity]

/-- Scalar contraction-margin theorem used by the perturbed containment bound.
If `epsilon < L*delta`, then the factor `1-L*delta+epsilon` is strictly below
one. -/
theorem perturbedContractionFactor_lt_one
    (mix delta epsilon : ℝ)
    (hmargin : epsilon < mix * delta) :
    1 - mix * delta + epsilon < 1 := by
  linarith

end WCTLean
