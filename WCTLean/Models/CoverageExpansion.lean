import Mathlib

namespace WCTLean

/-!
# Formal coverage expansion

Small exact algebraic results for canonical equations that already pass the
symbolic audit but were previously registry-only in Lean. These declarations
are intentionally narrower than the associated PDE or physical claims.
-/

/-- E16: linearized modal power under a supplied growth rate. -/
noncomputable def linearModePower
    (initialPower growthRate time : ℝ) : ℝ :=
  initialPower * Real.exp (2 * growthRate * time)

/-- E16: nonnegative initial power stays nonnegative in the linearized model. -/
theorem linearModePower_nonnegative
    (initialPower growthRate time : ℝ)
    (hinitial : 0 ≤ initialPower) :
    0 ≤ linearModePower initialPower growthRate time := by
  unfold linearModePower
  exact mul_nonneg hinitial (le_of_lt (Real.exp_pos _))

/-- E16: for equal positive initial power and positive time, the mode with the
larger supplied growth rate has strictly larger linearized power. -/
theorem linearModePower_selects_larger_growth
    (initialPower growthRate₁ growthRate₂ time : ℝ)
    (hinitial : 0 < initialPower)
    (htime : 0 < time)
    (hgrowth : growthRate₁ < growthRate₂) :
    linearModePower initialPower growthRate₁ time <
      linearModePower initialPower growthRate₂ time := by
  unfold linearModePower
  have harg : 2 * growthRate₁ * time < 2 * growthRate₂ * time := by
    nlinarith
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr harg) hinitial

/-- E37: energy-limited wavenumber scale. -/
noncomputable def energyBandlimit
    (coefficient maxEnergy hbar c : ℝ) : ℝ :=
  coefficient * maxEnergy / (hbar * c)

/-- E37: nonnegative coefficient/energy and positive constants give a
nonnegative bandlimit. -/
theorem energyBandlimit_nonnegative
    (coefficient maxEnergy hbar c : ℝ)
    (hcoefficient : 0 ≤ coefficient)
    (henergy : 0 ≤ maxEnergy)
    (hhbar : 0 < hbar)
    (hc : 0 < c) :
    0 ≤ energyBandlimit coefficient maxEnergy hbar c := by
  unfold energyBandlimit
  exact div_nonneg
    (mul_nonneg hcoefficient henergy)
    (le_of_lt (mul_pos hhbar hc))

/-- E38: the canonical scalar upper-bound expression for spatial channel
capacity. -/
def channelCapacityUpperBound
    (coefficient volume maxWavenumber : ℝ) : ℝ :=
  coefficient * volume * maxWavenumber ^ 3

/-- E38: the encoded channel-capacity upper bound is nonnegative when its
physical factors are nonnegative. -/
theorem channelCapacityUpperBound_nonnegative
    (coefficient volume maxWavenumber : ℝ)
    (hcoefficient : 0 ≤ coefficient)
    (hvolume : 0 ≤ volume)
    (hwavenumber : 0 ≤ maxWavenumber) :
    0 ≤ channelCapacityUpperBound coefficient volume maxWavenumber := by
  unfold channelCapacityUpperBound
  exact mul_nonneg
    (mul_nonneg hcoefficient hvolume)
    (pow_nonneg hwavenumber 3)

/-- CM11: Gaussian curvature-damping envelope. -/
noncomputable def curvatureDampingEnvelope
    (k dampingWavenumber : ℝ) : ℝ :=
  Real.exp (-(k ^ 2 / dampingWavenumber ^ 2))

/-- CM11: the Gaussian damping envelope is strictly positive. -/
theorem curvatureDampingEnvelope_positive
    (k dampingWavenumber : ℝ) :
    0 < curvatureDampingEnvelope k dampingWavenumber := by
  unfold curvatureDampingEnvelope
  exact Real.exp_pos _

/-- CM11: the zero-wavenumber mode is undamped. -/
@[simp] theorem curvatureDampingEnvelope_zero
    (dampingWavenumber : ℝ) :
    curvatureDampingEnvelope 0 dampingWavenumber = 1 := by
  simp [curvatureDampingEnvelope]

/-- Shared scalar curvature quotient for CLE4/CLE10. -/
noncomputable def scalarCurvatureQuotient
    (laplacianValue fieldValue : ℝ) : ℝ :=
  -laplacianValue / fieldValue

/-- CLE4: away from a field zero, curvature locking is algebraically equivalent
to the locked eigen-equation `-Δψ = σ ψ`. -/
theorem curvatureLock_iff_lockedEigenEquation
    (laplacianValue fieldValue sigma : ℝ)
    (hfield : fieldValue ≠ 0) :
    scalarCurvatureQuotient laplacianValue fieldValue = sigma ↔
      -laplacianValue = sigma * fieldValue := by
  unfold scalarCurvatureQuotient
  exact div_eq_iff hfield

/-- CLE9: radius is the reciprocal curvature scale. -/
noncomputable def curvatureRadius (sigma : ℝ) : ℝ := 1 / sigma

/-- CLE9: nonzero curvature gives the exact reciprocal identity `R σ = 1`. -/
theorem curvatureRadius_mul_curvature
    (sigma : ℝ) (hsigma : sigma ≠ 0) :
    curvatureRadius sigma * sigma = 1 := by
  unfold curvatureRadius
  field_simp

/-- CLE10: away from a field zero, the curvature-scalar identity is equivalent
to the squared-curvature locked eigen-equation. -/
theorem curvatureScalarSq_iff_lockedEigenEquation
    (laplacianValue fieldValue sigma : ℝ)
    (hfield : fieldValue ≠ 0) :
    scalarCurvatureQuotient laplacianValue fieldValue = sigma ^ 2 ↔
      -laplacianValue = sigma ^ 2 * fieldValue := by
  unfold scalarCurvatureQuotient
  exact div_eq_iff hfield

end WCTLean
