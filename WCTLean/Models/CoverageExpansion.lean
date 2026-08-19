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

/-- CLE5/CLE8: flat-product torus eigenvalue for integer Fourier labels.
Writing each term as a squared ratio makes the nonnegativity structure explicit. -/
noncomputable def flatProductTorusEigenvalue
    (m n : ℤ) (majorRadius minorRadius : ℝ) : ℝ :=
  ((m : ℝ) / majorRadius) ^ 2 + ((n : ℝ) / minorRadius) ^ 2

/-- CLE5: the flat-product torus Fourier eigenvalue is nonnegative. -/
theorem flatProductTorusEigenvalue_nonnegative
    (m n : ℤ) (majorRadius minorRadius : ℝ) :
    0 ≤ flatProductTorusEigenvalue m n majorRadius minorRadius := by
  unfold flatProductTorusEigenvalue
  positivity

/-- CLE8: after fixing winding/chirality to `n = +1`, the `m = 0` mode has no
larger flat-product eigenvalue than any other integer `m`. -/
theorem flatProductTorus_fixedWinding_one_minimal
    (m : ℤ) (majorRadius minorRadius : ℝ) :
    flatProductTorusEigenvalue 0 1 majorRadius minorRadius ≤
      flatProductTorusEigenvalue m 1 majorRadius minorRadius := by
  unfold flatProductTorusEigenvalue
  norm_num
  exact le_add_of_nonneg_left (sq_nonneg ((m : ℝ) / majorRadius))

/-- CLE8: for nonzero major radius, equality with the selected `m = 0, n = 1`
eigenvalue occurs only for integer `m = 0`. -/
theorem flatProductTorus_fixedWinding_one_eq_iff
    (m : ℤ) (majorRadius minorRadius : ℝ)
    (hmajor : majorRadius ≠ 0) :
    flatProductTorusEigenvalue m 1 majorRadius minorRadius =
        flatProductTorusEigenvalue 0 1 majorRadius minorRadius ↔
      m = 0 := by
  unfold flatProductTorusEigenvalue
  constructor
  · intro h
    norm_num at h
    have hsquare : ((m : ℝ) / majorRadius) ^ 2 = 0 := by
      linarith
    have hq : ((m : ℝ) / majorRadius) = 0 := by
      nlinarith [sq_nonneg ((m : ℝ) / majorRadius)]
    have hmreal : (m : ℝ) = 0 := by
      exact (div_eq_zero_iff).mp hq |>.resolve_right hmajor
    exact_mod_cast hmreal
  · intro hm
    subst m
    norm_num

/-- TOP3: finite-dimensional exact negative-gradient flow has nonpositive
instantaneous energy rate `-Σᵢ gᵢ²`. This is the algebraic core of the Hilbert
space descent identity under the differentiability hypotheses. -/
noncomputable def finiteGradientFlowEnergyRate
    {n : ℕ} (gradient : Fin n → ℝ) : ℝ :=
  -∑ i, (gradient i) ^ 2

/-- TOP3: the exact negative-gradient-flow rate is never positive. -/
theorem finiteGradientFlowEnergyRate_nonpositive
    {n : ℕ} (gradient : Fin n → ℝ) :
    finiteGradientFlowEnergyRate gradient ≤ 0 := by
  unfold finiteGradientFlowEnergyRate
  have hsum : 0 ≤ ∑ i, (gradient i) ^ 2 := by
    exact Finset.sum_nonneg (fun i _ => sq_nonneg (gradient i))
  linarith

end WCTLean
