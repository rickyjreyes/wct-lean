import Mathlib

namespace WCTLean

/-!
# Substantive E79 / E82 coverage

The entropy-production formula is a *definition* with a conditional sign
theorem. The information metric is the real Gram pairing on supplied curvature
derivatives. Nothing here identifies these derivatives with an existing WCT
solution or proves physical thermodynamics.
-/

/-- E79: canonical entropy production formula with a supplied effective
temperature. Zero-temperature interpretation is not asserted. -/
noncomputable def entropyProductionRate
    (entropyRate curvatureEnergy effectiveTemperature : ℝ) : ℝ :=
  entropyRate + curvatureEnergy / effectiveTemperature

/-- E79: for a positive temperature, nonnegative entropy rate and curvature
energy suffice for nonnegative production. Without the entropy-rate sign
hypothesis no unconditional second-law statement follows. -/
theorem entropyProductionRate_nonnegative
    (entropyRate curvatureEnergy effectiveTemperature : ℝ)
    (hEntropy : 0 ≤ entropyRate) (hCurvature : 0 ≤ curvatureEnergy)
    (hTemperature : 0 < effectiveTemperature) :
    0 ≤ entropyProductionRate entropyRate curvatureEnergy effectiveTemperature := by
  unfold entropyProductionRate
  exact add_nonneg hEntropy (div_nonneg hCurvature (le_of_lt hTemperature))

/-- E82: real symmetric information-Gram entry of supplied directional
curvature derivatives; using the real part avoids a falsely real complex
metric. -/
def informationMetricEntry {ι : Type*} (dTheta : ι → ℂ) (i j : ι) : ℝ :=
  (star (dTheta i) * dTheta j).re

/-- E82: the real Gram metric is symmetric under exchange of directions. -/
theorem informationMetricEntry_symmetric
    {ι : Type*} (dTheta : ι → ℂ) (i j : ι) :
    informationMetricEntry dTheta i j = informationMetricEntry dTheta j i := by
  unfold informationMetricEntry
  calc
    (star (dTheta i) * dTheta j).re =
        (star (star (dTheta i) * dTheta j)).re := by simp
    _ = (star (dTheta j) * dTheta i).re := by simp [mul_comm]

/-- E82: each diagonal Gram entry is nonnegative. -/
theorem informationMetricEntry_diagonal_nonnegative
    {ι : Type*} (dTheta : ι → ℂ) (i : ι) :
    0 ≤ informationMetricEntry dTheta i i := by
  have h : (star (dTheta i) * dTheta i).re = Complex.normSq (dTheta i) := by
    rw [← Complex.normSq_eq_conj_mul_self]
    simp
  unfold informationMetricEntry
  rw [h]
  exact Complex.normSq_nonneg (dTheta i)

/-- E82: finite weighted directional curvature variation. The weights are
real and the result is an actual complex directional derivative combination. -/
def weightedCurvatureVariation {ι : Type*} [Fintype ι]
    (dTheta : ι → ℂ) (v : ι → ℝ) : ℂ :=
  ∑ i, (v i : ℂ) * dTheta i

/-- E82: its squared norm is a nonnegative quadratic form, including
nonsymmetric direction vectors. Identifying the resulting form with a PDE
Fisher metric remains a separate operator/regularity obligation. -/
def informationMetricQuadratic {ι : Type*} [Fintype ι]
    (dTheta : ι → ℂ) (v : ι → ℝ) : ℝ :=
  Complex.normSq (weightedCurvatureVariation dTheta v)

theorem informationMetricQuadratic_nonnegative
    {ι : Type*} [Fintype ι] (dTheta : ι → ℂ) (v : ι → ℝ) :
    0 ≤ informationMetricQuadratic dTheta v := by
  exact Complex.normSq_nonneg _

end WCTLean
