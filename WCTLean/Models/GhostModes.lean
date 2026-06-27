import Mathlib

namespace WCTLean

noncomputable def ghostMode
    (amplitude logFrequency energy referenceEnergy phase : ℝ) : ℝ :=
  amplitude * Real.cos (logFrequency * Real.log (energy / referenceEnergy) + phase)

theorem abs_ghostMode_le
    (amplitude logFrequency energy referenceEnergy phase : ℝ) :
    |ghostMode amplitude logFrequency energy referenceEnergy phase| ≤ |amplitude| := by
  unfold ghostMode
  rw [abs_mul]
  calc
    |amplitude| * |Real.cos (logFrequency * Real.log (energy / referenceEnergy) + phase)|
        ≤ |amplitude| * 1 :=
      mul_le_mul_of_nonneg_left (abs_cos_le_one _) (abs_nonneg amplitude)
    _ = |amplitude| := by ring

noncomputable def gaussianSmearingFactor (logFrequency sigmaLog : ℝ) : ℝ :=
  Real.exp (-(1 / 2) * logFrequency ^ 2 * sigmaLog ^ 2)

noncomputable def smearedGhostAmplitude
    (amplitude logFrequency sigmaLog : ℝ) : ℝ :=
  amplitude * gaussianSmearingFactor logFrequency sigmaLog

noncomputable def junoResolution (a b energy : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 / energy + b ^ 2)

noncomputable def deltaC9
    (amplitude logQ2 center width frequency phase : ℝ) : ℝ :=
  amplitude * Real.exp (-((logQ2 - center) ^ 2) / (2 * width ^ 2)) *
    Real.cos (frequency * logQ2 + phase)

end WCTLean
