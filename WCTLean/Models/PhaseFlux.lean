import Mathlib

namespace WCTLean

def phaseFluxComponent (energyDensity phaseGradientComponent : ℝ) : ℝ :=
  energyDensity * phaseGradientComponent

def conservationResidual (duDt divFlux : ℝ) : ℝ := duDt + divFlux

def CausalFluxBound (fluxNorm c energyDensity : ℝ) : Prop :=
  fluxNorm ≤ c * energyDensity

def RadialShellQuantized (radialPhaseIntegral : ℝ) (n : ℤ) : Prop :=
  radialPhaseIntegral = 2 * Real.pi * (n : ℝ)

def WindingQuantized (circulation : ℝ) (m : ℤ) : Prop :=
  circulation = 2 * Real.pi * (m : ℝ)

/-- E10: radial shell quantization is closed under composition of phase
integrals and addition of integer shell indices. -/
theorem radialShellQuantized_add
    (x y : ℝ) (n m : ℤ)
    (hx : RadialShellQuantized x n)
    (hy : RadialShellQuantized y m) :
    RadialShellQuantized (x + y) (n + m) := by
  unfold RadialShellQuantized at hx hy ⊢
  rw [hx, hy]
  push_cast
  ring

/-- E11: winding quantization is closed under concatenation of circulations. -/
theorem windingQuantized_add
    (x y : ℝ) (n m : ℤ)
    (hx : WindingQuantized x n)
    (hy : WindingQuantized y m) :
    WindingQuantized (x + y) (n + m) := by
  unfold WindingQuantized at hx hy ⊢
  rw [hx, hy]
  push_cast
  ring

/-- E10 and E11 use the same integer quantization law after the geometric
observable has been chosen. -/
theorem radialShellQuantized_iff_windingQuantized
    (value : ℝ) (n : ℤ) :
    RadialShellQuantized value n ↔ WindingQuantized value n := by
  rfl

def plaquetteWindingNumerator (d12 d23 d34 d41 : ℝ) : ℝ :=
  d12 + d23 + d34 + d41

end WCTLean
