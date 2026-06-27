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

def plaquetteWindingNumerator (d12 d23 d34 d41 : ℝ) : ℝ :=
  d12 + d23 + d34 + d41

end WCTLean
