import Mathlib

namespace WCTLean

/-!
# Cross-equation derived constraints

These theorems do not promote the associated physical claims.  They record
algebraic consequences that any calibrated WCT realization of those claims must
satisfy.
-/

/-- E19: frequency-gap quantity obtained from a curvature-squared spatial gap. -/
def gapCurvatureFrequency
    (c gapCoefficient sigma : ℝ) : ℝ :=
  c ^ 2 * (gapCoefficient * sigma ^ 2)

/-- E49/E19 bridge: the effective mass squared induced by the E19 frequency gap
is the curvature-mass square multiplied by the dimensionless gap coefficient. -/
noncomputable def effectiveMassSquaredFromGap
    (hbar c deltaOmega : ℝ) : ℝ :=
  hbar ^ 2 * deltaOmega / c ^ 4

/-- E19: combining `Delta_omega = c^2 C_gap sigma^2` with E49 gives
`m_eff^2 = C_gap (hbar sigma / c)^2`. -/
theorem gapCurvature_massSquared_chain
    (hbar c gapCoefficient sigma : ℝ)
    (hc : c ≠ 0) :
    effectiveMassSquaredFromGap hbar c
        (gapCurvatureFrequency c gapCoefficient sigma) =
      gapCoefficient * (hbar / c * sigma) ^ 2 := by
  unfold effectiveMassSquaredFromGap gapCurvatureFrequency
  field_simp [hc]
  ring

/-- E19/E6 consistency: unit gap coefficient reproduces the square of the
canonical curvature-mass law exactly. -/
theorem gapCurvature_unitCoefficient_recovers_massLawSquared
    (hbar c sigma : ℝ)
    (hc : c ≠ 0) :
    effectiveMassSquaredFromGap hbar c
        (gapCurvatureFrequency c 1 sigma) =
      (hbar / c * sigma) ^ 2 := by
  simpa using gapCurvature_massSquared_chain hbar c 1 sigma hc

/-- TOP7 diagnostic: curvature-energy density for a constant-curvature planar
sector. -/
def constantCurvatureEnergyDensity (kappa : ℝ) : ℝ :=
  kappa ^ 2

/-- TOP7 diagnostic: the torsion-free constant-curvature reduction of the E6
mass law. -/
noncomputable def planarConstantCurvatureMass
    (hbar c kappa : ℝ) : ℝ :=
  hbar / c * kappa

/-- TOP7 constraint: in the constant-curvature planar sector, the canonical
mass law is square-root in curvature energy: `m^2` is linear in `epsilon_kappa`.
This is not the same as a universal `m proportional to epsilon_kappa` law. -/
theorem planarConstantCurvatureMass_squared
    (hbar c kappa : ℝ) :
    planarConstantCurvatureMass hbar c kappa ^ 2 =
      (hbar / c) ^ 2 * constantCurvatureEnergyDensity kappa := by
  unfold planarConstantCurvatureMass constantCurvatureEnergyDensity
  ring

end WCTLean
