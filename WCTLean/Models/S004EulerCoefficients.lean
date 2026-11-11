import Mathlib
import WCTLean.Models.S004FullSpatialJet

/-!
# Exact Euler–Lagrange momenta of the corrected S004 action

This is the ORIGINAL corrected two-real-component S004 jet density,
including every Fin d spatial gradient, the actual corrected
nonpolynomial curvature regulator, the independent acceleration and
Laplacian jets, and the arbitrary differentiable potential V(|psi|²).

The density variation is decomposed into its exact ten families of
field-jet coefficients. In particular, the high-order momenta below
depend on F(|psi|²), and the zero-order force contains F'(|psi|²)
times the actual curvature quadratic form.

This is the necessary nontrivial algebraic input for integration by
parts. It is NOT yet an integrated Euler–Lagrange PDE theorem.
-/

namespace WCTLean.S004EulerCoefficients

open WCTLean
open WCTLean.S004TwoComponent
open WCTLean.S004JetVariation
open WCTLean.S004FullSpatialJet

/-- Exact coefficient of the acceleration variation `delta (partial_t² u)`
inside F(|psi|²) K(partial_t² u, Delta u). -/
def accelSlope (kappa gamma a b : ℝ) : ℝ :=
  -(2 * kappa * (b - a)) - gamma * b

/-- Exact coefficient of the spatial Laplacian variation
`delta (Delta u)` inside F(|psi|²) K(partial_t² u, Delta u). -/
def lapSlope (kappa theta gamma a b : ℝ) : ℝ :=
  2 * kappa * (b - a) + 2 * theta * b + gamma * (2 * b - a)

/-- Identifies the *actual* two high-derivative momentum coefficients of
the mixed S004 quadratic curvature form, not an assumed adjoint. -/
theorem curvature_direction_coefficients
    (kappa theta gamma a b da db : ℝ) :
    curvatureQuadraticDirection kappa theta gamma a b da db =
      accelSlope kappa gamma a b * da +
      lapSlope kappa theta gamma a b * db := by
  unfold curvatureQuadraticDirection accelSlope lapSlope
  ring

/-- Nonlinear corrected regulator and potential produce this
zero-order force coefficient after the real density chain rule.
It is shared by the two field components before multiplication by
their respective real field value. -/
noncomputable def radialForceSlope {d : ℕ}
    (epsilon alpha kappa theta gamma Vprime : ℝ) (u : Jet d) : ℝ :=
  2 * (correctedWeightRadialSlope epsilon alpha
      (realTwoComponentDensity u.x u.y) *
      curvatureForm kappa theta gamma (core u) - Vprime)

/-- Exact real-component zero-order Euler coefficient from both
the potential slope and density-dependent curvature weight. -/
noncomputable def forceX {d : ℕ}
    (epsilon alpha kappa theta gamma Vprime : ℝ) (u : Jet d) : ℝ :=
  u.x * radialForceSlope epsilon alpha kappa theta gamma Vprime u

/-- Exact imaginary-component zero-order Euler coefficient. -/
noncomputable def forceY {d : ℕ}
    (epsilon alpha kappa theta gamma Vprime : ℝ) (u : Jet d) : ℝ :=
  u.y * radialForceSlope epsilon alpha kappa theta gamma Vprime u

/-- Coefficient of variation of the second temporal derivative of Re psi. -/
noncomputable def accelX {d : ℕ}
    (epsilon alpha kappa gamma : ℝ) (u : Jet d) : ℝ :=
  realTwoComponentWeight epsilon alpha u.x u.y *
    accelSlope kappa gamma u.ax u.bx

/-- Coefficient of variation of the second temporal derivative of Im psi. -/
noncomputable def accelY {d : ℕ}
    (epsilon alpha kappa gamma : ℝ) (u : Jet d) : ℝ :=
  realTwoComponentWeight epsilon alpha u.x u.y *
    accelSlope kappa gamma u.ay u.bY

/-- Coefficient of the Laplacian variation of Re psi. -/
noncomputable def lapX {d : ℕ}
    (epsilon alpha kappa theta gamma : ℝ) (u : Jet d) : ℝ :=
  realTwoComponentWeight epsilon alpha u.x u.y *
    lapSlope kappa theta gamma u.ax u.bx

/-- Coefficient of the Laplacian variation of Im psi. -/
noncomputable def lapY {d : ℕ}
    (epsilon alpha kappa theta gamma : ℝ) (u : Jet d) : ℝ :=
  realTwoComponentWeight epsilon alpha u.x u.y *
    lapSlope kappa theta gamma u.ay u.bY

/-- **Exact S004 Euler-coefficient decomposition at every spacetime point.**
The first two terms contain the FULL nonlinear regulator derivative;
the velocities and all d spatial gradients have their correct signs;
acceleration and Laplacian terms use the exact mixed quadratic momenta.
This is a polynomial identity in the actual corrected action jet, with
the nonpolynomial regulator carried unchanged through the identity. -/
theorem fullLocalDirection_coefficients {d : ℕ}
    (epsilon alpha kappa theta gamma Vprime : ℝ)
    (u h : Jet d) :
    fullLocalDirection epsilon alpha kappa theta gamma Vprime u h =
      forceX epsilon alpha kappa theta gamma Vprime u * h.x +
      forceY epsilon alpha kappa theta gamma Vprime u * h.y -
      2 * u.vx * h.vx - 2 * u.vy * h.vy +
      (∑ i : Fin d,
        2 * (u.gx i * h.gx i + u.gy i * h.gy i)) +
      accelX epsilon alpha kappa gamma u * h.ax +
      accelY epsilon alpha kappa gamma u * h.ay +
      lapX epsilon alpha kappa theta gamma u * h.bx +
      lapY epsilon alpha kappa theta gamma u * h.bY := by
  simp only [fullLocalDirection, localDirection, core, curvatureForm,
    forceX, forceY, radialForceSlope, accelX, accelY, lapX, lapY,
    accelSlope, lapSlope, curvatureQuadraticDirection]
  ring

/-- The fully derived Euler-momentum expression is the genuine local
Gâteaux derivative of the corrected S004 density with all gradient
directions, not a postulated symbolic first-variation expression. -/
theorem fullLocalDensity_hasDerivAt_coefficients {d : ℕ}
    (epsilon alpha kappa theta gamma : ℝ)
    (V : ℝ → ℝ) (u h : Jet d) (Vprime : ℝ)
    (heps : 0 < epsilon) (ha : 0 ≤ alpha)
    (hV : HasDerivAt V Vprime
      (realTwoComponentDensity u.x u.y)) :
    HasDerivAt
      (fun t : ℝ => fullLocalDensity
        epsilon alpha kappa theta gamma V (shift u h t))
      (forceX epsilon alpha kappa theta gamma Vprime u * h.x +
       forceY epsilon alpha kappa theta gamma Vprime u * h.y -
       2 * u.vx * h.vx - 2 * u.vy * h.vy +
       (∑ i : Fin d,
         2 * (u.gx i * h.gx i + u.gy i * h.gy i)) +
       accelX epsilon alpha kappa gamma u * h.ax +
       accelY epsilon alpha kappa gamma u * h.ay +
       lapX epsilon alpha kappa theta gamma u * h.bx +
       lapY epsilon alpha kappa theta gamma u * h.bY) 0 := by
  rw [← fullLocalDirection_coefficients
    epsilon alpha kappa theta gamma Vprime u h]
  exact fullLocalDensity_hasDerivAt epsilon alpha kappa theta gamma
    V u h Vprime heps ha hV

end WCTLean.S004EulerCoefficients
