import Mathlib

/-!
# S004 quadratic-jet first variation: exact algebraic Taylor identity

The flat corrected higher-derivative A2/S004 action has a quadratic
acceleration/Laplacian form
  K(a,b) = kappa*(b-a)^2 + theta*b^2 + gamma*(b-a)*b
after writing Box = Delta - partial_t^2.

On one real component, with velocity v, spatial gradient g, potential
value U and curvature coefficient f, the scalar jet density is
  L = -v^2 + g^2 - U + f*K(a,b).

This module proves the EXACT cubic polynomial Taylor identity in all
independent jet variables. Its first-order coefficient is the full
real-scalar local first variation including the f*delta K and delta f*K
terms. To obtain the full field action, delta f must be supplied by the
corrected regulator chain rule, delta U by V'(rho)*delta rho, the two
components must be assembled, and the variations integrated with valid
higher-order boundary terms. None of those continuum steps is asserted.
-/

namespace WCTLean.S004JetVariation

def curvatureQuadratic (kappa theta gamma a b : ℝ) : ℝ :=
  kappa * (b - a) ^ 2 + theta * b ^ 2 + gamma * (b - a) * b

def curvatureQuadraticDirection
    (kappa theta gamma a b da db : ℝ) : ℝ :=
  2 * kappa * (b - a) * (db - da) +
    2 * theta * b * db +
    gamma * ((db - da) * b + (b - a) * db)

/-- Exact second-order expansion of the higher-derivative quadratic
form. No assumption about positivity, differentiability or boundaries. -/
theorem curvatureQuadratic_exactTaylor
    (kappa theta gamma a b da db t : ℝ) :
    curvatureQuadratic kappa theta gamma
      (a + t * da) (b + t * db) =
      curvatureQuadratic kappa theta gamma a b +
      t * curvatureQuadraticDirection kappa theta gamma a b da db +
      t ^ 2 * curvatureQuadratic kappa theta gamma da db := by
  unfold curvatureQuadratic curvatureQuadraticDirection
  ring

def jetDensity
    (v g potential f kappa theta gamma a b : ℝ) : ℝ :=
  -(v ^ 2) + g ^ 2 - potential +
    f * curvatureQuadratic kappa theta gamma a b

def jetDensityDirection
    (v g f kappa theta gamma a b dv dg dPotential df da db : ℝ) : ℝ :=
  -(2 * v * dv) + 2 * g * dg - dPotential +
    df * curvatureQuadratic kappa theta gamma a b +
    f * curvatureQuadraticDirection kappa theta gamma a b da db

/-- Exact cubic remainder. This is a fully explicit local jet variation;
it does not silently replace a variable F(rho) by a constant. -/
theorem jetDensity_exactTaylor
    (v g potential f kappa theta gamma a b
      dv dg dPotential df da db t : ℝ) :
    jetDensity (v + t * dv) (g + t * dg)
        (potential + t * dPotential) (f + t * df)
        kappa theta gamma (a + t * da) (b + t * db) =
      jetDensity v g potential f kappa theta gamma a b +
      t * jetDensityDirection v g f kappa theta gamma a b
        dv dg dPotential df da db +
      t ^ 2 *
        (-(dv ^ 2) + dg ^ 2 +
          f * curvatureQuadratic kappa theta gamma da db +
          df * curvatureQuadraticDirection kappa theta gamma a b da db) +
      t ^ 3 * df * curvatureQuadratic kappa theta gamma da db := by
  unfold jetDensity jetDensityDirection
    curvatureQuadratic curvatureQuadraticDirection
  ring

/-- Algebraic chain-rule substitution for a density dependent curvature
coefficient f=F(rho) and potential V(rho): the true slopes F'(rho)
and V'(rho) must be justified independently. -/
theorem jetDensity_direction_chain
    (v g f kappa theta gamma a b dv dg drho
      potentialSlope curvatureSlope da db : ℝ) :
    jetDensityDirection v g f kappa theta gamma a b
      dv dg (potentialSlope * drho) (curvatureSlope * drho) da db =
      -(2 * v * dv) + 2 * g * dg -
        potentialSlope * drho +
        curvatureSlope * drho * curvatureQuadratic kappa theta gamma a b +
        f * curvatureQuadraticDirection kappa theta gamma a b da db := by
  rfl

/-! ## True real derivative of the quadratic acceleration/Laplacian form -/

/-- The exact quadratic-jet coefficient above is the genuine directional
derivative, not merely the linear term of a symbolic polynomial. -/
theorem curvatureQuadratic_hasDerivAt
    (kappa theta gamma a b da db : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        curvatureQuadratic kappa theta gamma
          (a + t * da) (b + t * db))
      (curvatureQuadraticDirection kappa theta gamma a b da db) 0 := by
  have ha : HasDerivAt (fun t : ℝ => a + t * da) da 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_mul da).const_add a using 1
    · funext t
      simp only [id_eq]
      ring
    · ring
  have hb : HasDerivAt (fun t : ℝ => b + t * db) db 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_mul db).const_add b using 1
    · funext t
      simp only [id_eq]
      ring
    · ring
  have hdiff := hb.sub ha
  have h := ((hdiff.pow 2).const_mul kappa).add
    ((hb.pow 2).const_mul theta) |>.add ((hdiff.mul hb).const_mul gamma)
  convert h using 1 <;>
    (try funext t) <;>
    simp [curvatureQuadratic, curvatureQuadraticDirection,
      Pi.sub_apply, Pi.mul_apply, Pi.pow_apply] <;>
    ring

end WCTLean.S004JetVariation
