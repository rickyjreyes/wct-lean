import Mathlib
import WCTLean.Models.CorrectedWeightDirection
import WCTLean.Models.S004JetVariation

/-!
# Actual two-component S004 local first variation

This is the corrected flat S004 ACTION DENSITY for two real field
components, with independent real jets for their time derivatives,
spatial-gradient components, accelerations and Laplacians.

The curvature coefficient is the original
 F(|psi|²) = |psi|² / (|psi|² + epsilon² exp(-2 alpha |psi|²))².
The potential is an arbitrary differentiable V(|psi|²).
The proof computes HasDerivAt of the COMPOSITE action density under
a simultaneous real variation of ALL jet coordinates. It uses the
actual correctedWeightRadialSlope and the non-holomorphic
2(x dx + y dy) derivative, rather than assuming F is constant.

This is pointwise in spacetime. A continuum integrated Euler-Lagrange
theorem additionally needs function-space differentiability,
dominated convergence, boundary traces and higher-order IBP.
-/

namespace WCTLean.S004TwoComponent

open WCTLean.S004JetVariation

structure Jet where
  x : ℝ
  y : ℝ
  vx : ℝ
  vy : ℝ
  gx : ℝ
  gy : ℝ
  ax : ℝ
  ay : ℝ
  bx : ℝ
  by : ℝ

/-- Simultaneous variation of both real-field components and all jets. -/
def Jet.shift (u h : Jet) (t : ℝ) : Jet where
  x := u.x + t * h.x
  y := u.y + t * h.y
  vx := u.vx + t * h.vx
  vy := u.vy + t * h.vy
  gx := u.gx + t * h.gx
  gy := u.gy + t * h.gy
  ax := u.ax + t * h.ax
  ay := u.ay + t * h.ay
  bx := u.bx + t * h.bx
  by := u.by + t * h.by

/-- S004's corrected two-component curvature quadratic form. -/
def curvatureForm (kappa theta gamma : ℝ) (u : Jet) : ℝ :=
  curvatureQuadratic kappa theta gamma u.ax u.bx +
    curvatureQuadratic kappa theta gamma u.ay u.by

/-- The genuine corrected flat higher-derivative S004 local density.
A single gx/gy entry represents the corresponding gradient quadratic
component. Additional spatial directions add another gradient sum. -/
noncomputable def localDensity
    (epsilon alpha kappa theta gamma : ℝ)
    (V : ℝ → ℝ) (u : Jet) : ℝ :=
  -(u.vx ^ 2 + u.vy ^ 2) + (u.gx ^ 2 + u.gy ^ 2) -
    V (realTwoComponentDensity u.x u.y) +
    realTwoComponentWeight epsilon alpha u.x u.y *
      curvatureForm kappa theta gamma u

/-- The full first-order coefficient in the local S004 real two-component
jet variation, with the potential slope at |psi|² explicitly supplied. -/
noncomputable def localDirection
    (epsilon alpha kappa theta gamma Vprime : ℝ)
    (u h : Jet) : ℝ :=
  -(2 * (u.vx * h.vx + u.vy * h.vy)) +
    2 * (u.gx * h.gx + u.gy * h.gy) -
    Vprime * (2 * (u.x * h.x + u.y * h.y)) +
    (correctedWeightRadialSlope epsilon alpha
      (realTwoComponentDensity u.x u.y) *
      (2 * (u.x * h.x + u.y * h.y))) *
      curvatureForm kappa theta gamma u +
    realTwoComponentWeight epsilon alpha u.x u.y *
      (curvatureQuadraticDirection kappa theta gamma
        u.ax u.bx h.ax h.bx +
       curvatureQuadraticDirection kappa theta gamma
        u.ay u.by h.ay h.by)

/-- The affine path in any one scalar jet coordinate is differentiable. -/
private theorem affine_hasDerivAt (a da : ℝ) :
    HasDerivAt (fun t : ℝ => a + t * da) da 0 := by
  convert ((hasDerivAt_id (0 : ℝ)).const_mul da).const_add a using 1
  · funext t
    ring
  · ring

/-- Pointwise first variation of the literal corrected S004 two-field
density. All nonlinear denominator derivatives are included through
the actual HasDerivAt theorem, and V is differentiated at the exact
squared field modulus. -/
theorem localDensity_hasDerivAt
    (epsilon alpha kappa theta gamma : ℝ) (V : ℝ → ℝ)
    (u h : Jet) (Vprime : ℝ)
    (hepsilon : 0 < epsilon) (halpha : 0 ≤ alpha)
    (hV : HasDerivAt V Vprime (realTwoComponentDensity u.x u.y)) :
    HasDerivAt
      (fun t : ℝ => localDensity epsilon alpha kappa theta gamma
        V (u.shift h t))
      (localDirection epsilon alpha kappa theta gamma Vprime u h) 0 := by
  have hvx := affine_hasDerivAt u.vx h.vx
  have hvy := affine_hasDerivAt u.vy h.vy
  have hgx := affine_hasDerivAt u.gx h.gx
  have hgy := affine_hasDerivAt u.gy h.gy
  have hcurvx := curvatureQuadratic_hasDerivAt
    kappa theta gamma u.ax u.bx h.ax h.bx
  have hcurvy := curvatureQuadratic_hasDerivAt
    kappa theta gamma u.ay u.by h.ay h.by
  have hcurv := hcurvx.add hcurvy
  have hw := realTwoComponentWeight_hasDerivAt
    epsilon alpha u.x u.y h.x h.y hepsilon halpha
  have hpotential := hV.comp 0
    (realTwoComponentDensity_hasDerivAt u.x u.y h.x h.y)
  have hquad := ((hvx.pow 2).add (hvy.pow 2)).neg.add
    ((hgx.pow 2).add (hgy.pow 2))
  have htotal := (hquad.sub hpotential).add (hw.mul hcurv)
  convert htotal using 1 <;>
    simp [localDensity, localDirection, curvatureForm, Jet.shift] <;>
    ring

end WCTLean.S004TwoComponent
