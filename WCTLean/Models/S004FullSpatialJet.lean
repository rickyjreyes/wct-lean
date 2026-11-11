import Mathlib
import WCTLean.Models.S004TwoComponentVariation

/-!
# Corrected S004 action density with ALL finite spatial-gradient directions

The existing verified two-real-component local density records one
spatial gradient per component. The action for spatial dimension d
contains the true gradient term
  sum_i ((partial_i Re psi)^2 + (partial_i Im psi)^2).

This module generalizes that EXACT local action density and its
directional derivative to every spatial direction i : Fin d. The
acceleration, Laplacian, potential, and true corrected S004 curvature
quotient are unchanged. The theorem derives the complete pointwise
first variation by calculus and FINITE summation, rather than claiming
a scalar 1D gradient covers a multidimensional spatial domain.

This is a pointwise finite-jet theorem. Higher-order integration by
parts and the nonlinear Euler–Lagrange PDE remain separate obligations.
-/

namespace WCTLean.S004FullSpatialJet

open WCTLean.S004TwoComponent

structure Jet (d : ℕ) where
  x : ℝ
  y : ℝ
  vx : ℝ
  vy : ℝ
  ax : ℝ
  ay : ℝ
  bx : ℝ
  bY : ℝ
  gx : Fin d → ℝ
  gy : Fin d → ℝ

def shift {d : ℕ} (u h : Jet d) (t : ℝ) : Jet d where
  x := u.x + t * h.x
  y := u.y + t * h.y
  vx := u.vx + t * h.vx
  vy := u.vy + t * h.vy
  ax := u.ax + t * h.ax
  ay := u.ay + t * h.ay
  bx := u.bx + t * h.bx
  bY := u.bY + t * h.bY
  gx := fun i => u.gx i + t * h.gx i
  gy := fun i => u.gy i + t * h.gy i

/-- Strip the gradient coordinates when invoking the already verified
non-gradient part of the corrected complex local action density. -/
def core {d : ℕ} (u : Jet d) : WCTLean.S004TwoComponent.Jet where
  x := u.x
  y := u.y
  vx := u.vx
  vy := u.vy
  gx := 0
  gy := 0
  ax := u.ax
  ay := u.ay
  bx := u.bx
  bY := u.bY

theorem core_shift {d : ℕ} (u h : Jet d) (t : ℝ) :
    core (shift u h t) =
      WCTLean.S004TwoComponent.Jet.shift (core u) (core h) t := by
  cases u
  cases h
  simp [core, shift, WCTLean.S004TwoComponent.Jet.shift]

noncomputable def fullLocalDensity {d : ℕ}
    (epsilon alpha kappa theta gamma : ℝ)
    (V : ℝ → ℝ) (u : Jet d) : ℝ :=
  localDensity epsilon alpha kappa theta gamma V (core u) +
    ∑ i : Fin d, ((u.gx i)^2 + (u.gy i)^2)

noncomputable def fullLocalDirection {d : ℕ}
    (epsilon alpha kappa theta gamma Vprime : ℝ)
    (u h : Jet d) : ℝ :=
  localDirection epsilon alpha kappa theta gamma Vprime
      (core u) (core h) +
    ∑ i : Fin d, 2 * (u.gx i * h.gx i + u.gy i * h.gy i)

private theorem affine_deriv (a b : ℝ) :
    HasDerivAt (fun t : ℝ => a + t * b) b 0 := by
  convert ((hasDerivAt_id (0 : ℝ)).const_mul b).const_add a using 1
  · funext t
    simp only [id_eq]
    ring
  · ring

/-- The full gradient energy in arbitrary finite spatial dimension
has the exact claimed real-direction derivative. -/
theorem gradient_sum_hasDerivAt {d : ℕ} (u h : Jet d) :
    HasDerivAt
      (fun t : ℝ =>
        ∑ i : Fin d,
          ((u.gx i + t * h.gx i) ^ 2 +
           (u.gy i + t * h.gy i) ^ 2))
      (∑ i : Fin d,
        2 * (u.gx i * h.gx i + u.gy i * h.gy i)) 0 := by
  have hi (i : Fin d) :
      HasDerivAt
        (fun t : ℝ =>
          ((u.gx i + t * h.gx i) ^ 2 +
           (u.gy i + t * h.gy i) ^ 2))
        (2 * (u.gx i * h.gx i + u.gy i * h.gy i)) 0 := by
    have hx := affine_deriv (u.gx i) (h.gx i)
    have hy := affine_deriv (u.gy i) (h.gy i)
    have hh := (hx.pow 2).add (hy.pow 2)
    convert hh using 1 <;>
      (try funext t) <;>
      simp [Pi.add_apply, Pi.mul_apply, Pi.pow_apply] <;> ring
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)

/-- **Corrected S004 multidimensional local first variation.**
This includes the sum over ALL spatial gradient directions, and
inherits the exact nonlinear corrected quotient/potential derivatives
and higher-order acceleration-Laplacian terms from the model-specific
complex real-two-component theorem. -/
theorem fullLocalDensity_hasDerivAt {d : ℕ}
    (epsilon alpha kappa theta gamma : ℝ)
    (V : ℝ → ℝ) (u h : Jet d) (Vprime : ℝ)
    (heps : 0 < epsilon) (ha : 0 ≤ alpha)
    (hV : HasDerivAt V Vprime
      (WCTLean.realTwoComponentDensity u.x u.y)) :
    HasDerivAt
      (fun t : ℝ => fullLocalDensity
        epsilon alpha kappa theta gamma V (shift u h t))
      (fullLocalDirection epsilon alpha kappa theta gamma
        Vprime u h) 0 := by
  have hVcore : HasDerivAt V Vprime
      (WCTLean.realTwoComponentDensity (core u).x (core u).y) := by
    simpa [core] using hV
  have hbase := localDensity_hasDerivAt epsilon alpha kappa theta gamma
    V (core u) (core h) Vprime heps ha hVcore
  have hgradient := gradient_sum_hasDerivAt u h
  have htotal := hbase.add hgradient
  convert htotal using 1
  · funext t
    simp only [fullLocalDensity, Pi.add_apply]
    rw [core_shift]
    congr 1
    all_goals
      apply Finset.sum_congr rfl
      intro i hi
      simp only [shift]
      ring

end WCTLean.S004FullSpatialJet
