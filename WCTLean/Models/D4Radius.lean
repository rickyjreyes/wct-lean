import Mathlib

namespace WCTLean

/-!
# Conditional D4 a posteriori radius bounds (issue #21)

D4 here denotes the square-symmetric branch of the separate 2D periodic
Hamiltonian PDE, NOT four spatial dimensions and NOT the full WCT action.
No constants, inverse estimates, tail bounds or root certificates are asserted
to have been computed. These reusable inequalities consume verified bounds
once supplied by the PDE evidence track.
-/

/-- The two exact scalar tests needed by the D4 a posteriori radius argument.
The constants are inputs, not a certificate for a particular computed state. -/
def D4RadiusConditions (Y0 Z0 L r : ℝ) : Prop :=
  0 < r ∧ 0 ≤ Y0 ∧ 0 ≤ Z0 ∧ 0 ≤ L ∧
    Y0 + Z0 * r + L * r ^ 2 / 2 ≤ r ∧
    Z0 + L * r < 1

/-- The verified outward bound supplies the rearranged self-map margin. -/
theorem d4_radius_margin
    (Y0 Z0 L r : ℝ) (h : D4RadiusConditions Y0 Z0 L r) :
    Y0 + (Z0 + L * r / 2) * r ≤ r := by
  dsimp [D4RadiusConditions] at h
  nlinarith [h.2.2.2.2.1]

/-- A strict contraction margin follows from the second scalar test, with
nonnegative factor under the named positivity assumptions. -/
theorem d4_contraction_factor_range
    (Y0 Z0 L r : ℝ) (h : D4RadiusConditions Y0 Z0 L r) :
    0 ≤ Z0 + L * r ∧ Z0 + L * r < 1 := by
  dsimp [D4RadiusConditions] at h
  rcases h with ⟨hr, _, hZ, hL, _, hcontract⟩
  exact ⟨add_nonneg hZ (mul_nonneg hL (le_of_lt hr)), hcontract⟩

/-- A conditional Banach-space self-mapping statement. This is the useful
analytical interface: the supplied center residual and local Taylor bound
produce invariance of the closed radius ball. It does NOT assert that the
specific D4 stationary/bordered map has these bounds, or that a PDE solution
exists. -/
theorem d4_maps_closed_ball
    {E : Type*} [NormedAddCommGroup E]
    (T : E → E) (center : E) (Y0 Z0 L r : ℝ)
    (h : D4RadiusConditions Y0 Z0 L r)
    (hresidual : ‖T center - center‖ ≤ Y0)
    (htaylor : ∀ x, ‖x - center‖ ≤ r →
      ‖T x - T center‖ ≤ (Z0 + L * r / 2) * ‖x - center‖)
    (x : E) (hx : ‖x - center‖ ≤ r) :
    ‖T x - center‖ ≤ r := by
  have hmargin := d4_radius_margin Y0 Z0 L r h
  have hfactor : 0 ≤ Z0 + L * r / 2 := by
    dsimp [D4RadiusConditions] at h
    rcases h with ⟨hr, _, hZ, hL, _, _⟩
    have hhalf : 0 ≤ L * r / 2 := div_nonneg (mul_nonneg hL (le_of_lt hr)) (by norm_num)
    exact add_nonneg hZ hhalf
  calc
    ‖T x - center‖ = ‖(T x - T center) + (T center - center)‖ := by
      congr 1
      abel
    _ ≤ ‖T x - T center‖ + ‖T center - center‖ := norm_add_le _ _
    _ ≤ (Z0 + L * r / 2) * ‖x - center‖ + Y0 :=
      add_le_add (htaylor x hx) hresidual
    _ ≤ (Z0 + L * r / 2) * r + Y0 := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left hx hfactor) Y0
    _ ≤ r := by linarith

end WCTLean
