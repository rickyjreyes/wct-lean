import Mathlib

namespace WCTLean

/-!
# Narrow canonical proof obligations: E15, CLE6, CLE7

These theorems concern precise scalar or separated-variable reductions.
They do not assert nonlinear PDE mode selection, the existence of a
nonzero separated toroidal eigenfunction, or completeness of its spectrum.
-/

/-- E15 (real scalar reduction): an amplitude following the explicitly
assumed cubic saturation ODE has the exact quadratic-power derivative
with the quartic damping term. This is not a theorem about every
complex Fourier coefficient of a nonlinear PDE. -/
theorem e15_scalar_modal_power_derivative (A : ℝ → ℝ)
    (t growth c : ℝ)
    (hA : HasDerivAt A (growth * A t - c / 2 * (A t) ^ 3) t) :
    HasDerivAt (fun τ => (A τ) ^ 2)
      (2 * growth * (A t) ^ 2 - c * (A t) ^ 4) t := by
  convert hA.pow 2 using 1 <;> ring

/-- E15: the same exact real-amplitude identity gives the advertised
upper bound in the special cubic-saturation ODE sector. -/
theorem e15_scalar_modal_growth_bound (A : ℝ → ℝ)
    (t growth c : ℝ)
    (hA : HasDerivAt A (growth * A t - c / 2 * (A t) ^ 3) t) :
    deriv (fun τ => (A τ) ^ 2) t ≤
      2 * growth * (A t) ^ 2 - c * (A t) ^ 4 := by
  rw [(e15_scalar_modal_power_derivative A t growth c hA).deriv]

/-- CLE6 (algebraic separated-sector implication): for nonzero mode
values f,g and transverse radius r, the separated product equation
implies the displayed quotient equation, treating f₂ and g₂ as
supplied second-derivative values. This does not establish PDE
separability or existence of such modes. -/
theorem cle6_separated_mode_quotient
    (f f₂ g g₂ R r sigma : ℝ)
    (hf : f ≠ 0) (hg : g ≠ 0) (hr : r ≠ 0)
    (hmode : f₂ * g + (R ^ 2 / r ^ 2) * f * g₂ =
      -(sigma ^ 2 * R ^ 2) * f * g) :
    f₂ / f + (R ^ 2 / r ^ 2) * (g₂ / g) =
      -(sigma ^ 2 * R ^ 2) := by
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  have hquot :
      f₂ / f + (R ^ 2 / r ^ 2) * (g₂ / g) =
        (f₂ * g + (R ^ 2 / r ^ 2) * f * g₂) / (f * g) := by
    field_simp [hf, hg, hr]
    <;> ring
  rw [hquot]
  apply (div_eq_iff hfg).2
  calc
    f₂ * g + (R ^ 2 / r ^ 2) * f * g₂ =
        -(sigma ^ 2 * R ^ 2) * f * g := hmode
    _ = -(sigma ^ 2 * R ^ 2) * (f * g) := by ring

/-- CLE7: the explicit trigonometric mode family for a nonnegative
integer angular winding. -/
noncomputable def cle7_angular_mode (A B : ℝ) (m : ℕ) (θ : ℝ) : ℝ :=
  A * Real.cos ((m : ℝ) * θ) + B * Real.sin ((m : ℝ) * θ)

/-- CLE7: every displayed integer-frequency mode is 2π-periodic.
The differential equation and general-solution completeness are not
claimed by this particular theorem. -/
theorem cle7_angular_mode_periodic (A B : ℝ) (m : ℕ) (θ : ℝ) :
    cle7_angular_mode A B m (θ + 2 * Real.pi) =
      cle7_angular_mode A B m θ := by
  have hc :
      Real.cos ((m : ℝ) * (θ + 2 * Real.pi)) =
        Real.cos ((m : ℝ) * θ) := by
    convert Real.cos_add_nat_mul_two_pi ((m : ℝ) * θ) m using 1 <;> ring
  have hs :
      Real.sin ((m : ℝ) * (θ + 2 * Real.pi)) =
        Real.sin ((m : ℝ) * θ) := by
    convert Real.sin_add_nat_mul_two_pi ((m : ℝ) * θ) m using 1 <;> ring
  simp only [cle7_angular_mode]
  rw [hc, hs]

end WCTLean
