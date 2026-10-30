import Mathlib

/-!
# Algebraic real-linearization of the independent D4 cubic–quintic nonlinearity

These are exact complex-polynomial Taylor identities valid without a radial or
D4-symmetric perturbation restriction. The full continuum Frechet derivative,
unbounded fourth-order operator domains and constrained spectral gap are
separate obligations, not asserted here.
-/

namespace WCTLean.Continuum

/-- `|z|² z` written as a polynomial in z and conjugate z. -/
noncomputable def cubicTerm (z : ℂ) : ℂ := z ^ 2 * star z

/-- `|z|⁴ z` written as a polynomial in z and conjugate z. -/
noncomputable def quinticTerm (z : ℂ) : ℂ := z ^ 3 * (star z) ^ 2

theorem cubicTerm_eq_normSq (z : ℂ) :
    cubicTerm z = (Complex.normSq z : ℂ) * z := by
  calc
    cubicTerm z = (z * star z) * z := by
      unfold cubicTerm
      ring
    _ = (Complex.normSq z : ℂ) * z := by
      change (z * Complex.conj z) * z = (Complex.normSq z : ℂ) * z
      rw [Complex.mul_conj]

theorem quinticTerm_eq_normSq (z : ℂ) :
    quinticTerm z = ((Complex.normSq z : ℝ) ^ 2 : ℂ) * z := by
  calc
    quinticTerm z = (z * star z) ^ 2 * z := by
      unfold quinticTerm
      ring
    _ = ((Complex.normSq z : ℝ) ^ 2 : ℂ) * z := by
      change (z * Complex.conj z) ^ 2 * z =
        ((Complex.normSq z : ℝ) ^ 2 : ℂ) * z
      rw [Complex.mul_conj]
      norm_cast

/-- The algebraic first-order term for `|z|² z` in an arbitrary complex
perturbation h. Its dependence on conjugate h makes it real-linear,
not complex-linear. -/
noncomputable def cubicFirstOrder (z h : ℂ) : ℂ :=
  2 * z * star z * h + z ^ 2 * star h

/-- The algebraic first-order term for `|z|⁴ z`. -/
noncomputable def quinticFirstOrder (z h : ℂ) : ℂ :=
  3 * z ^ 2 * (star z) ^ 2 * h +
    2 * z ^ 3 * star z * star h

/-- An exact Taylor identity, valid for arbitrary complex z and h. -/
theorem cubic_exact_expansion (z h : ℂ) :
    cubicTerm (z + h) - cubicTerm z - cubicFirstOrder z h =
      h ^ 2 * star z + 2 * z * h * star h + h ^ 2 * star h := by
  simp only [cubicTerm, cubicFirstOrder, star_add]
  ring

/-- Exact polynomial remainder beyond the real-linear quintic term. -/
theorem quintic_exact_expansion (z h : ℂ) :
    quinticTerm (z + h) - quinticTerm z - quinticFirstOrder z h =
      (3 * z * h ^ 2 + h ^ 3) * (star z) ^ 2 +
      (6 * z ^ 2 * h + 6 * z * h ^ 2 + 2 * h ^ 3) *
        star z * star h +
      (z ^ 3 + 3 * z ^ 2 * h + 3 * z * h ^ 2 + h ^ 3) *
        (star h) ^ 2 := by
  simp only [quinticTerm, quinticFirstOrder, star_add]
  ring

/-- The exact same-model cubic–quintic pointwise nonlinearity. -/
noncomputable def cubicQuinticPotential (β γ : ℝ) (z : ℂ) : ℂ :=
  -(β : ℂ) * cubicTerm z + (γ : ℂ) * quinticTerm z

/-- The corresponding real-linear candidate, with no radial restriction. -/
noncomputable def cubicQuinticFirstOrder (β γ : ℝ) (z h : ℂ) : ℂ :=
  -(β : ℂ) * cubicFirstOrder z h +
    (γ : ℂ) * quinticFirstOrder z h

/-- Pointwise potential agrees with the PDE's modulus-squared form. -/
theorem cubicQuinticPotential_eq (β γ : ℝ) (z : ℂ) :
    cubicQuinticPotential β γ z =
      -(β : ℂ) * (Complex.normSq z : ℂ) * z +
        (γ : ℂ) * ((Complex.normSq z : ℝ) ^ 2 : ℂ) * z := by
  simp [cubicQuinticPotential, cubicTerm_eq_normSq, quinticTerm_eq_normSq]
  ring

#print axioms WCTLean.Continuum.cubic_exact_expansion
#print axioms WCTLean.Continuum.quintic_exact_expansion
#print axioms WCTLean.Continuum.cubicQuinticPotential_eq

end WCTLean.Continuum
