import Mathlib
import WCTLean.Models.S004ClassicalField

/-!
# Phase XXIII: real periodic fields imply matching classical derivative traces

A complete periodic boundary condition is a *translation identity*
for the underlying classical scalar field:
   φ(t,x+L)=φ(t,x) for every t,x.
The ordinary derivative identities already supplied by our genuine
classical two-real-component fields imply the SAME translation identity
for their first and second spatial derivatives, and first and second
temporal derivatives.

Consequently periodic matching of all original S004 field/velocity/
acceleration/gradient/Laplacian jets follows from field periodicity,
not by assuming unrelated trace equalities for ten jet coordinates.

This is an exact C²-type classical result. It does not establish the
periodic Sobolev trace theorem, the nonlinear momentum derivative
Green regularity, or global well-posedness.
-/

namespace WCTLean.S004ClassicalPeriodicity

open WCTLean.S004ClassicalField

/-- An exact periodic real function's ordinary derivative is
periodic with the SAME period, when the derivative is certified
everywhere by HasDerivAt. No independent derivative trace
periodicity premise occurs. -/
theorem real_derivative_periodic
    (f g : ℝ → ℝ) (L : ℝ)
    (hPer : ∀ x, f (x + L) = f x)
    (hDeriv : ∀ x, HasDerivAt f (g x) x) :
    ∀ x, g (x + L) = g x := by
  intro x
  have htrans : HasDerivAt (fun s : ℝ => s + L) 1 x :=
    (hasDerivAt_id x).add_const L
  have hleft : HasDerivAt (fun s => f (s + L)) (g (x + L)) x := by
    simpa using (hDeriv (x + L)).comp x htrans
  have hfun : (fun s : ℝ => f (s + L)) = f :=
    funext hPer
  rw [hfun] at hleft
  exact hleft.deriv.symm.trans (hDeriv x).deriv

/-- The SECOND real derivative inherits the same spatial period
by twice applying the genuine first-derivative theorem. -/
theorem real_second_derivative_periodic
    (f f1 f2 : ℝ → ℝ) (L : ℝ)
    (hPer : ∀ x, f (x + L) = f x)
    (h1 : ∀ x, HasDerivAt f (f1 x) x)
    (h2 : ∀ x, HasDerivAt f1 (f2 x) x) :
    ∀ x, f2 (x + L) = f2 x := by
  exact real_derivative_periodic f1 f2 L
    (real_derivative_periodic f f1 L hPer h1) h2

/-- A single real classical S004 scalar field periodic in its
SPATIAL variable has both first and second TEMPORAL derivative
fields spatially periodic as well. The proof differentiates
the actual field translation identity in time. -/
theorem classical_time_jets_periodic
    (u : ClassicalScalarField) (L : ℝ)
    (hPer : ∀ t x, u.field (t, x + L) = u.field (t, x)) :
    ∀ t x,
      u.dt (t, x + L) = u.dt (t, x) ∧
      u.dtt (t, x + L) = u.dtt (t, x) := by
  have hDt : ∀ t x,
      u.dt (t, x + L) = u.dt (t, x) := by
    intro t x
    have hfun : (fun s : ℝ => u.field (s, x + L)) =
        (fun s => u.field (s, x)) :=
      funext (fun s => hPer s x)
    have hd := (u.time1 t (x + L)).deriv
    rw [hfun] at hd
    exact hd.symm.trans (u.time1 t x).deriv
  have hDtt : ∀ t x,
      u.dtt (t, x + L) = u.dtt (t, x) := by
    intro t x
    have hfun : (fun s : ℝ => u.dt (s, x + L)) =
        (fun s => u.dt (s, x)) :=
      funext (fun s => hDt s x)
    have hd := (u.time2 t (x + L)).deriv
    rw [hfun] at hd
    exact hd.symm.trans (u.time2 t x).deriv
  exact fun t x => ⟨hDt t x, hDtt t x⟩

/-- First and second classical SPATIAL derivatives inherit the
underlying scalar field's exact translation periodicity. -/
theorem classical_space_jets_periodic
    (u : ClassicalScalarField) (L : ℝ)
    (hPer : ∀ t x, u.field (t, x + L) = u.field (t, x)) :
    ∀ t x,
      u.dx (t, x + L) = u.dx (t, x) ∧
      u.dxx (t, x + L) = u.dxx (t, x) := by
  intro t x
  have h1 := real_derivative_periodic
    (fun s => u.field (t,s)) (fun s => u.dx (t,s)) L
    (hPer t) (u.space1 t)
  have h2 := real_second_derivative_periodic
    (fun s => u.field (t,s)) (fun s => u.dx (t,s))
    (fun s => u.dxx (t,s)) L (hPer t) (u.space1 t) (u.space2 t)
  exact ⟨h1 x, h2 x⟩

/-- Original corrected S004 scalar field periodicity implies
periodicity of ALL five corresponding physical scalar jet
components, without independently postulating any derivative
periodicity. Apply separately to real and imaginary fields. -/
theorem classical_all_five_jets_periodic
    (u : ClassicalScalarField) (L : ℝ)
    (hPer : ∀ t x, u.field (t, x + L) = u.field (t, x)) :
    ∀ t x,
      u.field (t, x + L) = u.field (t, x) ∧
      u.dt (t, x + L) = u.dt (t, x) ∧
      u.dtt (t, x + L) = u.dtt (t, x) ∧
      u.dx (t, x + L) = u.dx (t, x) ∧
      u.dxx (t, x + L) = u.dxx (t, x) := by
  intro t x
  obtain ⟨ht1, ht2⟩ := classical_time_jets_periodic u L hPer t x
  obtain ⟨hx1, hx2⟩ := classical_space_jets_periodic u L hPer t x
  exact ⟨hPer t x, ht1, ht2, hx1, hx2⟩

end WCTLean.S004ClassicalPeriodicity
