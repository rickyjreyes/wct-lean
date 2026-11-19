/-
  WCTLean/Fourier.lean

  E78 / issue #23: genuine integral orthogonality of the real trigonometric
  system on one full period `[0, 2π]`.

  The historical placeholder `cos_orthogonality_TODO` quantified over
  *integer* mode labels with only `n ≠ m`.  That statement is false: for
  `n = 1`, `m = -1` the integrand is `cos² x` and the integral is `π`.
  The placeholder is therefore kept only as a named proposition and is
  *refuted* below (`cos_orthogonality_TODO_false`).  The corrected
  statements are proved:

  * `integral_cos_mul_cos_of_natAbs_ne` — integer labels with `|n| ≠ |m|`;
  * `integral_cos_mul_cos_nat_of_ne` — natural labels with `n ≠ m`;
  * the matching sine/sine, sine/cosine orthogonality, and the
    normalization integrals `∫ cos² (n x) = ∫ sin² (n x) = π` (`n ≠ 0`).

  Everything here is about the real interval `[0, 2π]` with Lebesgue
  measure; the Hilbert-space (L²) spectral projection lives in
  `WCTLean/FourierSpectral.lean`.
-/

import Mathlib

namespace WCTLean

open Real intervalIntegral

/-- Pointwise product-to-sum identity used in Fourier orthogonality proofs:
    `2 cos(a) cos(b) = cos(a - b) + cos(a + b)`. -/
theorem two_cos_mul_cos (a b : ℝ) :
    2 * Real.cos a * Real.cos b = Real.cos (a - b) + Real.cos (a + b) := by
  rw [Real.cos_sub, Real.cos_add]; ring

/-- Product-to-sum: `2 sin(a) sin(b) = cos(a - b) - cos(a + b)`. -/
theorem two_sin_mul_sin (a b : ℝ) :
    2 * Real.sin a * Real.sin b = Real.cos (a - b) - Real.cos (a + b) := by
  rw [Real.cos_sub, Real.cos_add]; ring

/-- Product-to-sum: `2 sin(a) cos(b) = sin(a + b) + sin(a - b)`. -/
theorem two_sin_mul_cos (a b : ℝ) :
    2 * Real.sin a * Real.cos b = Real.sin (a + b) + Real.sin (a - b) := by
  rw [Real.sin_add, Real.sin_sub]; ring

/-- `sin (k · 2π) = 0` for every integer `k`. -/
theorem sin_int_mul_two_pi (k : ℤ) : Real.sin (k * (2 * π)) = 0 := by
  have h : (k : ℝ) * (2 * π) = ((2 * k : ℤ) : ℝ) * π := by
    push_cast; ring
  rw [h]
  exact Real.sin_int_mul_pi (2 * k)

/-- Full-period integral of `cos (k x)` vanishes for every nonzero integer `k`. -/
theorem integral_cos_int_mul_period {k : ℤ} (hk : k ≠ 0) :
    ∫ x in (0 : ℝ)..(2 * π), Real.cos (k * x) = 0 := by
  have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hk', integral_cos,
    sin_int_mul_two_pi]
  simp

/-- Full-period integral of `sin (k x)` vanishes for every integer `k`
(including `k = 0`). -/
theorem integral_sin_int_mul_period (k : ℤ) :
    ∫ x in (0 : ℝ)..(2 * π), Real.sin (k * x) = 0 := by
  by_cases hk : k = 0
  · subst hk; simp
  · have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) hk', integral_sin,
      Real.cos_int_mul_two_pi]
    simp

/-- Full-period integral of the constant mode `cos (0 · x) = 1`. -/
theorem integral_cos_zero_mul_period :
    ∫ x in (0 : ℝ)..(2 * π), Real.cos ((0 : ℤ) * x) = 2 * π := by
  simp

private theorem cos_int_mul_intervalIntegrable (k : ℤ) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.cos (k * x)) MeasureTheory.volume a b :=
  (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable a b

private theorem sin_int_mul_intervalIntegrable (k : ℤ) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.sin (k * x)) MeasureTheory.volume a b :=
  (Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable a b

/-- Integral of `cos (n x) cos (m x)` over a full period, written through the
two "difference" and "sum" modes. -/
theorem integral_cos_mul_cos_eq (n m : ℤ) :
    ∫ x in (0 : ℝ)..(2 * π), Real.cos (n * x) * Real.cos (m * x) =
      ((∫ x in (0 : ℝ)..(2 * π), Real.cos (((n - m : ℤ) : ℝ) * x)) +
        ∫ x in (0 : ℝ)..(2 * π), Real.cos (((n + m : ℤ) : ℝ) * x)) / 2 := by
  have hpt : ∀ x : ℝ, Real.cos (n * x) * Real.cos (m * x) =
      (Real.cos (((n - m : ℤ) : ℝ) * x) + Real.cos (((n + m : ℤ) : ℝ) * x)) / 2 := by
    intro x
    have h := two_cos_mul_cos (n * x) (m * x)
    push_cast
    rw [show ((n : ℝ) - m) * x = n * x - m * x by ring,
      show ((n : ℝ) + m) * x = n * x + m * x by ring]
    linarith
  simp_rw [hpt]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (cos_int_mul_intervalIntegrable _ _ _) (cos_int_mul_intervalIntegrable _ _ _)]

/-- Integral of `sin (n x) sin (m x)` over a full period. -/
theorem integral_sin_mul_sin_eq (n m : ℤ) :
    ∫ x in (0 : ℝ)..(2 * π), Real.sin (n * x) * Real.sin (m * x) =
      ((∫ x in (0 : ℝ)..(2 * π), Real.cos (((n - m : ℤ) : ℝ) * x)) -
        ∫ x in (0 : ℝ)..(2 * π), Real.cos (((n + m : ℤ) : ℝ) * x)) / 2 := by
  have hpt : ∀ x : ℝ, Real.sin (n * x) * Real.sin (m * x) =
      (Real.cos (((n - m : ℤ) : ℝ) * x) - Real.cos (((n + m : ℤ) : ℝ) * x)) / 2 := by
    intro x
    have h := two_sin_mul_sin (n * x) (m * x)
    push_cast
    rw [show ((n : ℝ) - m) * x = n * x - m * x by ring,
      show ((n : ℝ) + m) * x = n * x + m * x by ring]
    linarith
  simp_rw [hpt]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (cos_int_mul_intervalIntegrable _ _ _) (cos_int_mul_intervalIntegrable _ _ _)]

/-- Integral of `sin (n x) cos (m x)` over a full period. -/
theorem integral_sin_mul_cos_eq (n m : ℤ) :
    ∫ x in (0 : ℝ)..(2 * π), Real.sin (n * x) * Real.cos (m * x) =
      ((∫ x in (0 : ℝ)..(2 * π), Real.sin (((n + m : ℤ) : ℝ) * x)) +
        ∫ x in (0 : ℝ)..(2 * π), Real.sin (((n - m : ℤ) : ℝ) * x)) / 2 := by
  have hpt : ∀ x : ℝ, Real.sin (n * x) * Real.cos (m * x) =
      (Real.sin (((n + m : ℤ) : ℝ) * x) + Real.sin (((n - m : ℤ) : ℝ) * x)) / 2 := by
    intro x
    have h := two_sin_mul_cos (n * x) (m * x)
    push_cast
    rw [show ((n : ℝ) - m) * x = n * x - m * x by ring,
      show ((n : ℝ) + m) * x = n * x + m * x by ring]
    linarith
  simp_rw [hpt]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (sin_int_mul_intervalIntegrable _ _ _) (sin_int_mul_intervalIntegrable _ _ _)]

/-- **Cosine orthogonality (integer labels).**  If `|n| ≠ |m|` then
`∫₀^{2π} cos (n x) cos (m x) dx = 0`.  The hypothesis `|n| ≠ |m|` is exactly
what is needed: `n ≠ m` alone is not enough (`cos_orthogonality_TODO_false`). -/
theorem integral_cos_mul_cos_of_natAbs_ne {n m : ℤ} (h : n.natAbs ≠ m.natAbs) :
    ∫ x in (0 : ℝ)..(2 * π), Real.cos (n * x) * Real.cos (m * x) = 0 := by
  have h1 : n - m ≠ 0 := by
    intro h'; apply h; rw [sub_eq_zero.mp h']
  have h2 : n + m ≠ 0 := by
    intro h'; apply h; rw [eq_neg_of_add_eq_zero_left h', Int.natAbs_neg]
  rw [integral_cos_mul_cos_eq, integral_cos_int_mul_period h1, integral_cos_int_mul_period h2]
  simp

/-- **Cosine orthogonality (natural labels).**  For natural numbers `n ≠ m`,
`∫₀^{2π} cos (n x) cos (m x) dx = 0`. -/
theorem integral_cos_mul_cos_nat_of_ne {n m : ℕ} (h : n ≠ m) :
    ∫ x in (0 : ℝ)..(2 * π), Real.cos (n * x) * Real.cos (m * x) = 0 := by
  have := integral_cos_mul_cos_of_natAbs_ne (n := (n : ℤ)) (m := (m : ℤ))
    (by simpa using h)
  simpa using this

/-- **Sine orthogonality (integer labels).**  If `|n| ≠ |m|` then
`∫₀^{2π} sin (n x) sin (m x) dx = 0`. -/
theorem integral_sin_mul_sin_of_natAbs_ne {n m : ℤ} (h : n.natAbs ≠ m.natAbs) :
    ∫ x in (0 : ℝ)..(2 * π), Real.sin (n * x) * Real.sin (m * x) = 0 := by
  have h1 : n - m ≠ 0 := by
    intro h'; apply h; rw [sub_eq_zero.mp h']
  have h2 : n + m ≠ 0 := by
    intro h'; apply h; rw [eq_neg_of_add_eq_zero_left h', Int.natAbs_neg]
  rw [integral_sin_mul_sin_eq, integral_cos_int_mul_period h1, integral_cos_int_mul_period h2]
  simp

/-- **Sine orthogonality (natural labels).** -/
theorem integral_sin_mul_sin_nat_of_ne {n m : ℕ} (h : n ≠ m) :
    ∫ x in (0 : ℝ)..(2 * π), Real.sin (n * x) * Real.sin (m * x) = 0 := by
  have := integral_sin_mul_sin_of_natAbs_ne (n := (n : ℤ)) (m := (m : ℤ))
    (by simpa using h)
  simpa using this

/-- **Sine/cosine orthogonality.**  For *all* integer labels,
`∫₀^{2π} sin (n x) cos (m x) dx = 0` (no separation hypothesis is needed). -/
theorem integral_sin_mul_cos_int (n m : ℤ) :
    ∫ x in (0 : ℝ)..(2 * π), Real.sin (n * x) * Real.cos (m * x) = 0 := by
  rw [integral_sin_mul_cos_eq, integral_sin_int_mul_period, integral_sin_int_mul_period]
  simp

/-- **Cosine normalization.**  `∫₀^{2π} cos² (n x) dx = π` for `n ≠ 0`. -/
theorem integral_cos_mul_cos_self {n : ℤ} (hn : n ≠ 0) :
    ∫ x in (0 : ℝ)..(2 * π), Real.cos (n * x) * Real.cos (n * x) = π := by
  have h2 : n + n ≠ 0 := by omega
  rw [integral_cos_mul_cos_eq, integral_cos_int_mul_period h2]
  simp

/-- **Sine normalization.**  `∫₀^{2π} sin² (n x) dx = π` for `n ≠ 0`. -/
theorem integral_sin_mul_sin_self {n : ℤ} (hn : n ≠ 0) :
    ∫ x in (0 : ℝ)..(2 * π), Real.sin (n * x) * Real.sin (n * x) = π := by
  have h2 : n + n ≠ 0 := by omega
  rw [integral_sin_mul_sin_eq, integral_cos_int_mul_period h2]
  simp

/-- `∫₀^{2π} cos² (n x) = π` (square form), `n ≠ 0`. -/
theorem integral_cos_sq_int_mul {n : ℤ} (hn : n ≠ 0) :
    ∫ x in (0 : ℝ)..(2 * π), Real.cos (n * x) ^ 2 = π := by
  simpa [sq] using integral_cos_mul_cos_self hn

/-- `∫₀^{2π} sin² (n x) = π` (square form), `n ≠ 0`. -/
theorem integral_sin_sq_int_mul {n : ℤ} (hn : n ≠ 0) :
    ∫ x in (0 : ℝ)..(2 * π), Real.sin (n * x) ^ 2 = π := by
  simpa [sq] using integral_sin_mul_sin_self hn

/-- The opposite-sign cosine pair is *not* orthogonal: for `n ≠ 0`,
`∫₀^{2π} cos (n x) cos (-n x) dx = π`. -/
theorem integral_cos_mul_cos_neg {n : ℤ} (hn : n ≠ 0) :
    ∫ x in (0 : ℝ)..(2 * π), Real.cos (n * x) * Real.cos (((-n : ℤ) : ℝ) * x) = π := by
  have h : ∀ x : ℝ, Real.cos (((-n : ℤ) : ℝ) * x) = Real.cos (n * x) := by
    intro x; push_cast; rw [neg_mul, Real.cos_neg]
  simp_rw [h]
  exact integral_cos_mul_cos_self hn

/--
  Historical E78/#23 placeholder, kept verbatim as a *proposition*.

  It quantifies over integer labels with only `n ≠ m`; this is false
  (see `cos_orthogonality_TODO_false`).  The corrected, proved replacements
  are `integral_cos_mul_cos_of_natAbs_ne` and `integral_cos_mul_cos_nat_of_ne`.
-/
def cos_orthogonality_TODO : Prop :=
  ∀ n m : ℤ, n ≠ m →
    (∫ x in (0 : ℝ)..(2 * Real.pi), Real.cos (n * x) * Real.cos (m * x)) = 0

/-- **Refutation of the historical placeholder.**  The integer-label
statement with only `n ≠ m` fails at `n = 1`, `m = -1`, where the integral
equals `π ≠ 0`. -/
theorem cos_orthogonality_TODO_false : ¬ cos_orthogonality_TODO := by
  intro h
  have h1 := h 1 (-1) (by decide)
  have h2 := integral_cos_mul_cos_neg (n := 1) one_ne_zero
  have : (π : ℝ) = 0 := by
    rw [← h2]
    simpa using h1
  exact Real.pi_ne_zero this

/-- **Corrected cosine orthogonality statement** (the integer statement with
the exact separation hypothesis `|n| ≠ |m|`) holds. -/
def cos_orthogonality_corrected : Prop :=
  ∀ n m : ℤ, n.natAbs ≠ m.natAbs →
    (∫ x in (0 : ℝ)..(2 * Real.pi), Real.cos (n * x) * Real.cos (m * x)) = 0

theorem cos_orthogonality_corrected_holds : cos_orthogonality_corrected :=
  fun _ _ h => integral_cos_mul_cos_of_natAbs_ne h

/-- Exact characterization of the full-period cosine Gram matrix on integer
labels: the integral is `0` if `|n| ≠ |m|`, `π` if `|n| = |m| ≠ 0`, and `2π`
if `n = m = 0`. -/
theorem integral_cos_mul_cos_int (n m : ℤ) :
    ∫ x in (0 : ℝ)..(2 * π), Real.cos (n * x) * Real.cos (m * x) =
      if n.natAbs ≠ m.natAbs then 0 else if n = 0 then 2 * π else π := by
  by_cases h : n.natAbs = m.natAbs
  · rw [if_neg (not_not.mpr h)]
    rcases Int.natAbs_eq_natAbs_iff.mp h with hnm | hnm
    · subst hnm
      by_cases hn : n = 0
      · subst hn; simp
      · rw [if_neg hn]; exact integral_cos_mul_cos_self hn
    · subst hnm
      by_cases hm : m = 0
      · subst hm; simp
      · have hm' : -m ≠ 0 := neg_ne_zero.mpr hm
        rw [if_neg hm']
        have := integral_cos_mul_cos_neg (n := -m) hm'
        simpa using this
  · rw [if_pos h]; exact integral_cos_mul_cos_of_natAbs_ne h

end WCTLean
