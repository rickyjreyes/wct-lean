import Mathlib

/-!
# A posteriori (radii-polynomial) contraction theorem

This is the abstract analytical theorem used by computer-assisted proofs of
stationary PDE roots, as scoped in WCT-Lean issue #21 and `wct-pde` #24:
if a fixed-point map `T` on a real Banach space satisfies, around an
approximate solution `xbar`,

* `‖T xbar - xbar‖ ≤ Y0`,
* `‖DT x‖ ≤ Z0 + L ‖x - xbar‖` on the closed ball of radius `r`,
* `Y0 + Z0 r + (L/2) r² ≤ r` and `Z0 + L r < 1`,

then `T` has exactly one fixed point in that closed ball.

The theorem is fully proved here for an arbitrary real Banach space. It does
**not** by itself certify the periodic D4 root: instantiating it requires the
concrete torus Fourier/Wiener space, the bordered Newton map, and kernel-checked
values of `Y0`, `Z0`, `L`, and `r` for the saved candidate. Those inputs are
currently produced and checked outside Lean (`wct-pde` #24).
-/

open Set Metric

namespace WCTLean.Continuum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The integrated derivative bound: along the segment from `xbar`, the
displacement of `T` is controlled by `Z0 ρ + (L/2) ρ²`, with `ρ = ‖x - xbar‖`. -/
theorem radii_displacement_bound
    {T : E → E} {T' : E → E →L[ℝ] E} {xbar : E} {r Z0 L : ℝ}
    (hderiv : ∀ x ∈ closedBall xbar r, HasFDerivAt T (T' x) x)
    (hbound : ∀ x ∈ closedBall xbar r, ‖T' x‖ ≤ Z0 + L * ‖x - xbar‖)
    {x : E} (hx : x ∈ closedBall xbar r) :
    ‖T x - T xbar‖ ≤ Z0 * ‖x - xbar‖ + L / 2 * ‖x - xbar‖ ^ 2 := by
  set v : E := x - xbar with hv
  set ρ : ℝ := ‖v‖ with hρ
  have hρr : ρ ≤ r := by
    rw [hρ, hv, ← dist_eq_norm]
    exact mem_closedBall.mp hx
  -- The segment stays in the ball.
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, xbar + s • v ∈ closedBall xbar r := by
    intro s hs
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hs.1]
    calc s * ρ ≤ 1 * ρ := by
          exact mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
      _ = ρ := one_mul ρ
      _ ≤ r := hρr
  -- Path and its derivative.
  let g : ℝ → E := fun s => T (xbar + s • v) - T xbar
  let g' : ℝ → E := fun s => T' (xbar + s • v) v
  have hpath : ∀ s : ℝ, HasDerivAt (fun s : ℝ => xbar + s • v) v s := by
    intro s
    simpa using ((hasDerivAt_id s).smul_const v).const_add xbar
  have hg : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt g (g' s) s := by
    intro s hs
    have h1 := (hderiv _ (hseg s hs)).comp_hasDerivAt s (hpath s)
    simpa [g, g'] using h1.sub_const (T xbar)
  -- Comparison function.
  let B : ℝ → ℝ := fun s => Z0 * ρ * s + L / 2 * ρ ^ 2 * s ^ 2
  let B' : ℝ → ℝ := fun s => Z0 * ρ + L * ρ ^ 2 * s
  have hB : ∀ s : ℝ, HasDerivAt B (B' s) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => Z0 * ρ * s) (Z0 * ρ) s := by
      simpa using (hasDerivAt_id s).const_mul (Z0 * ρ)
    have h2 : HasDerivAt (fun s : ℝ => L / 2 * ρ ^ 2 * s ^ 2)
        (L / 2 * ρ ^ 2 * ((2 : ℕ) * s ^ (2 - 1))) s :=
      (hasDerivAt_pow 2 s).const_mul (L / 2 * ρ ^ 2)
    have h3 := h1.add h2
    convert h3 using 1
    simp [B']
    ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (f := g) (f' := g') (a := 0) (b := 1) (B := B) (B' := B')
    (fun s hs => (hg s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hg s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (by simp [g, B])
    (fun s _ => (hB s).continuousAt.continuousWithinAt)
    (fun s _ => (hB s).hasDerivWithinAt)
    (by
      intro s hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hs
      have hpt := hseg s hs'
      have hdist : ‖xbar + s • v - xbar‖ = s * ρ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs'.1]
      calc ‖g' s‖ = ‖T' (xbar + s • v) v‖ := rfl
        _ ≤ ‖T' (xbar + s • v)‖ * ‖v‖ := (T' _).le_opNorm v
        _ ≤ (Z0 + L * (s * ρ)) * ρ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            have hb := hbound _ hpt
            rwa [hdist] at hb
        _ = B' s := by simp only [B']; ring)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
  have hg1 : g 1 = T x - T xbar := by
    simp [g, v]
  rw [hg1] at key
  simpa [B] using key

/-- **Radii-polynomial contraction theorem.** Under the a posteriori bounds
`Y0 + Z0 r + (L/2) r² ≤ r` and `Z0 + L r < 1`, the map `T` has exactly one
fixed point in the closed ball of radius `r` about `xbar`. -/
theorem radii_polynomial_unique_fixed_point [CompleteSpace E]
    {T : E → E} {T' : E → E →L[ℝ] E} {xbar : E} {r Y0 Z0 L : ℝ}
    (hr : 0 ≤ r) (hZ0 : 0 ≤ Z0) (hL : 0 ≤ L)
    (hderiv : ∀ x ∈ closedBall xbar r, HasFDerivAt T (T' x) x)
    (hbound : ∀ x ∈ closedBall xbar r, ‖T' x‖ ≤ Z0 + L * ‖x - xbar‖)
    (hY0 : ‖T xbar - xbar‖ ≤ Y0)
    (hradii : Y0 + Z0 * r + L / 2 * r ^ 2 ≤ r)
    (hcontr : Z0 + L * r < 1) :
    ∃! x, x ∈ closedBall xbar r ∧ T x = x := by
  set K : ℝ := Z0 + L * r with hK
  have hK0 : 0 ≤ K := by positivity
  -- Uniform derivative bound on the ball.
  have hbd : ∀ x ∈ closedBall xbar r, ‖T' x‖ ≤ K := by
    intro x hx
    have hxr : ‖x - xbar‖ ≤ r := by
      rw [← dist_eq_norm]; exact mem_closedBall.mp hx
    calc ‖T' x‖ ≤ Z0 + L * ‖x - xbar‖ := hbound x hx
      _ ≤ K := by
        have := mul_le_mul_of_nonneg_left hxr hL
        linarith
  -- Lipschitz estimate on the ball (mean-value inequality on a convex set).
  have hlip : ∀ x ∈ closedBall xbar r, ∀ y ∈ closedBall xbar r,
      ‖T x - T y‖ ≤ K * ‖x - y‖ := by
    intro x hx y hy
    exact (convex_closedBall xbar r).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => (hderiv z hz).hasFDerivWithinAt) hbd hy hx
  -- The ball is mapped into itself.
  have hmaps : MapsTo T (closedBall xbar r) (closedBall xbar r) := by
    intro x hx
    have hxr : ‖x - xbar‖ ≤ r := by
      rw [← dist_eq_norm]; exact mem_closedBall.mp hx
    have hdisp := radii_displacement_bound hderiv hbound hx
    have hmono : Z0 * ‖x - xbar‖ + L / 2 * ‖x - xbar‖ ^ 2 ≤
        Z0 * r + L / 2 * r ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left hxr hZ0
      have h2 : ‖x - xbar‖ ^ 2 ≤ r ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hxr 2
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ L / 2)
      linarith
    rw [mem_closedBall, dist_eq_norm]
    calc ‖T x - xbar‖ = ‖(T x - T xbar) + (T xbar - xbar)‖ := by
          congr 1; abel
      _ ≤ ‖T x - T xbar‖ + ‖T xbar - xbar‖ := norm_add_le _ _
      _ ≤ r := by linarith
  -- Banach fixed point on the complete closed ball.
  let S := closedBall xbar r
  haveI : CompleteSpace S := (isClosed_closedBall.completeSpace_coe)
  haveI : Nonempty S := ⟨⟨xbar, mem_closedBall_self hr⟩⟩
  let f : S → S := hmaps.restrict T S S
  let Knn : NNReal := ⟨K, hK0⟩
  have hKlt : Knn < 1 := by
    change (⟨K, hK0⟩ : NNReal) < 1
    rw [← NNReal.coe_lt_coe]; simpa using hcontr
  have hfl : LipschitzWith Knn f := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    change dist (T a) (T b) ≤ K * dist (a : E) (b : E)
    rw [dist_eq_norm, dist_eq_norm]
    exact hlip a a.2 b b.2
  have hc : ContractingWith Knn f := ⟨hKlt, hfl⟩
  obtain ⟨p, hp⟩ : ∃ p : S, f p = p :=
    ⟨ContractingWith.fixedPoint f hc, ContractingWith.fixedPoint_isFixedPt hc⟩
  refine ⟨p, ⟨p.2, congrArg Subtype.val hp⟩, ?_⟩
  rintro y ⟨hy, hTy⟩
  have h := hlip y hy p p.2
  have hTp : T p = p := congrArg Subtype.val hp
  rw [hTy, hTp] at h
  have hK1 : K < 1 := hcontr
  have hn : ‖y - (p : E)‖ = 0 := by
    have h0 := norm_nonneg (y - (p : E))
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- **Newton-map corollary.** If `T x = x - A (F x)` with `A` injective
(e.g. an approximate inverse certified to be injective), the radii-polynomial
bounds give exactly one zero of `F` in the ball. -/
theorem radii_polynomial_unique_zero [CompleteSpace E]
    {F : E → E} (A : E →L[ℝ] E) (hA : Function.Injective A)
    {T' : E → E →L[ℝ] E} {xbar : E} {r Y0 Z0 L : ℝ}
    (hr : 0 ≤ r) (hZ0 : 0 ≤ Z0) (hL : 0 ≤ L)
    (hderiv : ∀ x ∈ closedBall xbar r,
      HasFDerivAt (fun x => x - A (F x)) (T' x) x)
    (hbound : ∀ x ∈ closedBall xbar r, ‖T' x‖ ≤ Z0 + L * ‖x - xbar‖)
    (hY0 : ‖A (F xbar)‖ ≤ Y0)
    (hradii : Y0 + Z0 * r + L / 2 * r ^ 2 ≤ r)
    (hcontr : Z0 + L * r < 1) :
    ∃! x, x ∈ closedBall xbar r ∧ F x = 0 := by
  have hfix : ∀ x, (x - A (F x) = x ↔ F x = 0) := by
    intro x
    constructor
    · intro h
      have : A (F x) = A 0 := by
        rw [map_zero]; exact sub_eq_self.mp h
      exact hA this
    · intro h; simp [h]
  have hY0' : ‖(xbar - A (F xbar)) - xbar‖ ≤ Y0 := by
    simpa [sub_sub_cancel_left, norm_neg] using hY0
  obtain ⟨x, ⟨hx, hTx⟩, huniq⟩ :=
    radii_polynomial_unique_fixed_point (T := fun x => x - A (F x))
      hr hZ0 hL hderiv hbound hY0' hradii hcontr
  refine ⟨x, ⟨hx, (hfix x).mp hTx⟩, ?_⟩
  rintro y ⟨hy, hFy⟩
  exact huniq y ⟨hy, (hfix y).mpr hFy⟩

end WCTLean.Continuum

#print axioms WCTLean.Continuum.radii_displacement_bound
#print axioms WCTLean.Continuum.radii_polynomial_unique_fixed_point
#print axioms WCTLean.Continuum.radii_polynomial_unique_zero
