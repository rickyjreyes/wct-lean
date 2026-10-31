import WCTLean.Continuum.CubicQuinticWholeSpace
import MathProofs.CubicQuinticFlow

/-!
# Constrained Euler–Lagrange equation for whole-plane CQ minimizers (#20)

For the independent cubic–quintic energy on `H²(ℝ²; ℂ)`,
`E(u) = ‖(Δ+k²)u‖² − (β/2)∫|u|⁴ + (γ/3)∫|u|⁶`, every constrained minimizer
`u ∈ 𝒢_m` (`M(u) = m > 0`, `E(u) = I(m)`, `γ > 0`) satisfies the weak
stationary equation

  `Re⟨(Δ+k²)u, (Δ+k²)h⟩ + Re⟨F(u), h⟩ = ω Re⟨u, h⟩`   for every `h ∈ H²(ℝ²; ℂ)`,

with `F(u) = −β|u|²u + γ|u|⁴u` (a.e., `ReyesMath.Sobolev.vl_Fnl_ae`) and the
explicit Lagrange multiplier

  `ω = (‖(Δ+k²)u‖² + Re⟨F(u), u⟩) / m`.

This is the weak form of `(Δ+k²)²u − β|u|²u + γ|u|⁴u = ω u`, i.e. a minimizer
is a standing wave `e^{-iωt}u` of the whole-plane CQ flow. Test functions are
arbitrary complex `H²` fields: no symmetry or reality is assumed.

Proof: the energy has an exact second-order Taylor bound on `H²` balls
(kinetic part exactly, potential part via the pinned
`ReyesMath.Sobolev.Nsp_taylor`); a tangent direction `h` is pushed back to
the mass sphere by the normalization `c(t) = √(m / M(u+th))`, which satisfies
`|c(t) − 1| ≤ t² ‖h‖²_{L²} / m`; minimality then forces the first variation
to vanish, and the general case splits off the radial direction.

Scope: independent CQ model only. Elliptic regularity beyond `H²` and
pointwise/exponential decay are not proved here.
-/

open ReyesMath ReyesMath.Sobolev InnerProductSpace

namespace WCTLean.Continuum

local notation "Sp" => ReyesMath.Sobolev.Hsp 2

/-- Half of the first variation of the CQ energy at `u` in direction `h`. -/
noncomputable def elForm (β γ k : ℝ) (u h : Sp) : ℝ :=
  (inner ℂ (Asp k u) (Asp k h)).re + (inner ℂ (vl (Fnl β γ u)) (vl h)).re

/-- The real `L²` pairing `Re⟨u, h⟩`. -/
noncomputable def massPairing (u h : Sp) : ℝ := (inner ℂ (vl u) (vl h)).re

theorem Asp_sub' (k : ℝ) (e f : Sp) : Asp k (e - f) = Asp k e - Asp k f :=
  map_sub (AspL k) e f

theorem elForm_add (β γ k : ℝ) (u x y : Sp) :
    elForm β γ k u (x + y) = elForm β γ k u x + elForm β γ k u y := by
  unfold elForm
  rw [Asp_add, vl_add, inner_add_right, inner_add_right, Complex.add_re, Complex.add_re]
  ring

theorem elForm_smul_real (β γ k : ℝ) (u x : Sp) (a : ℝ) :
    elForm β γ k u ((a : ℂ) • x) = a * elForm β γ k u x := by
  unfold elForm
  rw [Asp_smul, vl_smul, inner_smul_right, inner_smul_right, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul]
  ring

theorem massPairing_add (u x y : Sp) :
    massPairing u (x + y) = massPairing u x + massPairing u y := by
  unfold massPairing
  rw [vl_add, inner_add_right, Complex.add_re]

theorem massPairing_smul_real (u x : Sp) (a : ℝ) :
    massPairing u ((a : ℂ) • x) = a * massPairing u x := by
  unfold massPairing
  rw [vl_smul, inner_smul_right, Complex.re_ofReal_mul]

theorem massPairing_self (u : Sp) : massPairing u u = ‖vl u‖ ^ 2 := by
  unfold massPairing
  rw [← RCLike.re_to_complex]
  exact inner_self_eq_norm_sq _

/-- `|elForm u x| ≤ K ‖x‖` with `K = (1+k²)‖Au‖ + ‖F(u)‖_{L²}`. -/
theorem abs_elForm_le (β γ k : ℝ) (u x : Sp) :
    |elForm β γ k u x| ≤
      ((1 + k ^ 2) * ‖Asp k u‖ + ‖vl (Fnl β γ u)‖) * ‖x‖ := by
  unfold elForm
  have h1 : |(inner ℂ (Asp k u) (Asp k x)).re| ≤ ‖Asp k u‖ * ((1 + k ^ 2) * ‖x‖) :=
    (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (norm_Asp_le k x) (norm_nonneg _)))
  have h2 : |(inner ℂ (vl (Fnl β γ u)) (vl x)).re| ≤ ‖vl (Fnl β γ u)‖ * ‖x‖ :=
    (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (norm_vl_le x) (norm_nonneg _)))
  calc _ ≤ |(inner ℂ (Asp k u) (Asp k x)).re| + |(inner ℂ (vl (Fnl β γ u)) (vl x)).re| :=
        abs_add_le _ _
    _ ≤ _ := by nlinarith

/-- **Second-order Taylor bound for the CQ energy on `H²` balls.** -/
theorem Esp_taylor (β γ k : ℝ) {u w : Sp} {R : ℝ} (hu : ‖u‖ ≤ R) (hw : ‖w‖ ≤ R) :
    Esp β γ k w - Esp β γ k u ≤
      2 * elForm β γ k u (w - u) +
        ((1 + k ^ 2) ^ 2 + (3 * |β| * R ^ 2 + 5 * |γ| * R ^ 4)) * ‖w - u‖ ^ 2 := by
  have hpot := Nsp_taylor β γ hu hw
  have hkin : ‖Asp k w‖ ^ 2 = ‖Asp k u‖ ^ 2 +
      2 * (inner ℂ (Asp k u) (Asp k (w - u))).re + ‖Asp k (w - u)‖ ^ 2 := by
    have : Asp k w = Asp k u + Asp k (w - u) := by rw [Asp_sub']; abel
    rw [this, @norm_add_sq ℂ, RCLike.re_to_complex]
  have hAb : ‖Asp k (w - u)‖ ^ 2 ≤ (1 + k ^ 2) ^ 2 * ‖w - u‖ ^ 2 := by
    have := norm_Asp_le k (w - u)
    have h0 := norm_nonneg (Asp k (w - u))
    calc ‖Asp k (w - u)‖ ^ 2 ≤ ((1 + k ^ 2) * ‖w - u‖) ^ 2 := pow_le_pow_left₀ h0 this 2
      _ = _ := by ring
  have hvl : ‖vl w - vl u‖ ^ 2 ≤ ‖w - u‖ ^ 2 := by
    rw [← vl_sub]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_vl_le _) 2
  have hC : 0 ≤ 3 * |β| * R ^ 2 + 5 * |γ| * R ^ 4 := by positivity
  have hpot' := (abs_le.mp hpot).2
  rw [← vl_sub] at hpot'
  have hvl' := mul_le_mul_of_nonneg_left hvl hC
  rw [← vl_sub] at hvl'
  unfold Esp elForm
  nlinarith

/-- Elementary: if `0 ≤ a t + C t²` for all `|t| ≤ δ`, then `a = 0`. -/
theorem eq_zero_of_forall_quadratic_nonneg {a C δ : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (h : ∀ t : ℝ, |t| ≤ δ → 0 ≤ a * t + C * t ^ 2) : a = 0 := by
  by_contra ha
  set s : ℝ := min δ (|a| / (2 * (C + 1))) with hs
  have hspos : 0 < s := lt_min hδ (by positivity)
  have hsδ : s ≤ δ := min_le_left _ _
  have hsa : s ≤ |a| / (2 * (C + 1)) := min_le_right _ _
  have hCs : C * s ≤ |a| / 2 := by
    have h1 : (C + 1) * s ≤ |a| / 2 := by
      have := mul_le_mul_of_nonneg_left hsa (by positivity : (0 : ℝ) ≤ C + 1)
      calc (C + 1) * s ≤ (C + 1) * (|a| / (2 * (C + 1))) := this
        _ = |a| / 2 := by field_simp
    nlinarith
  -- choose t = -sign(a) s
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have ht := h s (by rw [abs_of_pos hspos]; exact hsδ)
    rw [abs_of_neg hneg] at hCs
    nlinarith
  · have ht := h (-s) (by rw [abs_neg, abs_of_pos hspos]; exact hsδ)
    rw [abs_of_pos hpos] at hCs
    nlinarith

/-- Scalar: `|t| x + t² q S ≤ |t| (x + q S)` for `|t| ≤ 1`, `q, S ≥ 0`. -/
theorem abs_mul_add_sq_le {t x q S : ℝ} (ht : |t| ≤ 1) (_hx : 0 ≤ x) (hq : 0 ≤ q)
    (hS : 0 ≤ S) : |t| * x + t ^ 2 * q * S ≤ |t| * (x + q * S) := by
  have h1 : t ^ 2 ≤ |t| := by
    rw [← sq_abs]
    have := mul_le_mul_of_nonneg_left ht (abs_nonneg t)
    nlinarith
  have := mul_le_mul_of_nonneg_right h1 (mul_nonneg hq hS)
  nlinarith

/-- Scalar facts for the mass normalization `c = √(m / (m + t² a))`. -/
theorem normalization_bounds {m a : ℝ} (hm : 0 < m) (ha : 0 ≤ a) (t : ℝ) :
    0 ≤ Real.sqrt (m / (m + t ^ 2 * a)) ∧ Real.sqrt (m / (m + t ^ 2 * a)) ≤ 1 ∧
    Real.sqrt (m / (m + t ^ 2 * a)) ^ 2 * (m + t ^ 2 * a) = m ∧
    |Real.sqrt (m / (m + t ^ 2 * a)) - 1| ≤ t ^ 2 * (a / m) := by
  have hta : 0 ≤ t ^ 2 * a := by positivity
  have hM : 0 < m + t ^ 2 * a := by linarith
  set c := Real.sqrt (m / (m + t ^ 2 * a)) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hcsq : c ^ 2 = m / (m + t ^ 2 * a) := Real.sq_sqrt (by positivity)
  have hratio : m / (m + t ^ 2 * a) ≤ 1 := by rw [div_le_one hM]; linarith
  have hc1 : c ≤ 1 := by
    calc c ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hratio
      _ = 1 := Real.sqrt_one
  refine ⟨hc0, hc1, by rw [hcsq]; field_simp, ?_⟩
  rw [abs_of_nonpos (by linarith), neg_sub]
  have hc2 : c ^ 2 ≤ c := by
    calc c ^ 2 = c * c := sq c
      _ ≤ 1 * c := mul_le_mul_of_nonneg_right hc1 hc0
      _ = c := one_mul c
  have h1 : 1 - m / (m + t ^ 2 * a) = t ^ 2 * a / (m + t ^ 2 * a) := by
    field_simp
    ring
  have h2 : t ^ 2 * a / (m + t ^ 2 * a) ≤ t ^ 2 * a / m :=
    div_le_div_of_nonneg_left hta hm (by linarith)
  have h3 : t ^ 2 * (a / m) = t ^ 2 * a / m := by ring
  rw [h3]
  linarith

/-- **Tangential stationarity.** A mass-constrained minimizer (over all of
`H²`) has vanishing first variation in every `L²`-tangent direction. -/
theorem elForm_eq_zero_of_tangent (β γ k : ℝ) {m : ℝ} (hm : 0 < m) {u : Sp}
    (hum : ‖vl u‖ ^ 2 = m)
    (hmin : ∀ v : Sp, ‖vl v‖ ^ 2 = m → Esp β γ k u ≤ Esp β γ k v)
    {h : Sp} (hh : massPairing u h = 0) :
    elForm β γ k u h = 0 := by
  set q : ℝ := ‖vl h‖ ^ 2 / m with hq
  set S : ℝ := ‖u‖ + ‖h‖ with hS
  set K : ℝ := (1 + k ^ 2) * ‖Asp k u‖ + ‖vl (Fnl β γ u)‖ with hK
  set C0 : ℝ := (1 + k ^ 2) ^ 2 + (3 * |β| * S ^ 2 + 5 * |γ| * S ^ 4) with hC0
  have hq0 : 0 ≤ q := by positivity
  have hS0 : 0 ≤ S := by positivity
  have hK0 : 0 ≤ K := by positivity
  have hC00 : 0 ≤ C0 := by positivity
  clear_value q S K C0
  apply eq_zero_of_forall_quadratic_nonneg (C := 2 * q * K * S + C0 * (‖h‖ + q * S) ^ 2)
    (δ := 1) one_pos (by positivity)
  intro t ht
  -- the line and its normalization
  set w : Sp := u + (t : ℂ) • h with hw
  have hMw : ‖vl w‖ ^ 2 = m + t ^ 2 * ‖vl h‖ ^ 2 := by
    rw [hw, vl_add, vl_smul, @norm_add_sq ℂ, inner_smul_right, RCLike.re_to_complex,
      Complex.re_ofReal_mul,
      norm_smul, hum]
    have : (inner ℂ (vl u) (vl h)).re = 0 := hh
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]; ring
  obtain ⟨hc0, hc1, hcM, hcdev⟩ := normalization_bounds hm (sq_nonneg ‖vl h‖) t
  set c : ℝ := Real.sqrt (m / (m + t ^ 2 * ‖vl h‖ ^ 2)) with hc
  have hcdev' : |c - 1| ≤ t ^ 2 * q := by rw [hq]; exact hcdev
  clear_value c
  set v : Sp := (c : ℂ) • w with hv
  have hvm : ‖vl v‖ ^ 2 = m := by
    rw [hv, vl_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hc0, mul_pow, hMw]
    exact hcM
  -- norms
  have ht1 : |t| ≤ 1 := ht
  have hwS : ‖w‖ ≤ S := by
    rw [hw]
    calc ‖u + (t : ℂ) • h‖ ≤ ‖u‖ + ‖(t : ℂ) • h‖ := norm_add_le _ _
      _ = ‖u‖ + |t| * ‖h‖ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ S := by
        have := mul_le_mul_of_nonneg_right ht1 (norm_nonneg h)
        linarith
  have hvS : ‖v‖ ≤ S := by
    rw [hv, norm_smul, Complex.norm_real, Real.norm_of_nonneg hc0]
    calc c * ‖w‖ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right hc1 (norm_nonneg _)
      _ ≤ S := by linarith
  have huS : ‖u‖ ≤ S := by rw [hS]; linarith [norm_nonneg h]
  -- decomposition of the displacement
  have hdisp : v - u = (t : ℂ) • h + ((c - 1 : ℝ) : ℂ) • w := by
    rw [hv, hw]
    push_cast
    rw [sub_smul, one_smul, smul_add]
    abel
  have hdn : ‖v - u‖ ≤ |t| * (‖h‖ + q * S) := by
    rw [hdisp]
    calc ‖(t : ℂ) • h + ((c - 1 : ℝ) : ℂ) • w‖
        ≤ ‖(t : ℂ) • h‖ + ‖((c - 1 : ℝ) : ℂ) • w‖ := norm_add_le _ _
      _ = |t| * ‖h‖ + |c - 1| * ‖w‖ := by
          rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |t| * ‖h‖ + (t ^ 2 * q) * S :=
          add_le_add_left (mul_le_mul hcdev' hwS (norm_nonneg _) (by positivity)) _
      _ ≤ |t| * (‖h‖ + q * S) :=
          abs_mul_add_sq_le ht1 (norm_nonneg h) hq0 hS0
  -- minimality and Taylor
  have hmin' := hmin v hvm
  have htay := Esp_taylor β γ k huS hvS
  have hel : elForm β γ k u (v - u) =
      t * elForm β γ k u h + (c - 1) * elForm β γ k u w := by
    rw [hdisp, elForm_add, elForm_smul_real, elForm_smul_real]
  have hwbound : |elForm β γ k u w| ≤ K * S := by
    have := abs_elForm_le β γ k u w
    calc _ ≤ K * ‖w‖ := by rw [hK]; exact this
      _ ≤ K * S := mul_le_mul_of_nonneg_left hwS hK0
  have hcw : (c - 1) * elForm β γ k u w ≤ t ^ 2 * q * (K * S) := by
    calc (c - 1) * elForm β γ k u w ≤ |(c - 1) * elForm β γ k u w| := le_abs_self _
      _ = |c - 1| * |elForm β γ k u w| := abs_mul _ _
      _ ≤ (t ^ 2 * q) * (K * S) :=
          mul_le_mul hcdev' hwbound (abs_nonneg _) (by positivity)
  have hsq : ‖v - u‖ ^ 2 ≤ t ^ 2 * (‖h‖ + q * S) ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hdn 2
    calc ‖v - u‖ ^ 2 ≤ (|t| * (‖h‖ + q * S)) ^ 2 := this
      _ = t ^ 2 * (‖h‖ + q * S) ^ 2 := by rw [mul_pow, sq_abs]
  have hsq' := mul_le_mul_of_nonneg_left hsq hC00
  -- combine
  have key : 0 ≤ 2 * elForm β γ k u (v - u) + C0 * ‖v - u‖ ^ 2 := by
    have h1 := htay
    rw [← hC0] at h1
    linarith
  rw [hel] at key
  have hp1 : 0 ≤ t ^ 2 * q * (K * S) := by positivity
  have hp2 : 0 ≤ C0 * (t ^ 2 * (‖h‖ + q * S) ^ 2) := by positivity
  have e1 : (2 * q * K * S + C0 * (‖h‖ + q * S) ^ 2) * t ^ 2 =
      2 * (t ^ 2 * q * (K * S)) + C0 * (t ^ 2 * (‖h‖ + q * S) ^ 2) := by ring
  rw [e1]
  linarith

/-- **Constrained Euler–Lagrange equation (Hilbert-space form).** -/
theorem euler_lagrange_of_constrained_min (β γ k : ℝ) {m : ℝ} (hm : 0 < m) {u : Sp}
    (hum : ‖vl u‖ ^ 2 = m)
    (hmin : ∀ v : Sp, ‖vl v‖ ^ 2 = m → Esp β γ k u ≤ Esp β γ k v) (h : Sp) :
    elForm β γ k u h = (elForm β γ k u u / m) * massPairing u h := by
  set lam : ℝ := massPairing u h / m with hlam
  set hT : Sp := h - (lam : ℂ) • u with hhT
  have htan : massPairing u hT = 0 := by
    have : massPairing u h = massPairing u hT + lam * massPairing u u := by
      rw [← massPairing_smul_real, ← massPairing_add, hhT, sub_add_cancel]
    rw [massPairing_self, hum, hlam] at this
    field_simp at this
    linarith
  have h0 := elForm_eq_zero_of_tangent β γ k hm hum hmin htan
  have hsplit : elForm β γ k u h = elForm β γ k u hT + lam * elForm β γ k u u := by
    rw [← elForm_smul_real, ← elForm_add, hhT, sub_add_cancel]
  rw [hsplit, h0, zero_add, hlam]
  ring

/-- **Euler–Lagrange equation for every whole-plane CQ minimizer.**
For `γ > 0` and `m > 0`, every `U ∈ 𝒢_m` satisfies, for all `h ∈ H²(ℝ²;ℂ)`,
`Re⟨(Δ+k²)U, (Δ+k²)h⟩ + Re⟨F(U), h⟩ = ω Re⟨U, h⟩`, with the explicit
multiplier `ω = (‖(Δ+k²)U‖² + Re⟨F(U), U⟩)/m`. -/
theorem minimizer_euler_lagrange {β γ k m : ℝ} (hγ : 0 < γ) (hm : 0 < m)
    {U : PlaneState} (hU : U ∈ ReyesMath.OrbitalStability.Gset β γ k m) :
    ∃ ω : ℝ,
      ω * m = ‖Asp k (H2.toSp U)‖ ^ 2 +
        (inner ℂ (vl (Fnl β γ (H2.toSp U))) (vl (H2.toSp U))).re ∧
      ∀ h : Sp,
        (inner ℂ (Asp k (H2.toSp U)) (Asp k h)).re +
          (inner ℂ (vl (Fnl β γ (H2.toSp U))) (vl h)).re =
        ω * (inner ℂ (vl (H2.toSp U)) (vl h)).re := by
  set u := H2.toSp U
  have hum : ‖vl u‖ ^ 2 = m := by rw [← M_eq_vl]; exact hU.1
  have hmin : ∀ v : Sp, ‖vl v‖ ^ 2 = m → Esp β γ k u ≤ Esp β γ k v := by
    intro v hv
    rw [← energy_eq_Esp, hU.2, ← energy_ofSp]
    exact StrictBinding.Imin_le_energy hγ (by rw [M_ofSp]; exact hv)
  refine ⟨elForm β γ k u u / m, ?_, fun h => ?_⟩
  · have hself : elForm β γ k u u = ‖Asp k u‖ ^ 2 +
        (inner ℂ (vl (Fnl β γ u)) (vl u)).re := by
      unfold elForm
      rw [← RCLike.re_to_complex, inner_self_eq_norm_sq]
    rw [div_mul_cancel₀ _ hm.ne', hself]
  · exact euler_lagrange_of_constrained_min β γ k hm hum hmin h

/-- The frozen-parameter instance: every whole-plane minimizer at the exact
rational frozen parameters is a weak standing wave with an explicit frequency. -/
theorem frozen_minimizer_euler_lagrange {U : PlaneState}
    (hU : U ∈ ReyesMath.OrbitalStability.Gset frozenBeta frozenBeta 1 frozenMass) :
    ∃ ω : ℝ,
      ω * frozenMass = ‖Asp 1 (H2.toSp U)‖ ^ 2 +
        (inner ℂ (vl (Fnl frozenBeta frozenBeta (H2.toSp U))) (vl (H2.toSp U))).re ∧
      ∀ h : Sp,
        (inner ℂ (Asp 1 (H2.toSp U)) (Asp 1 h)).re +
          (inner ℂ (vl (Fnl frozenBeta frozenBeta (H2.toSp U))) (vl h)).re =
        ω * (inner ℂ (vl (H2.toSp U)) (vl h)).re :=
  minimizer_euler_lagrange frozen_beta_positive frozen_mass_positive hU

end WCTLean.Continuum

#print axioms WCTLean.Continuum.Esp_taylor
#print axioms WCTLean.Continuum.elForm_eq_zero_of_tangent
#print axioms WCTLean.Continuum.euler_lagrange_of_constrained_min
#print axioms WCTLean.Continuum.minimizer_euler_lagrange
#print axioms WCTLean.Continuum.frozen_minimizer_euler_lagrange
