import WCTLean.Continuum.CurvatureEvolutionSymbol
import WCTLean.Continuum.CubicQuinticWholeSpace
import MathProofs.H2Algebra

/-!
# The M7 curvature nonlinearity on `H²(ℝ²; ℂ)`: mapping and Lipschitz estimates (#19)

The canonical M7 equation
`∂ₜψ = N_curv[ψ] + g|ψ|²ψ + c₁(Δ+σ²)ψ − c₂(Δ+k⋆²)²ψ + i c₃ m ψ + …`
has the quasilinear curvature term `N_curv[ψ] = Θ_ε[ψ] = −(Δψ) R_ε(ψ)`
(M6B), with `R_ε(z) = conj z / (|z|² + ε² e^{−2α|z|²})`.

This module proves, for `ε > 0`, `α ≥ 0`:

1. `R_ε` is **globally Lipschitz on ℂ** with the explicit constant
   `L_ε = 1/δ + (1 + 2αε²)(B² + 1/δ)`, `δ = min 1 (ε² e^{−2α})`, where `B` is
   the proved uniform bound on `‖R_ε‖`.
2. The pointwise curvature field `x ↦ −(Δψ)(x) R_ε(ψ(x))` of every whole-plane
   `H²` state lies in `L²`, with `‖N_curv[ψ]‖_{L²} ≤ B ‖Δψ‖_{L²}`.
3. **Local Lipschitz estimate** `H² → L²`:
   `‖N_curv[ψ] − N_curv[φ]‖²_{L²} ≤ 2B²‖Δψ − Δφ‖²_{L²} + 2L_ε²‖ψ − φ‖²_{H²}‖Δφ‖²_{L²}`,
   using the proved embedding `‖u‖_{L^∞} ≤ ‖u‖_{H²}` (`ReyesMath.Sobolev.ae_norm_vl_le`).

These are the nonlinear mapping estimates of a Duhamel formulation of M7 in
`C([0,T]; H²)`: the curvature term loses exactly two derivatives (`H² → L²`),
which the M7 fourth-order damping regains (see `CurvatureEvolutionSymbol`).
**Not proved here:** the damped semigroup on `H²`, its `L² → H²` smoothing
estimate, and the Duhamel fixed point, hence no M7 existence theorem yet.
-/

open MeasureTheory ReyesMath ReyesMath.Sobolev

namespace WCTLean.Continuum

open WCTLean

/-! ## 1. Global Lipschitz bound for `R_ε` -/

/-- Lower bound for the corrected denominator. -/
noncomputable def denomFloor (ε α : ℝ) : ℝ := min 1 (ε ^ 2 * Real.exp (-2 * α))

theorem denomFloor_pos {ε α : ℝ} (hε : 0 < ε) : 0 < denomFloor ε α :=
  lt_min one_pos (by positivity)

theorem denom_ge_floor (z : ℂ) {ε α : ℝ} (hα : 0 ≤ α) :
    denomFloor ε α ≤ complexRegularizerDenominator z ε α := by
  unfold complexRegularizerDenominator denomFloor
  set s := Complex.normSq z
  have hs : 0 ≤ s := Complex.normSq_nonneg z
  have he : 0 ≤ ε ^ 2 * Real.exp (-2 * α * s) := by positivity
  by_cases h1 : s ≤ 1
  · have hexp : Real.exp (-2 * α) ≤ Real.exp (-2 * α * s) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have : ε ^ 2 * Real.exp (-2 * α) ≤ ε ^ 2 * Real.exp (-2 * α * s) :=
      mul_le_mul_of_nonneg_left hexp (sq_nonneg ε)
    exact (min_le_right _ _).trans (by linarith)
  · push_neg at h1
    exact (min_le_left _ _).trans (by linarith)

/-- `|e^x − e^y| ≤ |x − y|` for `x, y ≤ 0`. -/
theorem abs_exp_sub_exp_le_of_nonpos {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y| ≤ |x - y| := by
  wlog hxy : x ≤ y generalizing x y
  · rw [abs_sub_comm, abs_sub_comm x]; exact this hy hx (le_of_not_ge hxy)
  have hey : Real.exp y ≤ 1 := Real.exp_le_one_iff.mpr hy
  have h1 : 1 - (y - x) ≤ Real.exp (-(y - x)) := by
    have := Real.add_one_le_exp (-(y - x)); linarith
  have h2 : Real.exp x = Real.exp y * Real.exp (-(y - x)) := by
    rw [← Real.exp_add]; ring_nf
  have hle : Real.exp x ≤ Real.exp y := Real.exp_le_exp.mpr hxy
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  have hpos := Real.exp_pos y
  nlinarith

theorem denom_sub_le (a b : ℂ) {ε α : ℝ} (hα : 0 ≤ α) :
    |complexRegularizerDenominator b ε α - complexRegularizerDenominator a ε α| ≤
      (1 + 2 * α * ε ^ 2) * ((‖a‖ + ‖b‖) * ‖a - b‖) := by
  unfold complexRegularizerDenominator
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have hab : |‖b‖ ^ 2 - ‖a‖ ^ 2| ≤ (‖a‖ + ‖b‖) * ‖a - b‖ := by
    have h1 : ‖b‖ ^ 2 - ‖a‖ ^ 2 = (‖b‖ + ‖a‖) * (‖b‖ - ‖a‖) := by ring
    rw [h1, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖b‖ + ‖a‖), add_comm ‖b‖]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [abs_sub_comm]; exact abs_norm_sub_norm_le a b
  have hexp := abs_exp_sub_exp_le_of_nonpos
    (x := -2 * α * ‖b‖ ^ 2) (y := -2 * α * ‖a‖ ^ 2) (by nlinarith [sq_nonneg ‖b‖])
    (by nlinarith [sq_nonneg ‖a‖])
  have hexp' : |Real.exp (-2 * α * ‖b‖ ^ 2) - Real.exp (-2 * α * ‖a‖ ^ 2)| ≤
      2 * α * |‖b‖ ^ 2 - ‖a‖ ^ 2| := by
    refine hexp.trans (le_of_eq ?_)
    rw [show -2 * α * ‖b‖ ^ 2 - -2 * α * ‖a‖ ^ 2 = -(2 * α) * (‖b‖ ^ 2 - ‖a‖ ^ 2) by ring,
      abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * α)]
  have hsplit : ‖b‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖b‖ ^ 2) -
      (‖a‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * ‖a‖ ^ 2)) =
      (‖b‖ ^ 2 - ‖a‖ ^ 2) +
        ε ^ 2 * (Real.exp (-2 * α * ‖b‖ ^ 2) - Real.exp (-2 * α * ‖a‖ ^ 2)) := by ring
  rw [hsplit]
  calc _ ≤ |‖b‖ ^ 2 - ‖a‖ ^ 2| +
        |ε ^ 2 * (Real.exp (-2 * α * ‖b‖ ^ 2) - Real.exp (-2 * α * ‖a‖ ^ 2))| :=
        abs_add_le _ _
    _ = |‖b‖ ^ 2 - ‖a‖ ^ 2| +
        ε ^ 2 * |Real.exp (-2 * α * ‖b‖ ^ 2) - Real.exp (-2 * α * ‖a‖ ^ 2)| := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg ε)]
    _ ≤ |‖b‖ ^ 2 - ‖a‖ ^ 2| + ε ^ 2 * (2 * α * |‖b‖ ^ 2 - ‖a‖ ^ 2|) := by
        gcongr
    _ = (1 + 2 * α * ε ^ 2) * |‖b‖ ^ 2 - ‖a‖ ^ 2| := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hab (by positivity)

/-- The explicit Lipschitz constant of `R_ε`. -/
noncomputable def reciprocalLipschitz (ε α : ℝ) : ℝ :=
  1 / denomFloor ε α +
    (1 + 2 * α * ε ^ 2) * (curvatureReciprocalBound ε α ^ 2 + 1 / denomFloor ε α)

theorem reciprocalLipschitz_nonneg {ε α : ℝ} (hε : 0 < ε) (hα : 0 ≤ α) :
    0 ≤ reciprocalLipschitz ε α := by
  have := denomFloor_pos (α := α) hε
  unfold reciprocalLipschitz; positivity

/-- **`R_ε` is globally Lipschitz on ℂ.** -/
theorem reciprocal_lipschitz (a b : ℂ) {ε α : ℝ} (hε : 0 < ε) (hα : 0 ≤ α) :
    ‖complexRegularizedReciprocal a ε α - complexRegularizedReciprocal b ε α‖ ≤
      reciprocalLipschitz ε α * ‖a - b‖ := by
  set Da := complexRegularizerDenominator a ε α
  set Db := complexRegularizerDenominator b ε α
  set δ := denomFloor ε α
  set B := curvatureReciprocalBound ε α
  have hδ : 0 < δ := denomFloor_pos hε
  have hDa : δ ≤ Da := denom_ge_floor a hα
  have hDb : δ ≤ Db := denom_ge_floor b hα
  have hDa0 : 0 < Da := hδ.trans_le hDa
  have hDb0 : 0 < Db := hδ.trans_le hDb
  have hRa : ‖a‖ / Da ≤ B := by
    have := complexRegularizedReciprocal_uniform_bound a ε α hε hα
    unfold complexRegularizedReciprocal at this
    rwa [norm_div, norm_star, Complex.norm_real, Real.norm_of_nonneg hDa0.le] at this
  have hRb : ‖b‖ / Db ≤ B := by
    have := complexRegularizedReciprocal_uniform_bound b ε α hε hα
    unfold complexRegularizedReciprocal at this
    rwa [norm_div, norm_star, Complex.norm_real, Real.norm_of_nonneg hDb0.le] at this
  have hb2 : ‖b‖ ^ 2 ≤ Db := by
    have : Db = ‖b‖ ^ 2 + ε ^ 2 * Real.exp (-2 * α * Complex.normSq b) := by
      simp only [Db, complexRegularizerDenominator, Complex.normSq_eq_norm_sq]
    rw [this]; have : 0 ≤ ε ^ 2 * Real.exp (-2 * α * Complex.normSq b) := by positivity
    linarith
  -- algebraic decomposition
  have hDa' : (Da : ℂ) ≠ 0 := by exact_mod_cast hDa0.ne'
  have hDb' : (Db : ℂ) ≠ 0 := by exact_mod_cast hDb0.ne'
  have hdec : complexRegularizedReciprocal a ε α - complexRegularizedReciprocal b ε α =
      (star a - star b) / (Da : ℂ) +
        star b * ((Db : ℂ) - (Da : ℂ)) / ((Da : ℂ) * (Db : ℂ)) := by
    have hRa' : complexRegularizedReciprocal a ε α = star a / (Da : ℂ) := rfl
    have hRb' : complexRegularizedReciprocal b ε α = star b / (Db : ℂ) := rfl
    rw [hRa', hRb']
    field_simp
    ring
  rw [hdec]
  have hDiff := denom_sub_le a b (ε := ε) hα
  have t1 : ‖(star a - star b) / (Da : ℂ)‖ ≤ (1 / δ) * ‖a - b‖ := by
    rw [norm_div, ← star_sub, norm_star, Complex.norm_real, Real.norm_of_nonneg hDa0.le,
      div_eq_mul_inv, mul_comm, one_div]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hδ hDa) (norm_nonneg _)
  have t2 : ‖star b * ((Db : ℂ) - (Da : ℂ)) / ((Da : ℂ) * (Db : ℂ))‖ ≤
      (1 + 2 * α * ε ^ 2) * (B ^ 2 + 1 / δ) * ‖a - b‖ := by
    rw [norm_div, norm_mul, norm_mul, norm_star, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hDa0.le, Real.norm_of_nonneg hDb0.le,
      show (Db : ℂ) - (Da : ℂ) = ((Db - Da : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs]
    have hk : 0 ≤ 1 + 2 * α * ε ^ 2 := by positivity
    have hprod : ‖b‖ * ((‖a‖ + ‖b‖)) / (Da * Db) ≤ B ^ 2 + 1 / δ := by
      have e1 : ‖b‖ * (‖a‖ + ‖b‖) / (Da * Db) =
          (‖a‖ / Da) * (‖b‖ / Db) + ‖b‖ ^ 2 / Db * (1 / Da) := by
        field_simp
      rw [e1]
      have f1 : (‖a‖ / Da) * (‖b‖ / Db) ≤ B * B :=
        mul_le_mul hRa hRb (by positivity)
          (by have := curvatureReciprocalBound_ge_one ε α; linarith)
      have f2 : ‖b‖ ^ 2 / Db ≤ 1 := (div_le_one hDb0).mpr hb2
      have f3 : 1 / Da ≤ 1 / δ := one_div_le_one_div_of_le hδ hDa
      have f4 : ‖b‖ ^ 2 / Db * (1 / Da) ≤ 1 * (1 / δ) :=
        mul_le_mul f2 f3 (by positivity) zero_le_one
      nlinarith
    calc ‖b‖ * |Db - Da| / (Da * Db)
        ≤ ‖b‖ * ((1 + 2 * α * ε ^ 2) * ((‖a‖ + ‖b‖) * ‖a - b‖)) / (Da * Db) := by
          gcongr
      _ = (1 + 2 * α * ε ^ 2) * (‖b‖ * (‖a‖ + ‖b‖) / (Da * Db)) * ‖a - b‖ := by ring
      _ ≤ (1 + 2 * α * ε ^ 2) * (B ^ 2 + 1 / δ) * ‖a - b‖ := by
          gcongr
  calc _ ≤ ‖(star a - star b) / (Da : ℂ)‖ +
        ‖star b * ((Db : ℂ) - (Da : ℂ)) / ((Da : ℂ) * (Db : ℂ))‖ := norm_add_le _ _
    _ ≤ (1 / δ) * ‖a - b‖ + (1 + 2 * α * ε ^ 2) * (B ^ 2 + 1 / δ) * ‖a - b‖ :=
        add_le_add t1 t2
    _ = reciprocalLipschitz ε α * ‖a - b‖ := by
        unfold reciprocalLipschitz; ring

/-! ## 2. The curvature field of an `H²` state lies in `L²` -/

theorem continuous_reciprocal {ε α : ℝ} (hε : 0 < ε) (hα : 0 ≤ α) :
    Continuous fun z : ℂ => complexRegularizedReciprocal z ε α := by
  have hL := reciprocalLipschitz_nonneg (α := α) hε hα
  refine (LipschitzWith.of_dist_le_mul (K := ⟨reciprocalLipschitz ε α, hL⟩) ?_).continuous
  intro a b
  rw [dist_eq_norm, dist_eq_norm]
  exact reciprocal_lipschitz a b hε hα

/-- The M6B/M7 curvature field `x ↦ −(Δψ)(x) R_ε(ψ(x))` of a whole-plane state. -/
noncomputable def curvField (ε α : ℝ) (U : PlaneState) :
    EuclideanSpace ℝ (Fin 2) → ℂ :=
  fun x => -(U.lap x) * complexRegularizedReciprocal (U.val x) ε α

/-- It is exactly the corrected operator `Θ_ε` evaluated pointwise. -/
theorem curvField_eq_theta (ε α : ℝ) (U : PlaneState) (x : EuclideanSpace ℝ (Fin 2)) :
    curvField ε α U x = thetaComplex (U.lap x) (U.val x) ε α := rfl

theorem memLp_curvField {ε α : ℝ} (hε : 0 < ε) (hα : 0 ≤ α) (U : PlaneState) :
    MemLp (curvField ε α U) 2 volume := by
  set B := curvatureReciprocalBound ε α
  have hB : 0 ≤ B := by have := curvatureReciprocalBound_ge_one ε α; linarith
  refine MemLp.of_le ((Lp.memLp U.lap).const_mul (B : ℂ)) ?_ ?_
  · exact (Lp.aestronglyMeasurable U.lap).neg.mul
      ((continuous_reciprocal hε hα).comp_aestronglyMeasurable (Lp.aestronglyMeasurable U.val))
  · refine Filter.Eventually.of_forall fun x => ?_
    simp only [curvField, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hB]
    rw [mul_comm B]
    exact mul_le_mul_of_nonneg_left
      (complexRegularizedReciprocal_uniform_bound _ ε α hε hα) (norm_nonneg _)

/-- The curvature operator `N_curv : H²(ℝ²; ℂ) → L²(ℝ²; ℂ)`. -/
noncomputable def curvOp {ε α : ℝ} (hε : 0 < ε) (hα : 0 ≤ α) (U : PlaneState) : L2 2 :=
  (memLp_curvField hε hα U).toLp _

theorem curvOp_ae {ε α : ℝ} (hε : 0 < ε) (hα : 0 ≤ α) (U : PlaneState) :
    curvOp hε hα U =ᵐ[volume] curvField ε α U :=
  (memLp_curvField hε hα U).coeFn_toLp

/-- **Mapping estimate** `‖N_curv[ψ]‖_{L²} ≤ B ‖Δψ‖_{L²}`. -/
theorem norm_curvOp_le {ε α : ℝ} (hε : 0 < ε) (hα : 0 ≤ α) (U : PlaneState) :
    ‖curvOp hε hα U‖ ≤ curvatureReciprocalBound ε α * ‖U.lap‖ := by
  set B := curvatureReciprocalBound ε α
  have hB : 0 ≤ B := by have := curvatureReciprocalBound_ge_one ε α; linarith
  have hsq : ‖curvOp hε hα U‖ ^ 2 ≤ (B * ‖U.lap‖) ^ 2 := by
    rw [normSq_eq_integral, mul_pow, normSq_eq_integral, ← integral_const_mul]
    refine integral_mono_ae (integrable_sq_L2 _) ((integrable_sq_L2 _).const_mul _) ?_
    filter_upwards [curvOp_ae hε hα U] with x hx
    rw [hx]
    simp only [curvField, norm_mul, norm_neg]
    have := complexRegularizedReciprocal_uniform_bound (U.val x) ε α hε hα
    have h0 := norm_nonneg (U.lap x)
    have h1 := norm_nonneg (complexRegularizedReciprocal (U.val x) ε α)
    have h2 : ‖U.lap x‖ * ‖complexRegularizedReciprocal (U.val x) ε α‖ ≤ ‖U.lap x‖ * B :=
      mul_le_mul_of_nonneg_left this h0
    have h3 := pow_le_pow_left₀ (mul_nonneg h0 h1) h2 2
    calc (‖U.lap x‖ * ‖complexRegularizedReciprocal (U.val x) ε α‖) ^ 2
        ≤ (‖U.lap x‖ * B) ^ 2 := h3
      _ = B ^ 2 * ‖U.lap x‖ ^ 2 := by ring
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq

/-- `vl (toSp U − toSp V)` is `U − V` in `L²`. -/
theorem vl_toSp_sub (U V : PlaneState) :
    vl (H2.toSp U - H2.toSp V) = U.val - V.val := rfl

/-- **Local Lipschitz estimate `H² → L²`** for the M7 curvature nonlinearity. -/
theorem curvOp_lipschitz {ε α : ℝ} (hε : 0 < ε) (hα : 0 ≤ α) (U V : PlaneState) :
    ‖curvOp hε hα U - curvOp hε hα V‖ ^ 2 ≤
      2 * curvatureReciprocalBound ε α ^ 2 * ‖U.lap - V.lap‖ ^ 2 +
        2 * reciprocalLipschitz ε α ^ 2 * ‖H2.toSp U - H2.toSp V‖ ^ 2 * ‖V.lap‖ ^ 2 := by
  set B := curvatureReciprocalBound ε α
  set L := reciprocalLipschitz ε α
  set E := ‖H2.toSp U - H2.toSp V‖
  have hB : 0 ≤ B := by have := curvatureReciprocalBound_ge_one ε α; linarith
  have hL : 0 ≤ L := reciprocalLipschitz_nonneg hε hα
  have hE : 0 ≤ E := norm_nonneg _
  rw [normSq_eq_integral, normSq_eq_integral, normSq_eq_integral, ← integral_const_mul,
    ← integral_const_mul]
  have hint := ((integrable_sq_L2 (U.lap - V.lap)).const_mul (2 * B ^ 2)).add
    ((integrable_sq_L2 V.lap).const_mul (2 * L ^ 2 * E ^ 2))
  rw [← integral_add ((integrable_sq_L2 (U.lap - V.lap)).const_mul (2 * B ^ 2))
    ((integrable_sq_L2 V.lap).const_mul (2 * L ^ 2 * E ^ 2))]
  refine integral_mono_ae (integrable_sq_L2 _) hint ?_
  have hsup := ae_norm_vl_le (H2.toSp U - H2.toSp V)
  rw [vl_toSp_sub] at hsup
  filter_upwards [curvOp_ae hε hα U, curvOp_ae hε hα V,
    Lp.coeFn_sub (curvOp hε hα U) (curvOp hε hα V), Lp.coeFn_sub U.lap V.lap,
    Lp.coeFn_sub U.val V.val, hsup] with x h1 h2 h3 h4 h5 h6
  rw [h3, Pi.sub_apply, h1, h2, h4, Pi.sub_apply]
  rw [h5, Pi.sub_apply] at h6
  set a := U.lap x; set b := V.lap x
  set Ru := complexRegularizedReciprocal (U.val x) ε α
  set Rv := complexRegularizedReciprocal (V.val x) ε α
  have hdec : curvField ε α U x - curvField ε α V x = -((a - b) * Ru) - b * (Ru - Rv) := by
    simp only [curvField, a, b, Ru, Rv]; ring
  have hRu : ‖Ru‖ ≤ B := complexRegularizedReciprocal_uniform_bound _ ε α hε hα
  have hRd : ‖Ru - Rv‖ ≤ L * E :=
    (reciprocal_lipschitz _ _ hε hα).trans (mul_le_mul_of_nonneg_left h6 hL)
  have hpt : ‖curvField ε α U x - curvField ε α V x‖ ≤ B * ‖a - b‖ + L * E * ‖b‖ := by
    rw [hdec]
    calc ‖-((a - b) * Ru) - b * (Ru - Rv)‖ ≤ ‖-((a - b) * Ru)‖ + ‖b * (Ru - Rv)‖ :=
          norm_sub_le _ _
      _ = ‖a - b‖ * ‖Ru‖ + ‖b‖ * ‖Ru - Rv‖ := by rw [norm_neg, norm_mul, norm_mul]
      _ ≤ ‖a - b‖ * B + ‖b‖ * (L * E) :=
          add_le_add (mul_le_mul_of_nonneg_left hRu (norm_nonneg _))
            (mul_le_mul_of_nonneg_left hRd (norm_nonneg _))
      _ = B * ‖a - b‖ + L * E * ‖b‖ := by ring
  have h0 := norm_nonneg (curvField ε α U x - curvField ε α V x)
  have hsq := pow_le_pow_left₀ h0 hpt 2
  have hyoung : (B * ‖a - b‖ + L * E * ‖b‖) ^ 2 ≤
      2 * B ^ 2 * ‖a - b‖ ^ 2 + 2 * L ^ 2 * E ^ 2 * ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (B * ‖a - b‖ - L * E * ‖b‖)]
  linarith

/-! ## 3. Parabolic smoothing of the linear M7 multiplier -/

/-- Real symbol of the linear M7 part `c₁(Δ+σ²) − c₂(Δ+k⋆²)²` at `|ξ|² = q`. -/
noncomputable def m7LinearSymbol (c₁ c₂ σ kstar q : ℝ) : ℝ :=
  c₁ * (σ ^ 2 - q) - c₂ * (kstar ^ 2 - q) ^ 2

/-- Its growth constant. -/
noncomputable def m7GrowthConstant (c₁ c₂ σ kstar : ℝ) : ℝ :=
  c₁ * σ ^ 2 + (|c₁| + 2 * c₂ * kstar ^ 2) ^ 2 / (2 * c₂)

theorem m7LinearSymbol_le (c₁ c₂ σ kstar : ℝ) (hc₂ : 0 < c₂) {q : ℝ} (hq : 0 ≤ q) :
    m7LinearSymbol c₁ c₂ σ kstar q ≤ m7GrowthConstant c₁ c₂ σ kstar - c₂ / 2 * q ^ 2 := by
  unfold m7LinearSymbol m7GrowthConstant
  set M := |c₁| + 2 * c₂ * kstar ^ 2
  have hc1 : -(c₁ * q) ≤ |c₁| * q := by nlinarith [neg_abs_le c₁, abs_nonneg c₁]
  have hk4 : 0 ≤ c₂ * kstar ^ 4 := by positivity
  have hyoung : M * q ≤ c₂ / 2 * q ^ 2 + M ^ 2 / (2 * c₂) := by
    have hsq : 0 ≤ (c₂ * q - M) ^ 2 / (2 * c₂) := by positivity
    have hexp : (c₂ * q - M) ^ 2 / (2 * c₂) = c₂ / 2 * q ^ 2 - M * q + M ^ 2 / (2 * c₂) := by
      field_simp; ring
    linarith
  nlinarith

/-- `q e^{−a q²} ≤ (2a)^{−1/2}` for `a > 0`, `q ≥ 0`. -/
theorem mul_exp_neg_sq_le {a q : ℝ} (ha : 0 < a) (hq : 0 ≤ q) :
    q * Real.exp (-(a * q ^ 2)) ≤ 1 / Real.sqrt (2 * a) := by
  have h2a : 0 < 2 * a := by positivity
  rw [le_div_iff₀ (Real.sqrt_pos.mpr h2a)]
  have hx := Real.add_one_le_exp (2 * a * q ^ 2)
  have he : Real.exp (-(a * q ^ 2)) ^ 2 * Real.exp (2 * a * q ^ 2) = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; simp; ring_nf
  have hpos := Real.exp_pos (-(a * q ^ 2))
  have hsq : (q * Real.exp (-(a * q ^ 2)) * Real.sqrt (2 * a)) ^ 2 ≤ 1 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt h2a.le]
    have hE := Real.exp_pos (2 * a * q ^ 2)
    have : q ^ 2 * (2 * a) ≤ Real.exp (2 * a * q ^ 2) := by linarith
    calc q ^ 2 * Real.exp (-(a * q ^ 2)) ^ 2 * (2 * a)
        = (q ^ 2 * (2 * a)) * Real.exp (-(a * q ^ 2)) ^ 2 := by ring
      _ ≤ Real.exp (2 * a * q ^ 2) * Real.exp (-(a * q ^ 2)) ^ 2 :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = 1 := by rw [mul_comm]; exact he
  have hnn : 0 ≤ q * Real.exp (-(a * q ^ 2)) * Real.sqrt (2 * a) := by positivity
  nlinarith

/-- **`L² → H²` smoothing of the linear M7 multiplier.** For `c₂ > 0`,
`t > 0`, every frequency `q = |ξ|² ≥ 0`:
`(1 + q) e^{t ℓ(q)} ≤ e^{t C} (1 + (c₂ t)^{−1/2})`.
The `t^{−1/2}` rate is integrable at `t = 0`, which is what allows the
fourth-order damping to absorb the two-derivative loss of `N_curv`. -/
theorem m7_multiplier_smoothing (c₁ c₂ σ kstar : ℝ) (hc₂ : 0 < c₂) {t q : ℝ}
    (ht : 0 < t) (hq : 0 ≤ q) :
    (1 + q) * Real.exp (t * m7LinearSymbol c₁ c₂ σ kstar q) ≤
      Real.exp (t * m7GrowthConstant c₁ c₂ σ kstar) * (1 + 1 / Real.sqrt (c₂ * t)) := by
  set C := m7GrowthConstant c₁ c₂ σ kstar
  set a := t * c₂ / 2 with ha
  have ha0 : 0 < a := by positivity
  have hsym := m7LinearSymbol_le c₁ c₂ σ kstar hc₂ hq
  have hexp : Real.exp (t * m7LinearSymbol c₁ c₂ σ kstar q) ≤
      Real.exp (t * C) * Real.exp (-(a * q ^ 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hsym ht.le
    rw [ha]; nlinarith
  have hE1 : Real.exp (-(a * q ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ a * q ^ 2 := by positivity
    linarith)
  have hsm := mul_exp_neg_sq_le ha0 hq
  have h2a : 2 * a = c₂ * t := by rw [ha]; ring
  rw [h2a] at hsm
  have hEt := Real.exp_pos (t * C)
  calc (1 + q) * Real.exp (t * m7LinearSymbol c₁ c₂ σ kstar q)
      ≤ (1 + q) * (Real.exp (t * C) * Real.exp (-(a * q ^ 2))) :=
        mul_le_mul_of_nonneg_left hexp (by linarith)
    _ = Real.exp (t * C) * (Real.exp (-(a * q ^ 2)) + q * Real.exp (-(a * q ^ 2))) := by ring
    _ ≤ Real.exp (t * C) * (1 + 1 / Real.sqrt (c₂ * t)) := by
        apply mul_le_mul_of_nonneg_left _ hEt.le
        linarith

end WCTLean.Continuum

#print axioms WCTLean.Continuum.reciprocal_lipschitz
#print axioms WCTLean.Continuum.memLp_curvField
#print axioms WCTLean.Continuum.norm_curvOp_le
#print axioms WCTLean.Continuum.curvOp_lipschitz
#print axioms WCTLean.Continuum.m7_multiplier_smoothing
