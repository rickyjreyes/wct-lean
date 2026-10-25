import WCTLean.Models.D4Binding

/-! Phase VII rational gap constants and explicitly conditional analytic bridges.
The concrete H²/Fourier/compactness/flow instances are NOT supplied here.
No definition packages an assumed binding or attained infimum. -/

namespace WCTLean.D4

noncomputable section

open Filter Topology

def gapSlack : ℝ := 221 / 100000
def gaussianDFloor : ℝ := 7*frozenBeta*frozenMass/1760-1/50
def gaussianCCap : ℝ := 30203/40000+frozenBeta*frozenMass^2/8100
def uniformGapConstant : ℝ := gapSlack*gaussianDFloor^2/(4*gaussianCCap)

theorem gap_slack_pos : 0 < gapSlack := by norm_num [gapSlack]
theorem gaussian_d_floor_pos : 0 < gaussianDFloor := by
  norm_num [gaussianDFloor, frozenBeta, frozenMass]
theorem gaussian_c_cap_pos : 0 < gaussianCCap := by
  norm_num [gaussianCCap, frozenBeta, frozenMass]
theorem uniform_gap_constant_pos : 0 < uniformGapConstant := by
  unfold uniformGapConstant
  exact div_pos (mul_pos gap_slack_pos (sq_pos_of_pos gaussian_d_floor_pos))
    (mul_pos (by norm_num) gaussian_c_cap_pos)

/-- A convenient rational lower bound; no decimal approximation is a premise. -/
theorem uniform_gap_constant_gt : (1:ℝ)/3000000 < uniformGapConstant := by
  norm_num [uniformGapConstant, gapSlack, gaussianDFloor, gaussianCCap,
    frozenBeta, frozenMass]

theorem frozen_slack_floor : gapSlack ≤ 1-frozenMass/frozenThreshold := by
  have hs := Real.sqrt_pos.2 frozen_rho_pos
  have hsq : (frozenMass*Real.sqrt frozenRho)^2 = frozenMass^2*frozenRho := by
    rw [mul_pow, Real.sq_sqrt frozen_rho_pos.le]
  have hm : frozenRho*frozenMass^2 < 9*(1-gapSlack)^2 := by
    norm_num [frozenRho, frozenBeta, frozenMass, gapSlack]
  have hb : 0 < 3*(1-gapSlack) := by norm_num [gapSlack]
  have hn : 0 ≤ frozenMass*Real.sqrt frozenRho := mul_nonneg frozen_mass_pos.le hs.le
  have bound : frozenMass*Real.sqrt frozenRho ≤ 3*(1-gapSlack) := by
    nlinarith [sq_nonneg (frozenMass*Real.sqrt frozenRho-3*(1-gapSlack))]
  have ratio : frozenMass/frozenThreshold = frozenMass*Real.sqrt frozenRho/3 := by
    unfold frozenThreshold
    field_simp
  rw [ratio]
  linarith

/-- Gaussian lower bound after c2,c4 have been derived from actual integrals. -/
theorem gaussian_gap_lower (b d C c2 c4 : ℝ) (hb : 0 < b) (hd : 0 < d)
    (hC : 0 < C) (hc4 : 0 < c4) (hc2 : c2 ≤ -b*d) (hcap : c4 ≤ b*C) :
    b*d^2/(4*C) ≤ c2^2/(4*c4) := by
  have hbd : 0 < b*d := mul_pos hb hd
  have hsq : (b*d)^2 ≤ c2^2 := by
    nlinarith [sq_nonneg (c2+b*d)]
  have h1 := mul_le_mul_of_nonneg_left hcap (mul_nonneg hb.le (sq_nonneg d))
  have h2 := mul_le_mul_of_nonneg_right hsq hC.le
  apply (div_le_div_iff₀ (by positivity : 0 < 4*C) (by positivity : 0 < 4*c4)).2
  nlinarith

/-- Quantified split assembly. Its energy-per-mass premises are visible. -/
theorem split_gap_from_per_mass (I : ℝ → ℝ) (m a κ : ℝ)
    (hm : 0 < m) (ha : 0 < a) (ham : a < m)
    (horder : I (m-a)/(m-a) ≤ I a/a)
    (hgap : κ*a/m ≤ I (m-a)/(m-a)-I m/m) :
    κ*a ≤ I a+I (m-a)-I m := by
  have hb : 0 < m-a := sub_pos.2 ham
  have h1 := mul_le_mul_of_nonneg_left horder ha.le
  have h2 := mul_le_mul_of_nonneg_left hgap hm.le
  have hcancel : a*(I a/a) = I a := by field_simp
  have hcancel2 : m*(κ*a/m) = κ*a := by field_simp
  have hid : I a+I (m-a)-I m =
      (I a-a*(I (m-a)/(m-a)))+m*(I (m-a)/(m-a)-I m/m) := by
    field_simp
    ring
  rw [hcancel] at h1
  rw [hcancel2] at h2
  rw [hid]
  linarith

/-- Constructs the old inputs from the weaker, direct Sobolev cap.
Negativity, adjusted sequences and admissible trials still require H² instances. -/
theorem binding_inputs_from_cap (I : ℝ → ℝ)
    (negative : ∀ a, 0 < a → I a < 0)
    (adjusted : ∀ a b, 0 < a → a < b → a+b < 2*frozenThreshold →
      ∃ T Q S : ℕ → ℝ,
        Tendsto (fun n => profileEnergy frozenBeta frozenBeta (T n) (Q n) (S n))
          atTop (𝓝 (I a)) ∧
        ∀ n, 0 ≤ T n ∧ 0 ≤ S n ∧
          S n ≤ (Real.sqrt frozenRho/4)*a*Q n ∧
          I b/(b/a) ≤ amplitudePerMass frozenBeta frozenBeta (T n) (Q n) (S n) (b/a)) :
    BindingSequenceInputs I frozenBeta frozenBeta frozenThreshold := by
  refine ⟨negative, ?_⟩
  intro a b ha hab hspan
  obtain ⟨T,Q,S,hlim,hrows⟩ := adjusted a b ha hab hspan
  refine ⟨T,Q,S,hlim,?_⟩
  intro n
  obtain ⟨hT,hS,hcap,htrial⟩ := hrows n
  have balance : frozenBeta*(Real.sqrt frozenRho/4)*frozenThreshold = 3*frozenBeta/4 := by
    have hs := (Real.sqrt_pos.2 frozen_rho_pos).ne'
    unfold frozenThreshold
    field_simp
    <;> ring
  exact ⟨hT, mul_nonneg frozen_beta_pos.le hS,
    amplitude_ratio_from_L6_bound frozenBeta frozenBeta (Real.sqrt frozenRho/4)
      frozenThreshold a b (Q n) (S n) frozen_beta_pos.le frozen_threshold_pos ha
      (le_of_lt (lt_trans ha hab)) balance hcap, htrial⟩

/-- Extends the old same-mass implication to nearby-mass energy trapping.
The actual flow and near-mass trapping theorem are still explicit premises. -/
theorem nearby_mass_stability_from_trapping {X : Type*}
    (M H d : X → ℝ) (flow : ℝ → X → X) (m Emin : ℝ)
    (mass_conserved : ∀ t u, M (flow t u) = M u)
    (energy_conserved : ∀ t u, H (flow t u) = H u)
    (initial_control : ∀ η > 0, ∃ δ > 0, ∀ u,
      d u < δ → |M u-m| < η ∧ H u < Emin+η)
    (trapping : ∀ ε > 0, ∃ η > 0, ∀ u,
      |M u-m| < η → H u < Emin+η → d u < ε) :
    ∀ ε > 0, ∃ δ > 0, ∀ u, d u < δ → ∀ t, d (flow t u) < ε := by
  intro ε hε
  obtain ⟨η,hη,htrap⟩ := trapping ε hε
  obtain ⟨δ,hδ,hinit⟩ := initial_control η hη
  refine ⟨δ,hδ,?_⟩
  intro u hu t
  obtain ⟨hm,hH⟩ := hinit u hu
  apply htrap (flow t u)
  · rw [mass_conserved]
    exact hm
  · rw [energy_conserved]
    exact hH

/-- An all-time observable bound makes the specified escape set empty. -/
theorem no_exit_of_observable_bound (C : ℝ → ℝ) (α : ℝ)
    (bound : ∀ t, 1-α ≤ C t) : {t : ℝ | 0 ≤ t ∧ C t < 1-α} = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.2
  intro t ht
  exact (not_lt_of_ge (bound t)) ht.2

end
end WCTLean.D4
