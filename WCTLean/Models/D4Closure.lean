import WCTLean.Models.D4Analytical

/-! Phase VIII: assemble the quantitative ALL-split theorem from the visible
adjusted-sequence and Gaussian-trial obligations. This is not a concrete H²
instance. In particular no premise of this file assumes binding or attainment.
The concrete remaining obligations are listed in docs/D4_PHASE_VIII_LEDGER.md. -/

namespace WCTLean.D4
noncomputable section

def gaussianEnergyFloor : ℝ := gaussianDFloor^2/(4*gaussianCCap)

theorem gaussian_energy_floor_pos : 0 < gaussianEnergyFloor := by
  unfold gaussianEnergyFloor
  exact div_pos (sq_pos_of_pos gaussian_d_floor_pos)
    (mul_pos (by norm_num) gaussian_c_cap_pos)

theorem gap_constant_factorization :
    uniformGapConstant = gapSlack*gaussianEnergyFloor := by
  unfold uniformGapConstant gaussianEnergyFloor
  ring

theorem frozen_per_mass_nonincreasing (I : ℝ → ℝ)
    (inputs : BindingSequenceInputs I frozenBeta frozenBeta frozenThreshold)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ frozenMass) :
    I b/b ≤ I a/a := by
  rcases eq_or_lt_of_le hab with he | he
  · subst b
    exact le_rfl
  · have span : a+b < 2*frozenThreshold := by linarith [frozen_below_threshold]
    have scale := infimum_scaling_bound I frozenBeta frozenBeta frozenThreshold
      a b inputs frozen_threshold_pos ha he span
    have gap := quantitative_gap I frozenThreshold a b frozen_threshold_pos ha he span
      (inputs.negative a ha) scale
    linarith [gap.1, gap.2]

/-- The Gaussian premise concerns only masses in the upper half interval.
It follows conventionally from the exact trial integrals; that bridge is open.
All smaller splits, including both endpoints, are assembled here. -/
theorem frozen_quantitative_all_splits (I : ℝ → ℝ)
    (inputs : BindingSequenceInputs I frozenBeta frozenBeta frozenThreshold)
    (gaussian : ∀ b, frozenMass/2 ≤ b → b ≤ frozenMass →
      I b ≤ -b*gaussianEnergyFloor)
    (μ : ℝ) (hμ : 0 < μ) (hμm : μ < frozenMass) :
    min μ (frozenMass-μ)/3000000 < I μ+I (frozenMass-μ)-I frozenMass := by
  let s := min μ (frozenMass-μ)
  let b := frozenMass-s
  have hs : 0 < s := lt_min hμ (sub_pos.2 hμm)
  have hsm : s < frozenMass := lt_of_le_of_lt (min_le_left _ _) hμm
  have hs2 : s ≤ frozenMass/2 := by
    have h1 : s ≤ μ := min_le_left _ _
    have h2 : s ≤ frozenMass-μ := min_le_right _ _
    linarith
  have hb : 0 < b := sub_pos.2 hsm
  have hbm : b < frozenMass := by dsimp [b]; linarith
  have hhalf : frozenMass/2 ≤ b := by dsimp [b]; linarith
  have hsb : s ≤ b := by dsimp [b]; linarith
  have horder := frozen_per_mass_nonincreasing I inputs s b hs hsb hbm.le
  have span : b+frozenMass < 2*frozenThreshold := by linarith [frozen_below_threshold]
  have scale := infimum_scaling_bound I frozenBeta frozenBeta frozenThreshold b frozenMass
    inputs frozen_threshold_pos hb hbm span
  have gap := quantitative_gap I frozenThreshold b frozenMass frozen_threshold_pos hb hbm span
    (inputs.negative b hb) scale
  let h := 1-(b+frozenMass)/(2*frozenThreshold)
  have hh : gapSlack ≤ h := by
    have hr : (b+frozenMass)/(2*frozenThreshold) ≤ frozenMass/frozenThreshold := by
      apply (div_le_div_iff₀ (mul_pos (by norm_num) frozen_threshold_pos)
        frozen_threshold_pos).2
      nlinarith [frozen_threshold_pos]
    dsimp [h]
    linarith [frozen_slack_floor]
  have hf := gaussian_energy_floor_pos
  have hI : b*gaussianEnergyFloor ≤ -I b := by
    linarith [gaussian b hhalf hbm.le]
  have hr : gaussianEnergyFloor/frozenMass ≤ (-I b)/b^2 := by
    apply (div_le_div_iff₀ frozen_mass_pos (sq_pos_of_pos hb)).2
    have h1 := mul_le_mul_of_nonneg_right hI frozen_mass_pos.le
    have h2 := mul_le_mul_of_nonneg_left hbm.le (mul_nonneg hb.le hf.le)
    nlinarith
  have hpos : 0 ≤ (-I b)/b^2 := div_nonneg (by linarith [inputs.negative b hb]) (sq_nonneg b)
  have lower : uniformGapConstant*s/frozenMass ≤
      (frozenMass-b)*(-I b)/b^2*h := by
    calc
      uniformGapConstant*s/frozenMass =
          (gaussianEnergyFloor/frozenMass)*s*gapSlack := by
            rw [gap_constant_factorization]; ring
      _ ≤ ((-I b)/b^2)*s*gapSlack :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr hs.le) gap_slack_pos.le
      _ ≤ ((-I b)/b^2)*s*h :=
        mul_le_mul_of_nonneg_left hh (mul_nonneg hpos hs.le)
      _ = (frozenMass-b)*(-I b)/b^2*h := by dsimp [b]; ring
  have hgap : uniformGapConstant*s/frozenMass ≤ I b/b-I frozenMass/frozenMass :=
    lower.trans gap.1
  have assembled := split_gap_from_per_mass I frozenMass s uniformGapConstant
    frozen_mass_pos hs hsm horder hgap
  have strict : s/3000000 < uniformGapConstant*s := by
    have ht := mul_lt_mul_of_pos_right uniform_gap_constant_gt hs
    nlinarith
  have sumid : I s+I (frozenMass-s) = I μ+I (frozenMass-μ) := by
    by_cases hc : μ ≤ frozenMass-μ
    · simp [s, min_eq_left hc]
    · have hd : frozenMass-μ ≤ μ := (lt_of_not_ge hc).le
      have he : frozenMass-(frozenMass-μ) = μ := by ring
      simp [s, min_eq_right hd, he, add_comm]
  rw [sumid] at assembled
  exact strict.trans_le assembled

/-- Actual I₂ syntax, with the two remaining analytic inputs in the type. -/
theorem frozen_I2_quantitative_all_splits (data : WholeSpaceData)
    (inputs : BindingSequenceInputs (I2 data 1 frozenBeta frozenBeta)
      frozenBeta frozenBeta frozenThreshold)
    (gaussian : ∀ b, frozenMass/2 ≤ b → b ≤ frozenMass →
      I2 data 1 frozenBeta frozenBeta b ≤ -b*gaussianEnergyFloor)
    (μ : ℝ) (hμ : 0 < μ) (hμm : μ < frozenMass) :
    min μ (frozenMass-μ)/3000000 <
      I2 data 1 frozenBeta frozenBeta μ +
      I2 data 1 frozenBeta frozenBeta (frozenMass-μ) -
      I2 data 1 frozenBeta frozenBeta frozenMass :=
  frozen_quantitative_all_splits _ inputs gaussian μ hμ hμm

/-- Energy splitting is impossible once the quantitative theorem is supplied.
The concentration-compactness theorem producing a split is not assumed proved. -/
theorem frozen_no_energy_dichotomy (I : ℝ → ℝ)
    (inputs : BindingSequenceInputs I frozenBeta frozenBeta frozenThreshold)
    (gaussian : ∀ b, frozenMass/2 ≤ b → b ≤ frozenMass →
      I b ≤ -b*gaussianEnergyFloor)
    (μ : ℝ) (hμ : 0 < μ) (hμm : μ < frozenMass) :
    ¬ (I μ+I (frozenMass-μ) ≤ I frozenMass) := by
  have hg := frozen_quantitative_all_splits I inputs gaussian μ hμ hμm
  have hp : 0 < min μ (frozenMass-μ)/3000000 := by
    exact div_pos (lt_min hμ (sub_pos.2 hμm)) (by norm_num)
  linarith

end
end WCTLean.D4
