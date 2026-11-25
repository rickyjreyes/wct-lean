import MyProject.Basic
import MyProject.Falsification

namespace WCT

theorem empty_overlap_rejected : normalized_overlap [] [] = none := by
  simp [normalized_overlap, norm, dot_product]

theorem empty_state_rejected (cfg : VerifierConfig) :
    ¬ passes_verifier cfg ⟨[], []⟩ := by
  intro h
  obtain ⟨_, _, _, overlap, _, hOverlap, _, _, _⟩ := h
  rw [empty_overlap_rejected] at hOverlap
  cases hOverlap

theorem singleton_admissibility_has_no_perturbations
    {X : Type} [MetricSpace X] (s : X) :
    ¬ HasNearbyPerturbations (fun x : X => x = s) s := by
  intro h
  obtain ⟨x, hx, hne, _⟩ := h 1 (by norm_num)
  exact hne hx

end WCT
