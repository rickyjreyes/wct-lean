import Mathlib

namespace WCT

/-
  Basic foundations for symbolic computation
-/

-- Abstract symbolic bit
inductive Bit : Type
| zero : Bit
| one  : Bit

-- Symbolic tape
abbrev Tape := List Bit

-- Validity predicate
def is_valid_block (b : Tape) : Prop :=
  b.length > 0

-- Nonempty symbolic block
def Block := { b : Tape // is_valid_block b }

-- Abstract vector state
abbrev Vector := List Real

-- Symbolic configuration
structure StateConfig where
  field     : Vector
  reference : Vector

-- Verifier configuration
structure VerifierConfig where
  tau        : Real
  sigma_crit : Real

-- Symbolic evolution operator
abbrev Evolution := StateConfig -> StateConfig

/-- An arbitrary state sequence, not a Turing machine. -/
abbrev StateSequence := Nat → StateConfig

-- Inner product
def dot_product (x y : Vector) : Real :=
  List.foldl (fun a b => a + b) 0 (List.zipWith (fun a b => a * b) x y)

-- Vector norm
noncomputable def norm (v : Vector) : Real :=
  Real.sqrt (dot_product v v)

/-- Checked normalization: undefined inputs are rejected, not mapped to zero. -/
noncomputable def normalized_overlap (a b : Vector) : Option ℝ := by
  classical
  exact if a.length = b.length ∧ 0 < norm a ∧ 0 < norm b then
    some (dot_product a b / (norm a * norm b)) else none

def IsProbabilityVector (p : Vector) : Prop :=
  p ≠ [] ∧ (∀ x ∈ p, 0 ≤ x) ∧ p.sum = 1

def ProbabilityVector := {p : Vector // IsProbabilityVector p}

/-- Shannon entropy on the probability simplex, with the zero-mass convention. -/
noncomputable def entropy (p : ProbabilityVector) : ℝ :=
  - List.foldl (fun a b => a + b) 0
      (p.val.map (fun pi => if pi = 0 then 0 else pi * Real.log pi))

/-- Squared amplitudes, normalized by their total squared mass. Real-valued
symbolic amplitude convention; correspondence to the physical spectral
distribution is a separate obligation. -/
noncomputable def amplitudeProbabilities (v : Vector) : Vector :=
  v.map (fun x => x ^ 2 / (v.map (fun y => y ^ 2)).sum)

/-- Fail closed unless the normalized amplitudes actually define a probability
vector. No theorem about normalization is assumed. -/
noncomputable def amplitudeEntropy (v : Vector) : Option ℝ := by
  classical
  exact if h : IsProbabilityVector (amplitudeProbabilities v) then
    some (entropy ⟨amplitudeProbabilities v, h⟩) else none

/-- Conditional symbolic verifier. Physical threshold calibration and the
spectral interpretation remain OPEN. -/
def passes_verifier (cfg : VerifierConfig) (s : StateConfig) : Prop :=
  0 ≤ cfg.tau ∧ cfg.tau < 1 ∧ 0 ≤ cfg.sigma_crit ∧
    ∃ overlap H : ℝ,
      normalized_overlap s.field s.reference = some overlap ∧
      amplitudeEntropy s.field = some H ∧
      cfg.tau < overlap ∧ H ≤ cfg.sigma_crit

/-- A finite binary description language: unary naturals separated by zero
bits, with one bit contributing one unit of description length. A nonterminated
run is rejected. This is an explicit coding model, not a universal TM. -/
def decodeRuns : Tape → Nat → Option (List Nat)
  | [], k => if k = 0 then some [] else none
  | Bit.one :: bs, k => decodeRuns bs (k + 1)
  | Bit.zero :: bs, k => (decodeRuns bs 0).map (List.cons k)

/-- Each triple encodes sign, numerator, and denominator minus one.
The finite programs describe rational vectors, not arbitrary real vectors.
The denominator is always strictly positive. -/
noncomputable def decodeRationalWords : List Nat → Option Vector
  | [] => some []
  | sign :: num :: den :: rest =>
    if sign ≤ 1 then
      (decodeRationalWords rest).map (fun xs =>
        ((if sign = 0 then (num : ℝ) else -(num : ℝ)) / ((den : ℝ) + 1)) :: xs)
    else none
  | _ => none

noncomputable def decodeDescription (program : Tape) : Option Vector :=
  (decodeRuns program 0).bind decodeRationalWords

/-- Minimum bit length of a successful description, if any. No external
complexity oracle is postulated. None denotes no finite description in
this language. This is description length, not running time or universal
Kolmogorov complexity. -/
noncomputable def literalDescriptionLength (psi : Vector) : Option Nat := by
  classical
  exact if h : ∃ n : Nat, ∃ program : Tape,
    program.length = n ∧ decodeDescription program = some psi
  then some (Nat.find h) else none

/-- Original universal lower-bound obligation, including representability.
This is not asserted: arbitrary real vectors need not be describable,
and the empty vector has a zero-length description in this model. -/
def exponential_bound : Prop :=
  ∀ psi : Vector, ∃ k : Nat, literalDescriptionLength psi = some k ∧ k ≥ 2 ^ psi.length

theorem empty_description_decodes : decodeDescription [] = some [] := by
  simp [decodeDescription, decodeRuns, decodeRationalWords]

theorem K_empty : literalDescriptionLength [] = some 0 := by
  classical
  have h : ∃ n : Nat, ∃ program : Tape,
      program.length = n ∧ decodeDescription program = some ([] : Vector) :=
    ⟨0, [], rfl, empty_description_decodes⟩
  unfold literalDescriptionLength
  rw [dif_pos h]
  have hle : Nat.find h ≤ 0 :=
    Nat.find_le (show ∃ program : Tape,
      program.length = 0 ∧ decodeDescription program = some ([] : Vector) from
      ⟨[], rfl, empty_description_decodes⟩)
  rw [Nat.le_zero.mp hle]

/-- The literal universal statement is false for this explicit model.
The intended nonempty hard-family lower bound requires a separate,
precisely specified machine/resource model and independent proof. -/
theorem exponential_bound_false_in_description_model : ¬ exponential_bound := by
  intro h
  obtain ⟨k, hk, hb⟩ := h []
  rw [K_empty] at hk
  have hz : k = 0 := (Option.some.inj hk).symm
  subst k
  norm_num at hb

/-- Range exclusion only. This is not computational nonconstructibility. -/
def OutsideSequenceRange (M : StateSequence) (psi_star : StateConfig) : Prop :=
  ∀ i : Nat, M i ≠ psi_star

/-- Uniform family resource obligation for an independently specified machine
semantics. This is not a Turing-machine implementation or a lower bound. -/
structure FamilyMachineSemantics where
  Machine : Type
  machine_nonempty : Nonempty Machine
  runs : Machine → List Bit → List Bit → Nat → Prop

def PolynomialFamilyConstructor (S : FamilyMachineSemantics)
    (target : List Bit → List Bit) : Prop :=
  ∃ m : S.Machine, ∃ C k : Nat, 0 < C ∧
    ∀ input : List Bit, ∃ t : Nat,
      t ≤ C * (input.length + 1) ^ k ∧ S.runs m input (target input) t

def UniformNonconstructibilityObligation (S : FamilyMachineSemantics)
    (target : List Bit → List Bit) : Prop :=
  ¬ PolynomialFamilyConstructor S target

end WCT
