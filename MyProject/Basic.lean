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

-- Deterministic symbolic machine
abbrev TuringMachine := Nat -> StateConfig

-- Inner product
def dot_product (x y : Vector) : Real :=
  List.foldl (fun a b => a + b) 0 (List.zipWith (fun a b => a * b) x y)

-- Vector norm
noncomputable def norm (v : Vector) : Real :=
  Real.sqrt (dot_product v v)

-- Normalized overlap
noncomputable def normalized_overlap (a b : Vector) : Real :=
  dot_product a b / (norm a * norm b)

-- Shannon entropy
noncomputable def entropy (p : Vector) : Real :=
  - List.foldl (fun a b => a + b) 0
      (p.map (fun pi =>
        if pi = 0 then 0 else pi * Real.log pi))

-- Verifier acceptance
def passes_verifier (cfg : VerifierConfig) (s : StateConfig) : Prop :=
  normalized_overlap s.field s.reference > cfg.tau
  /\ entropy s.field <= cfg.sigma_crit

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
noncomputable def K (psi : Vector) : Option Nat := by
  classical
  exact if h : ∃ n : Nat, ∃ program : Tape,
    program.length = n ∧ decodeDescription program = some psi
  then some (Nat.find h) else none

/-- Original universal lower-bound obligation, including representability.
This is not asserted: arbitrary real vectors need not be describable,
and the empty vector has a zero-length description in this model. -/
def exponential_bound : Prop :=
  ∀ psi : Vector, ∃ k : Nat, K psi = some k ∧ k ≥ 2 ^ psi.length

theorem empty_description_decodes : decodeDescription [] = some [] := by
  simp [decodeDescription, decodeRuns, decodeRationalWords]

theorem K_empty : K [] = some 0 := by
  classical
  have h : ∃ n : Nat, ∃ program : Tape,
      program.length = n ∧ decodeDescription program = some ([] : Vector) :=
    ⟨0, [], rfl, empty_description_decodes⟩
  unfold K
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

-- Nonconstructibility
def NonConstructible (M : Nat -> StateConfig) (psi_star : StateConfig) : Prop :=
  ∀ i : Nat, M i ≠ psi_star

end WCT
