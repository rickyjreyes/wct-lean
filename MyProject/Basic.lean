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

/-- A finite-description decoder. Only vectors in its image are representable.
No universality or computability property is asserted for this decoder. -/
abbrev DescriptionDecoder := Tape → Option Vector

def DescriptionLengthAtMost (decode : DescriptionDecoder) (psi : Vector) (k : ℕ) : Prop :=
  ∃ code : Tape, decode code = some psi ∧ code.length ≤ k

/-- Open, decoder-relative lower-bound claim for a representable vector.
The representability conjunct prevents a vacuous lower bound.
This is not an assertion about universal Kolmogorov complexity. -/
def ExponentialDescriptionLowerBound (decode : DescriptionDecoder) (psi : Vector) : Prop :=
  (∃ code : Tape, decode code = some psi) ∧
  ∀ code : Tape, decode code = some psi → 2 ^ psi.length ≤ code.length

/-- Unreachability in the specified enumeration, not a complexity lower bound. -/
def NonConstructible (M : Nat → StateConfig) (psi_star : StateConfig) : Prop :=
  ∀ i : Nat, M i ≠ psi_star

end WCT
