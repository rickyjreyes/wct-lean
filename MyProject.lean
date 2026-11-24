import MyProject.Basic
import MyProject.Theta.Definitions
import MyProject.Theta.Entropy
import MyProject.Theta.Dynamics
import MyProject.Theta.Baselines
import MyProject.LeanTests.Sanity
import MyProject.LeanTests.EntropyMonotone
import MyProject.LeanTests.Attractor
import MyProject.LeanTests.DimensionFailure
import MyProject.Falsification

namespace WCT

/-- The historical fixed-point contract is now an open proposition, not a postulate.
It must be established for a specific model. -/
def LegacyFixedPointContractNotFalsified (M : ThetaModel) : Prop := ¬ LegacyFixedPointContractFalsified M

/-- The falsification contract follows conditionally from the separately
stated monotonicity and uniqueness obligations. No physical instance or
unconditional consistency or dynamical attraction result is claimed. -/
theorem legacy_fixedPoint_contract_valid_of (M : ThetaModel)
    (hEntropy : Theta_entropy_monotone M) (hUnique : fixedPoint_unique M) :
    ¬ LegacyFixedPointContractFalsified M := by
  intro hf
  rcases hf with ⟨p, hbad⟩ | ⟨p, s1, s2, hne, h1, h2⟩
  · exact hbad (hEntropy p)
  · exact hne (hUnique p s1 s2 h1 h2)

end WCT
