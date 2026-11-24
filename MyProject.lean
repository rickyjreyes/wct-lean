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

end WCT
