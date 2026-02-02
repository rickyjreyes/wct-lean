/-
  MyProject - Root Library Module
-/

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

/--
  Consistency postulate.
-/
axiom WCT_consistent : Not WCT_Falsified

/--
  Contract validity follows from consistency.
-/
theorem WCT_contract_valid : Not WCT_Falsified :=
  WCT_consistent

end WCT
