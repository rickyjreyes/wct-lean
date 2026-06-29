/-
  WCTLean/Main.lean

  Root import for the WCT Lean foundation, canonical registry, model
  definitions, and resolved equation audit.
-/

import WCTLean.Registry
import WCTLean.Dimension
import WCTLean.Curvature
import WCTLean.Energy
import WCTLean.Koide
import WCTLean.Fourier
import WCTLean.Contracts.Analytic
import WCTLean.Models.CurvatureOperator
import WCTLean.Models.ComplexCurvature
import WCTLean.Models.PhaseFlux
import WCTLean.Models.RestDensity
import WCTLean.Models.Locking
import WCTLean.Models.BandPass
import WCTLean.Models.AlgebraicChecks
import WCTLean.Models.LogFlow
import WCTLean.Models.GhostModes
import WCTLean.Models.Collider
import WCTLean.Models.KoideDerivation
import WCTLean.Models.UnifiedOperator
import WCTLean.Models.CompactDynamics
import WCTLean.ResolvedAudit
import WCTLean.DerivedAudit

namespace WCTLean

/-- A bundled smoke test that references the dimensional mass lemma. -/
theorem wctlean_smoke :
    mulDim (divDim actionDim velocityDim) inverseLengthDim = massDim :=
  hbar_div_c_mul_k_is_mass

/-- The public root includes the complete 142-object canonical registry. -/
theorem wctlean_registry_smoke : canonicalRegistry.length = 142 :=
  canonicalRegistry_length

end WCTLean
