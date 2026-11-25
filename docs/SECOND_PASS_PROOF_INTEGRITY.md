# Second-pass adversarial proof integrity remediation

Base evidence: 315f33924e5c20a7c39dd5cd955a3bbc7815d1af. The earlier build failed in FullContractFalsified because Theta_not_baseline lacked its baseline argument. The correction below does not assert any previously unproved mathematical result.

| Finding | Remediation | Remaining obligation |
|---|---|---|
| Missing attractors | Unique existence in positive dimensions up to 3; failure of the full restriction is a falsification alternative | Physical existence/uniqueness OPEN |
| Hardcoded dimensional model | Concrete dimension-indexed Sobolev field and canonical curvature expression; abstract dimension model explicitly diagnostic | Derive original PDE and prove correspondence, not an arbitrary map |
| Singleton admissibility | Distinct nearby admissible states, invariance, Lyapunov stability | Physical admissibility OPEN |
| Unit state | Nontrivial state type required | Continuum realization OPEN |
| Attraction vs stability | Separate Lyapunov and asymptotic stability predicates | Orbital stability OPEN |
| Constant entropy | Strict dissipation stated separately | Physical entropy and applicability of strict dissipation OPEN |
| Empty flow | Nonempty flow and open flow laws | PDE solution flow OPEN |
| Cherry-picked baselines | All real-linear maps explicitly compared | Physical baseline family OPEN |
| Parameter IDs | Concrete positive-regulator curvature parameter structure | Full physical parameterization and evolution OPEN |
| Unconstrained energy | Explicit boundedness and conservation obligations | Physical functional and coercivity OPEN |
| Undefined overlap | Option result with compatible lengths and positive norms | None for domain guard |
| Empty verifier | Fail-closed thresholds and checked overlap and entropy | Physical threshold calibration OPEN |
| Invalid entropy inputs | Probability subtype and checked squared-amplitude distribution | Spectral correspondence OPEN |
| Fake machine | Rename arbitrary sequence; state uniform-family resource obligation | Concrete machine semantics and lower bound OPEN |
| Literal K | Name literalDescriptionLength; preserve counterexample and scope | Universal complexity OPEN |
| Disconnected energy | Whole-space energy tied to common Sobolev derivative graph | Physical functional correspondence OPEN |
| Critical exponent | Natural dimension with proof of d > 2 | Low-dimensional regimes separate |
| Scalar interpolation | Uniform whole-space eLpNorm inequality with constant outside field quantifier | Exponent relation and analytic proof OPEN |
| Negative local energy | Sign/domain guards and uniform localized integral obligation | Original estimate OPEN |
| Zero dilation | Guarded positive-dilation interface; arithmetic identities separately scoped | Actual field scaling law OPEN |
| Stability label | AnalyticSubcriticalCriterion, not a dynamical criterion | Dynamical threshold OPEN |
| Mixed models | One indexed family supplies local state, entropy, energy and map | Actual physical realization OPEN |
| Mutable verification | Independent protected policy required | Repository settings and reviewer separation not changed |
| Lexical limitations | Additional trust-boundary tokens; elaborated axiom check retained | Not a parser, not independent authorization |
| Unlimited budget | Finite registry/audit heartbeats and CI timeout | Exact-head CI required |

The abstract models remain useful only as diagnostic interfaces. No concrete realization of the original WCT time evolution is claimed. Model structures must not be used as proof of the supplied properties. Added regression declarations cover empty overlap, empty verifier states, singleton admissibility and missing attractors.

## Independent verification requirements

The candidate branch cannot certify its own verification policy. A reviewer-controlled protected workflow should obtain its scanner, module inventory generator, Lean audit template and axiom allowlist from an independently reviewed immutable revision. Review changes to the original mathematical statement separately from implementation changes. Require exact-head CI and independent approval before merging, including any changes to audit tooling or build configuration. This document does not install those protections or authorize a waiver.

All new definitions and regression statements are subject to exact-head CI. No new physical obligation is promoted to PROVED.
