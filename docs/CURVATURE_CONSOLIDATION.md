# Consolidated curvature and M6B research

This draft consolidates PRs #55, #56, #43 and #29 on top of the proof-integrity remediation in #58. Original commits are retained as parents of the integration commit. No theorem is promoted to verified status until the current full build and transitive axiom audit pass.

- #55: conditional measure-space dominated convergence and Lp convergence of the corrected complex curvature; the multiplicative-Laplacian relation is supplied, not derived from arbitrary PDE solutions.
- #56: explicit admissibility, nonuniqueness, common nonnodal limit and global phase invariance of the regularizer family. The intensity-one anchor selects the canonical member only within that family; the WCT action does not derive the anchor.
- #43: quantitative nonnodal reciprocal and field error bounds.
- #29: algebraic oscillatory noncoercivity witness; periodic integral identities remain analytic, not kernel checked.

Issues #22 and #26 remain open. Preserve the strict source inventory, registry statement lock, complete transitive axiom audit and both library/executable builds from main.
