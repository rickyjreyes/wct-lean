import WCTLean.Models.CurvatureMultiplicativeLaplacian

/-!
# Sharp absence of uniform regulator removal near nodal complex jets (#22)

The maintained corrected complex curvature has pointwise regulator-removal
limits for every *fixed* nonzero field value. The separately verified
`theta_node_scale_error` computes the exact error on the diagonal
  psi = epsilon > 0, lapPsi = 1, alpha = 0
as 1/(2 epsilon).

This module quantifies the obstruction: in **every** positive regulator
neighborhood, the unregularized-comparison error exceeds **any**
prescribed real bound. Hence no error estimate uniform over all
nonnodal complex jets can hold without additional near-node control.

This is a sharp algebraic jet obstruction, not an actual solution of
the nonlinear WCT PDE and not a proof of failure of dominated
convergence under its separately imposed integrability assumptions.
-/

noncomputable section

namespace WCTLean

/-- Pointwise epsilon -> 0 convergence cannot be uniform in field
amplitude near nodes. For any regulator neighborhood and any bound
there is a nonzero complex jet with lapPsi = 1 and psi = epsilon
whose comparison error exceeds that bound. -/
theorem theta_no_uniform_limit_near_nodes
    (bound delta : ℝ) (hdelta : 0 < delta) :
    ∃ epsilon : ℝ,
      0 < epsilon ∧ epsilon < delta ∧
      bound < ‖thetaComplex 1 (epsilon : ℂ) epsilon 0 -
        (-(1 / (epsilon : ℂ)))‖ := by
  let t : ℝ := |bound| + 1 + 1 / delta
  have hd : 0 < 1 / delta := one_div_pos.mpr hdelta
  have ht : 0 < t := by
    dsimp [t]
    linarith [abs_nonneg bound]
  have htd : 1 / delta < t := by
    dsimp [t]
    linarith [abs_nonneg bound]
  let epsilon : ℝ := 1 / (2 * t)
  have he : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  have hed : epsilon < delta := by
    change 1 / (2 * t) < delta
    apply (div_lt_iff₀ (by positivity : 0 < 2 * t)).mpr
    have h1 : 1 < t * delta := (div_lt_iff₀ hdelta).mp htd
    nlinarith
  have hform : 1 / (2 * epsilon) = t := by
    dsimp [epsilon]
    have htnz : t ≠ 0 := ne_of_gt ht
    field_simp
    <;> ring
  refine ⟨epsilon, he, hed, ?_⟩
  rw [theta_node_scale_error epsilon he, hform]
  dsimp [t]
  linarith [le_abs_self bound]

end WCTLean
