import WCTLean.Models.CurvatureNodalObstruction

/-!
# PDE-structured dominated-convergence corollaries for corrected M2/E17 (#22)

Unlike the existing curvature dominated-convergence results, these theorems
do not independently assume that the totalized unregularized quotient
lapPsi/psi lies in Lp. Instead, the explicitly supplied structural
identity lapPsi = V * psi and integrable bounds on V deliver the pointwise
majorant. This includes arbitrary measurable nodal sets.

The relation is an *assumption*: no theorem derives it for all solutions
of the fourth-order WCT evolution. Neither this file nor the parent
theorems proves weak-PDE compactness, WCT confinement or passage through
a nonlinear PDE limit. The integrability of the potential norm and its
square are stated as explicit hypotheses for the relevant integrals.
-/

noncomputable section

namespace WCTLean
open MeasureTheory Filter Topology
open scoped ENNReal

/-- The corrected complex curvature integrals converge under the
supplied multiplicative-Laplacian relation and an L1 potential bound,
without a separate MemLp hypothesis on the quotient. At field zeros
the quotient is Lean's totalized zero division. -/
theorem curvature_integral_limit_of_multiplicative_laplacian
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (psi V : X → ℂ) (alpha : ℝ)
    (hmpsi : AEStronglyMeasurable psi mu)
    (hV : MemLp V 1 mu)
    (hVnorm : Integrable (fun x => ‖V x‖) mu) :
    Tendsto (fun epsilon : ℝ =>
      ∫ x, thetaComplex (V x * psi x) (psi x) epsilon alpha ∂mu)
      (nhds 0)
      (nhds (∫ x, -((V x * psi x) / psi x) ∂mu)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun x => ‖V x‖)
  · exact Filter.Eventually.of_forall (fun epsilon =>
      (theta_multiplicative_laplacian_memLp mu 1 psi V epsilon alpha
        hmpsi hV).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall (fun epsilon =>
      Filter.Eventually.of_forall (fun x =>
        (theta_no_gap_domination (V x * psi x) (psi x)
          epsilon alpha).trans
            (multiplicative_laplacian_quotient_bound (V x) (psi x))))
  · exact hVnorm
  · apply Filter.Eventually.of_forall
    intro x
    by_cases hx : psi x = 0
    · simp [hx, thetaComplex_field_node]
    · exact thetaComplex_nonzero_limit (V x * psi x) (psi x) alpha hx

/-- The squared curvature density has a convergent integral if V has
a square-integrable potential bound. The complete WCT Hamiltonian and
the nonlinear field equations are not involved. -/
theorem curvature_energy_integral_limit_of_multiplicative_laplacian
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (psi V : X → ℂ) (alpha : ℝ)
    (hmpsi : AEStronglyMeasurable psi mu)
    (hV : MemLp V 2 mu)
    (hVnormSq : Integrable (fun x => ‖V x‖ ^ 2) mu) :
    Tendsto (fun epsilon : ℝ =>
      ∫ x, ‖thetaComplex (V x * psi x) (psi x) epsilon alpha‖ ^ 2 ∂mu)
      (nhds 0)
      (nhds (∫ x, ‖(V x * psi x) / psi x‖ ^ 2 ∂mu)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun x => ‖V x‖ ^ 2)
  · apply Filter.Eventually.of_forall
    intro epsilon
    have hmeas :=
      (theta_multiplicative_laplacian_memLp mu 2 psi V epsilon alpha
        hmpsi hV).aestronglyMeasurable
    have hc : Continuous (fun z : ℂ => (‖z‖ ^ 2 : ℝ)) := by fun_prop
    exact hc.comp_aestronglyMeasurable hmeas
  · apply Filter.Eventually.of_forall
    intro epsilon
    apply Filter.Eventually.of_forall
    intro x
    have hs : 0 ≤
        (‖thetaComplex (V x * psi x) (psi x) epsilon alpha‖ ^ 2 : ℝ) :=
      sq_nonneg _
    have habs : |‖thetaComplex (V x * psi x) (psi x)
        epsilon alpha‖ ^ 2| =
        ‖thetaComplex (V x * psi x) (psi x) epsilon alpha‖ ^ 2 :=
      abs_of_nonneg hs
    rw [Real.norm_eq_abs, habs]
    exact theta_multiplicative_laplacian_energy_bound (V x) (psi x)
      epsilon alpha
  · exact hVnormSq
  · apply Filter.Eventually.of_forall
    intro x
    have htheta : Tendsto (fun epsilon : ℝ =>
        thetaComplex (V x * psi x) (psi x) epsilon alpha)
        (nhds 0) (nhds (-((V x * psi x) / psi x))) := by
      by_cases hx : psi x = 0
      · simp [hx, thetaComplex_field_node]
      · exact thetaComplex_nonzero_limit (V x * psi x) (psi x) alpha hx
    have hc : Continuous (fun z : ℂ => (‖z‖ ^ 2 : ℝ)) := by fun_prop
    simpa only [norm_neg] using (hc.continuousAt.tendsto.comp htheta)

end WCTLean
