import Mathlib
import WCTLean.Models.S004SpacetimeFubini
import WCTLean.Models.S004IntervalGreen

/-!
# Two-dimensional continuum Green identities, with proved Fubini interchange

The earlier S004 interval Green identities only integrated in one
variable. Here the actual t,x spacetime rectangle is integrated as a
two-dimensional iterated Lebesgue interval integral.

For temporal integration by parts the proof first invokes the real
product-measure Fubini theorem, applies the proved 1D FTC-based Green
identities for EVERY spatial slice, and swaps integration back.

For spatial derivatives the one-dimensional periodic Green identity is
applied to EVERY time slice before time integration. There is no
assumption of the desired two-dimensional adjoint formula.

Precisely required assumptions:
- genuine classical 1st/2nd partial derivatives of coefficients and tests
  on the respective closed interval slices,
- their interval integrability on every slice,
- compact temporal test traces or periodic spatial traces, and
- real product-measure integrability of the two temporal integrands
  where Fubini is required.

These are real continuum identities, not discrete grids. They do not
yet derive Sobolev admissibility of every nonlinear S004 coefficient,
nor assert a final nonlinear Euler–Lagrange equation.
-/

open MeasureTheory Set
open scoped Interval

namespace WCTLean.S004SpacetimeGreen

open WCTLean.S004IntervalGreen
open WCTLean.S004SpacetimeFubini

/-- Actual spacetime first-order temporal Green identity:
∫∫ u * ∂t v = - ∫∫ (∂t u) * v,
with the test variation vanishing at temporal endpoints.
Proof uses real interval FTC and Fubini from product integrability. -/
theorem temporal_first_spacetime
    (a b c d : ℝ) (hcd : c ≤ d) (u u1 v v1 : ℝ → ℝ → ℝ)
    (hu : ∀ x t, t ∈ [[a,b]] →
      HasDerivAt (fun s => u s x) (u1 t x) t)
    (hv : ∀ x t, t ∈ [[a,b]] →
      HasDerivAt (fun s => v s x) (v1 t x) t)
    (huInt : ∀ x, IntervalIntegrable (fun t => u1 t x) volume a b)
    (hvInt : ∀ x, IntervalIntegrable (fun t => v1 t x) volume a b)
    (hva : ∀ x, v a x = 0) (hvb : ∀ x, v b x = 0)
    (hf : IntegrableOn
      (Function.uncurry (fun t x => u t x * v1 t x))
      (uIoc a b ×ˢ uIoc c d))
    (hg : IntegrableOn
      (Function.uncurry (fun t x => u1 t x * v t x))
      (uIoc a b ×ˢ uIoc c d)) :
    (∫ t in a..b, ∫ x in c..d, u t x * v1 t x) =
      -(∫ t in a..b, ∫ x in c..d, u1 t x * v t x) := by
  have hl := rectangle_integral_swap a b c d
    (fun t x => u t x * v1 t x) hcd hf
  have hr := rectangle_integral_swap a b c d
    (fun t x => u1 t x * v t x) hcd hg
  calc
    (∫ t in a..b, ∫ x in c..d, u t x * v1 t x) =
      (∫ x in c..d, ∫ t in a..b, u t x * v1 t x) := hl
    _ = ∫ x in c..d, -(∫ t in a..b, u1 t x * v t x) := by
      congr 1
      funext x
      exact integral_mul_first_deriv_eq_neg a b
        (fun t => u t x) (fun t => u1 t x)
        (fun t => v t x) (fun t => v1 t x)
        (hu x) (hv x) (huInt x) (hvInt x) (hva x) (hvb x)
    _ = -(∫ x in c..d, ∫ t in a..b, u1 t x * v t x) := by
      rw [intervalIntegral.integral_neg]
    _ = -(∫ t in a..b, ∫ x in c..d, u1 t x * v t x) := by rw [hr]

/-- Actual spacetime SECOND temporal Green identity:
∫∫ u * ∂tt v = ∫∫ (∂tt u) * v. Both 0th and 1st
temporal traces of the test variation must vanish. -/
theorem temporal_second_spacetime
    (a b c d : ℝ) (hcd : c ≤ d)
    (u u1 u2 v v1 v2 : ℝ → ℝ → ℝ)
    (hu : ∀ x t, t ∈ [[a,b]] →
      HasDerivAt (fun s => u s x) (u1 t x) t)
    (hu1 : ∀ x t, t ∈ [[a,b]] →
      HasDerivAt (fun s => u1 s x) (u2 t x) t)
    (hv : ∀ x t, t ∈ [[a,b]] →
      HasDerivAt (fun s => v s x) (v1 t x) t)
    (hv1 : ∀ x t, t ∈ [[a,b]] →
      HasDerivAt (fun s => v1 s x) (v2 t x) t)
    (hu1Int : ∀ x, IntervalIntegrable (fun t => u1 t x) volume a b)
    (hu2Int : ∀ x, IntervalIntegrable (fun t => u2 t x) volume a b)
    (hv1Int : ∀ x, IntervalIntegrable (fun t => v1 t x) volume a b)
    (hv2Int : ∀ x, IntervalIntegrable (fun t => v2 t x) volume a b)
    (hva : ∀ x, v a x = 0) (hvb : ∀ x, v b x = 0)
    (hv1a : ∀ x, v1 a x = 0) (hv1b : ∀ x, v1 b x = 0)
    (hf : IntegrableOn
      (Function.uncurry (fun t x => u t x * v2 t x))
      (uIoc a b ×ˢ uIoc c d))
    (hg : IntegrableOn
      (Function.uncurry (fun t x => u2 t x * v t x))
      (uIoc a b ×ˢ uIoc c d)) :
    (∫ t in a..b, ∫ x in c..d, u t x * v2 t x) =
      (∫ t in a..b, ∫ x in c..d, u2 t x * v t x) := by
  have hl := rectangle_integral_swap a b c d
    (fun t x => u t x * v2 t x) hcd hf
  have hr := rectangle_integral_swap a b c d
    (fun t x => u2 t x * v t x) hcd hg
  calc
    (∫ t in a..b, ∫ x in c..d, u t x * v2 t x) =
      (∫ x in c..d, ∫ t in a..b, u t x * v2 t x) := hl
    _ = (∫ x in c..d, ∫ t in a..b, u2 t x * v t x) := by
      congr 1
      funext x
      exact integral_mul_second_deriv_eq a b
        (fun t => u t x) (fun t => u1 t x) (fun t => u2 t x)
        (fun t => v t x) (fun t => v1 t x) (fun t => v2 t x)
        (hu x) (hu1 x) (hv x) (hv1 x)
        (hu1Int x) (hu2Int x) (hv1Int x) (hv2Int x)
        (hva x) (hvb x) (hv1a x) (hv1b x)
    _ = (∫ t in a..b, ∫ x in c..d, u2 t x * v t x) := hr.symm

/-- Exact periodic spatial FIRST derivative Green identity over the
whole 1+1 spacetime rectangle. Here spatial IBP is performed on each
time slice so Fubini is not needed to establish the stated order. -/
theorem spatial_first_spacetime
    (a b c d : ℝ) (u u1 v v1 : ℝ → ℝ → ℝ)
    (hu : ∀ t x, x ∈ [[c,d]] →
      HasDerivAt (fun y => u t y) (u1 t x) x)
    (hv : ∀ t x, x ∈ [[c,d]] →
      HasDerivAt (fun y => v t y) (v1 t x) x)
    (huInt : ∀ t, IntervalIntegrable (fun x => u1 t x) volume c d)
    (hvInt : ∀ t, IntervalIntegrable (fun x => v1 t x) volume c d)
    (huPer : ∀ t, u t d = u t c)
    (hvPer : ∀ t, v t d = v t c) :
    (∫ t in a..b, ∫ x in c..d, u t x * v1 t x) =
      -(∫ t in a..b, ∫ x in c..d, u1 t x * v t x) := by
  calc
    (∫ t in a..b, ∫ x in c..d, u t x * v1 t x) =
        (∫ t in a..b, -(∫ x in c..d, u1 t x * v t x)) := by
      congr 1
      funext t
      exact integral_mul_first_deriv_periodic c d
        (fun x => u t x) (fun x => u1 t x)
        (fun x => v t x) (fun x => v1 t x)
        (hu t) (hv t) (huInt t) (hvInt t)
        (huPer t) (hvPer t)
    _ = -(∫ t in a..b, ∫ x in c..d, u1 t x * v t x) := by
      rw [intervalIntegral.integral_neg]

/-- Exact periodic spatial SECOND derivative Green identity over
the whole continuum spacetime rectangle, not a one-dimensional
surrogate or a bilinear abstract adjoint assumption. -/
theorem spatial_second_spacetime
    (a b c d : ℝ)
    (u u1 u2 v v1 v2 : ℝ → ℝ → ℝ)
    (hu : ∀ t x, x ∈ [[c,d]] →
      HasDerivAt (fun y => u t y) (u1 t x) x)
    (hu1 : ∀ t x, x ∈ [[c,d]] →
      HasDerivAt (fun y => u1 t y) (u2 t x) x)
    (hv : ∀ t x, x ∈ [[c,d]] →
      HasDerivAt (fun y => v t y) (v1 t x) x)
    (hv1 : ∀ t x, x ∈ [[c,d]] →
      HasDerivAt (fun y => v1 t y) (v2 t x) x)
    (hu1Int : ∀ t, IntervalIntegrable (fun x => u1 t x) volume c d)
    (hu2Int : ∀ t, IntervalIntegrable (fun x => u2 t x) volume c d)
    (hv1Int : ∀ t, IntervalIntegrable (fun x => v1 t x) volume c d)
    (hv2Int : ∀ t, IntervalIntegrable (fun x => v2 t x) volume c d)
    (huPer : ∀ t, u t d = u t c)
    (hu1Per : ∀ t, u1 t d = u1 t c)
    (hvPer : ∀ t, v t d = v t c)
    (hv1Per : ∀ t, v1 t d = v1 t c) :
    (∫ t in a..b, ∫ x in c..d, u t x * v2 t x) =
      (∫ t in a..b, ∫ x in c..d, u2 t x * v t x) := by
  congr 1
  funext t
  exact integral_mul_second_deriv_periodic c d
    (fun x => u t x) (fun x => u1 t x) (fun x => u2 t x)
    (fun x => v t x) (fun x => v1 t x) (fun x => v2 t x)
    (hu t) (hu1 t) (hv t) (hv1 t)
    (hu1Int t) (hu2Int t) (hv1Int t) (hv2Int t)
    (huPer t) (hu1Per t) (hvPer t) (hv1Per t)

end WCTLean.S004SpacetimeGreen
