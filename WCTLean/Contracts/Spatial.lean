import Mathlib

namespace WCTLean

/-!
# Explicit spatial and boundary interfaces (issue #18)

These are concrete Cartesian domains and field types that downstream PDE
statements can share. They do not silently assert an H² embedding, a trace
theorem, compactness, or an integration-by-parts identity. A general manifold
cannot be represented merely by labelling a Cartesian set "manifold".
-/

abbrev CartesianPoint (n : ℕ) := Fin n → ℝ
abbrev SpatialComplexField (n : ℕ) := CartesianPoint n → ℂ

/-- A region of Euclidean n-space with an explicit boundary set. The caller
must justify that the supplied boundary is contained in its topological
closure; equality with the actual topological boundary is not assumed. -/
structure CartesianDomain (n : ℕ) where
  region : Set (CartesianPoint n)
  boundary : Set (CartesianPoint n)
  boundary_in_closure : boundary ⊆ closure region

/-- The free-space case has no artificial box boundary. -/
def freeSpaceDomain (n : ℕ) : CartesianDomain n where
  region := Set.univ
  boundary := ∅
  boundary_in_closure := by simp

@[simp] theorem freeSpaceDomain_region (n : ℕ) :
    (freeSpaceDomain n).region = Set.univ := rfl

@[simp] theorem freeSpaceDomain_boundary (n : ℕ) :
    (freeSpaceDomain n).boundary = ∅ := rfl

/-- Explicit homogeneous Dirichlet data on a supplied boundary set.
This is pointwise zero trace data; Sobolev trace existence is a separate
continuum obligation. -/
def DirichletZero {n : ℕ} (boundary : Set (CartesianPoint n))
    (psi : SpatialComplexField n) : Prop :=
  ∀ x ∈ boundary, psi x = 0

/-- A Cartesian representation of componentwise periodic boundary data;
the quotient-torus/H² construction is a separate theorem target. -/
def ComponentwisePeriodic {n : ℕ} (period : Fin n → ℝ)
    (psi : SpatialComplexField n) : Prop :=
  ∀ x i, psi (Function.update x i (x i + period i)) = psi x

/-- Free space does not impose a spurious zero trace on a finite box. -/
theorem freeSpace_dirichlet_vacuous {n : ℕ} (psi : SpatialComplexField n) :
    DirichletZero (freeSpaceDomain n).boundary psi := by
  intro x hx
  simp at hx

/-- Homogeneous Dirichlet data are closed under sums of fields. -/
theorem dirichletZero_add {n : ℕ} (boundary : Set (CartesianPoint n))
    (psi phi : SpatialComplexField n)
    (hpsi : DirichletZero boundary psi)
    (hphi : DirichletZero boundary phi) :
    DirichletZero boundary (psi + phi) := by
  intro x hx
  simp [Pi.add_apply, hpsi x hx, hphi x hx]

/-- The selected componentwise periodic sector is closed under sums. -/
theorem componentwisePeriodic_add {n : ℕ} (period : Fin n → ℝ)
    (psi phi : SpatialComplexField n)
    (hpsi : ComponentwisePeriodic period psi)
    (hphi : ComponentwisePeriodic period phi) :
    ComponentwisePeriodic period (psi + phi) := by
  intro x i
  simp only [Pi.add_apply]
  rw [hpsi x i, hphi x i]

end WCTLean
