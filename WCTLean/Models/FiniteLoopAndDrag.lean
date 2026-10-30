import Mathlib
import WCTLean.Models.NarrowCanonicalCoverage

namespace WCTLean

/-!
# Narrow canonical proofs: TOP1 and CM10

TOP1: exact closure of the supplied finite trigonometric representation.
CM10: ratio-domain and convex interpolation consequences for a declared
baryon/photon drag step.

No knot or topology emergence, acoustic oscillator solution, derivation
of physical exchange energies, or empirical cosmological fit is implied.
-/

/-- TOP1: finite real trigonometric loop with the canonical positive
integer harmonics 1,...,K. -/
noncomputable def top1FiniteSpectralLoop (K : ℕ)
    (a b : Fin K → ℝ) (s : ℝ) : ℝ :=
  ∑ k : Fin K, cle7_angular_mode (a k) (b k) (k.val + 1) s

/-- TOP1: the finite Fourier representation is exactly 2π-periodic. -/
theorem top1FiniteSpectralLoop_periodic
    (K : ℕ) (a b : Fin K → ℝ) (s : ℝ) :
    top1FiniteSpectralLoop K a b (s + 2 * Real.pi) =
      top1FiniteSpectralLoop K a b s := by
  simp only [top1FiniteSpectralLoop, cle7_angular_mode_periodic]

/-- TOP1: as a consequence, the parametrized real loop closes at its
specified endpoints. This is a periodic representation, not a claim
about smooth embedded knots or their dynamics. -/
theorem top1FiniteSpectralLoop_closes
    (K : ℕ) (a b : Fin K → ℝ) :
    top1FiniteSpectralLoop K a b (2 * Real.pi) =
      top1FiniteSpectralLoop K a b 0 := by
  simpa only [zero_add] using
    top1FiniteSpectralLoop_periodic K a b 0

/-- CM10: the formal energy-exchange-to-compression ratio. -/
noncomputable def cm10DragRatio (exchange compression : ℝ) : ℝ :=
  exchange / compression

/-- CM10: supplied nonnegative exchange no larger than positive
compression implies a coupling coefficient between zero and one. -/
theorem cm10DragRatio_mem_unitInterval
    (exchange compression : ℝ)
    (hexchange : 0 ≤ exchange)
    (hcompression : 0 < compression)
    (hbound : exchange ≤ compression) :
    0 ≤ cm10DragRatio exchange compression ∧
      cm10DragRatio exchange compression ≤ 1 := by
  unfold cm10DragRatio
  constructor
  · exact div_nonneg hexchange (le_of_lt hcompression)
  · exact (div_le_one hcompression).mpr hbound

/-- CM10: the photon/baryon drag update from the canonical registry. -/
def cm10DragUpdate (epsilon baryon photon : ℝ) : ℝ :=
  (1 - epsilon) * baryon + epsilon * photon

/-- CM10: one drag step shrinks the signed mismatch by precisely
the declared retention factor. -/
theorem cm10DragUpdate_mismatch (epsilon baryon photon : ℝ) :
    cm10DragUpdate epsilon baryon photon - photon =
      (1 - epsilon) * (baryon - photon) := by
  unfold cm10DragUpdate
  ring

/-- CM10: when the coupling is between 0 and 1 and the baryon input
is below the photon input, the update lies in the interval. -/
theorem cm10DragUpdate_between
    (epsilon baryon photon : ℝ)
    (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1)
    (horder : baryon ≤ photon) :
    baryon ≤ cm10DragUpdate epsilon baryon photon ∧
      cm10DragUpdate epsilon baryon photon ≤ photon := by
  unfold cm10DragUpdate
  constructor
  · nlinarith [mul_nonneg hzero (sub_nonneg.mpr horder)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hone) (sub_nonneg.mpr horder)]

end WCTLean
