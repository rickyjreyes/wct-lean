import Mathlib
import WCTLean.Koide

namespace WCTLean

def curvatureHarmonicSq (spin : ℝ) : ℝ := 2 * spin / (2 * spin + 1)

def spinKoide (spin : ℝ) : ℝ := (2 * spin + 1) / (6 * spin)

theorem spinKoide_identity (spin : ℝ) (hs : spin ≠ 0) :
    3 * spinKoide spin - 1 = 1 / (2 * spin) := by
  unfold spinKoide
  field_simp [hs]
  ring

theorem spinKoide_half : spinKoide (1 / 2 : ℝ) = 2 / 3 := by
  norm_num [spinKoide]

def geometricKoide (cosThetaSq : ℝ) : ℝ := 1 / (3 * cosThetaSq)

theorem geometricKoide_of_curvature_harmonic
    (spin : ℝ) (hs : spin ≠ 0) (hden : 2 * spin + 1 ≠ 0) :
    geometricKoide (curvatureHarmonicSq spin) = spinKoide spin := by
  unfold geometricKoide curvatureHarmonicSq spinKoide
  field_simp [hs, hden]
  ring

end WCTLean
