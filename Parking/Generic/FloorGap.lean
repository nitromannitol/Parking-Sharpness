/-
A one-line real-arithmetic fact about `Nat.floor`: `⌊a+b⌋₊ ≤ ⌊a⌋₊ + ⌊b⌋₊ + 1` for nonnegative
reals, and its consequence for a two-scale floor: `⌊⌊R²⌋₊·s⌋₊` and `⌊s·R²⌋₊` differ by at most
`⌊s⌋₊ + 1`, uniformly in `R`.  Both statements are about arbitrary nonnegative reals
`a, b, s, R` and mention no object specific to this paper.

Used by `Parking.Support.SpatialStopValueConv` to close the floor-rounding gap between two
horizons: `Parking.spatialStopValueCutoff` reads `Parking.External.SpatialStoppingStability` at
horizon `⌊⌊R²⌋₊·s⌋₊` (the instantiation `n := ⌊R²⌋₊`, `T := s`), while `Parking.barDivisible`
(`Parking/Support/Continuum.lean`) reads the discrete odometer at horizon `⌊s·R²⌋₊`; the two
horizons agree up to this uniformly-bounded step count, not exactly.
-/
import Mathlib

noncomputable section
namespace Parking.Generic.FloorGap

/-- **The floor of a sum is at most the sum of the floors, plus one.**  For nonnegative
reals `a, b`: `⌊a+b⌋₊ ≤ ⌊a⌋₊ + ⌊b⌋₊ + 1`. -/
theorem floor_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ⌊a + b⌋₊ ≤ ⌊a⌋₊ + ⌊b⌋₊ + 1 := by
  have hab : 0 ≤ a + b := by linarith
  rw [← Nat.lt_succ_iff, Nat.floor_lt hab]
  push_cast
  have h1 := Nat.lt_floor_add_one a
  have h2 := Nat.lt_floor_add_one b
  linarith

/-- **`⌊⌊R²⌋₊·s⌋₊ ≤ ⌊s·R²⌋₊`**, for `s > 0`: `⌊R²⌋₊ ≤ R²`, and `Nat.floor` is monotone. -/
theorem natFloor_horizon_le (s R : ℝ) (hs : 0 < s) :
    ⌊(⌊R ^ 2⌋₊ : ℝ) * s⌋₊ ≤ ⌊s * R ^ 2⌋₊ := by
  have hR2 : (0 : ℝ) ≤ R ^ 2 := by positivity
  have h1 : (⌊R ^ 2⌋₊ : ℝ) ≤ R ^ 2 := Nat.floor_le hR2
  have h2 : (⌊R ^ 2⌋₊ : ℝ) * s ≤ s * R ^ 2 := by nlinarith [hs.le]
  exact Nat.floor_mono h2

/-- **`⌊s·R²⌋₊ ≤ ⌊⌊R²⌋₊·s⌋₊ + ⌊s⌋₊ + 1`**, for `s > 0`: `R² < ⌊R²⌋₊ + 1`, so
`s·R² < ⌊R²⌋₊·s + s`, and `floor_add_le` bounds the extra `+ s`. -/
theorem natFloor_sq_mul_le_natFloor_horizon_add (s R : ℝ) (hs : 0 < s) :
    ⌊s * R ^ 2⌋₊ ≤ ⌊(⌊R ^ 2⌋₊ : ℝ) * s⌋₊ + ⌊s⌋₊ + 1 := by
  have h1 : R ^ 2 < (⌊R ^ 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (R ^ 2)
  have h2 : s * R ^ 2 < s * ((⌊R ^ 2⌋₊ : ℝ) + 1) := by nlinarith [hs]
  have h3 : s * ((⌊R ^ 2⌋₊ : ℝ) + 1) = (⌊R ^ 2⌋₊ : ℝ) * s + s := by ring
  rw [h3] at h2
  have h4 : ⌊s * R ^ 2⌋₊ ≤ ⌊(⌊R ^ 2⌋₊ : ℝ) * s + s⌋₊ := Nat.floor_mono h2.le
  have h5 : ⌊(⌊R ^ 2⌋₊ : ℝ) * s + s⌋₊ ≤ ⌊(⌊R ^ 2⌋₊ : ℝ) * s⌋₊ + ⌊s⌋₊ + 1 :=
    floor_add_le _ _ (by positivity) hs.le
  omega

/-- **The floor-rounding gap, an `O(1)`-step bound.**  `⌊s·R²⌋₊` and `⌊⌊R²⌋₊·s⌋₊`
differ by at most `⌊s⌋₊ + 1` steps, for every `R`, uniformly (the bound does not depend
on `R`). -/
theorem natFloor_sq_mul_sub_natFloor_horizon_le (s R : ℝ) (hs : 0 < s) :
    ⌊s * R ^ 2⌋₊ - ⌊(⌊R ^ 2⌋₊ : ℝ) * s⌋₊ ≤ ⌊s⌋₊ + 1 := by
  have h1 := natFloor_horizon_le s R hs
  have h2 := natFloor_sq_mul_le_natFloor_horizon_add s R hs
  omega

end Parking.Generic.FloorGap
end
