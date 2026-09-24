/-
The spatial cutoff `χ_A` of the scaling limit.

The cited stability estimates need UNIFORMLY BOUNDED rewards, while the
rescaled potential field is only in `L^r`.  The paper's remedy, and the one the
companion divisible-sandpile argument uses, is a continuous cutoff
`χ_A : ℝ → [0,1]` equal to one on `|y| ≤ A` and to zero on `|y| ≥ 2A`; the
`L^r` bound `Parking.exists_uOriented_two_moment` is what makes the truncation
harmless as `A → ∞`.

`χ_A(y) = max 0 (min 1 (2 - |y|/A))` is such a cutoff: it is one exactly where
`|y|/A ≤ 1` and zero exactly where `|y|/A ≥ 2`, and it is continuous for
`A > 0`.
-/
import Mathlib

noncomputable section

namespace Parking

/-- The continuous spatial cutoff: one on `|y| ≤ A`, zero on `|y| ≥ 2A`, with
values in `[0,1]`. -/
def spatialCutoff (A y : ℝ) : ℝ := max 0 (min 1 (2 - |y| / A))

theorem continuous_spatialCutoff (A : ℝ) : Continuous (spatialCutoff A) := by
  unfold spatialCutoff
  exact continuous_const.max (continuous_const.min (continuous_const.sub
    (continuous_abs.div_const A)))

/-- The cutoff is one where it should be. -/
theorem spatialCutoff_eq_one {A y : ℝ} (hA : 0 < A) (h : |y| ≤ A) :
    spatialCutoff A y = 1 := by
  have hdiv : |y| / A ≤ 1 := (div_le_one hA).mpr h
  have h1 : (1 : ℝ) ≤ 2 - |y| / A := by linarith
  unfold spatialCutoff
  rw [min_eq_left h1, max_eq_right (zero_le_one)]

/-- The cutoff vanishes outside twice the radius. -/
theorem spatialCutoff_eq_zero {A y : ℝ} (hA : 0 < A) (h : 2 * A ≤ |y|) :
    spatialCutoff A y = 0 := by
  have hdiv : (2 : ℝ) ≤ |y| / A := (le_div_iff₀ hA).mpr (by linarith)
  have h1 : 2 - |y| / A ≤ 0 := by linarith
  unfold spatialCutoff
  rw [min_eq_right (by linarith), max_eq_left h1]

theorem spatialCutoff_nonneg (A y : ℝ) : 0 ≤ spatialCutoff A y := le_max_left _ _

theorem spatialCutoff_le_one (A y : ℝ) : spatialCutoff A y ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

end Parking

end
