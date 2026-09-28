import Parking.Support.GreenPotential

/-!
# The escape potential

`escapePotential d x y := 1 - fullGreen d (y - x) / escapeConst d` is the probability that a
simple random walk started at `y` never visits `x`, defined for dimension `d ≥ 3` where the walk
is transient. `escapePotential_bounds` confirms it takes values in `[0, 1]`,
`escapePotential_self` records that it vanishes at `y = x`, and
`integral_step_escapePotential_ge` shows it is subharmonic: averaging over one step of the walk
from `y` can only raise it.
-/

open LatticeProb (measurable_from_countable')

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The probability that a walk started at y avoids x forever. -/
def escapePotential (d : ℕ) (x y : Site d) : ℝ := 1 - fullGreen d (y - x) / escapeConst d

/-- `escapePotential d x y` lies in `[0, 1]`, from `fullGreen_le_escapeConst` and the
nonnegativity of `fullGreen`. -/
theorem escapePotential_bounds (hd : 3 ≤ d) (x y : Site d) :
    0 ≤ escapePotential d x y ∧ escapePotential d x y ≤ 1 := by
  have hg : 0 < escapeConst d := lt_of_lt_of_le zero_lt_one (one_le_escapeConst hd)
  unfold escapePotential
  constructor
  · exact sub_nonneg.mpr ((div_le_one hg).mpr (fullGreen_le_escapeConst hd _))
  · exact sub_le_self _ (div_nonneg (fullGreen_nonneg d _) hg.le)

/-- `escapePotential d x x = 0`: a walk started at its own target visits it immediately. -/
theorem escapePotential_self (hd : 3 ≤ d) (x : Site d) : escapePotential d x x = 0 := by
  have hg : escapeConst d ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_escapeConst hd))
  simp only [escapePotential, sub_self]
  change 1 - escapeConst d / escapeConst d = 0
  rw [div_self hg, sub_self]

/-- The escape probability is subharmonic, including at its absorbing target. -/
theorem integral_step_escapePotential_ge (hd : 3 ≤ d) (x y : Site d) :
    escapePotential d x y ≤ ∫ a, escapePotential d x (y + stepVec a) ∂(stepLaw d) := by
  have hd1 : 1 ≤ d := by omega
  haveI := stepLaw_isProbability hd1
  have hg : 0 < escapeConst d := lt_of_lt_of_le zero_lt_one (one_le_escapeConst hd)
  have hi : Integrable (fun a : Fin d × Bool => fullGreen d (y + stepVec a - x)) (stepLaw d) :=
    Integrable.of_bound (measurable_from_countable' _).aestronglyMeasurable (escapeConst d)
      (ae_of_all _ fun a => by
        change ‖fullGreen d (y + stepVec a - x)‖ ≤ escapeConst d
        rw [Real.norm_eq_abs, abs_of_nonneg (fullGreen_nonneg d _)]
        exact fullGreen_le_escapeConst hd _)
  simp only [escapePotential]
  rw [integral_sub (integrable_const _) (hi.div_const _), integral_div, integral_const,
    probReal_univ, one_smul, integral_step_green hd]
  apply sub_le_sub_left
  apply div_le_div_of_nonneg_right _ hg.le
  exact sub_le_self _ (by split <;> positivity)
end Parking
