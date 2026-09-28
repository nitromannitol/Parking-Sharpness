import Parking.Basic

/-!
# The three-point law

Packages the symmetric three-point probability law on `ℤ` used elsewhere in the
formalization: mass `p` on each of `1` and `-1`, and the remaining mass `1 - 2p`
on `0`. It is built as a weighted sum of `ENNReal.ofReal`-scaled Dirac measures,
so it is defined for every real `p`, even though it is only a probability
measure when `0 ≤ p ≤ 1/2`.
-/

open MeasureTheory

/-- The three-point law `P(±1) = p`, `P(0) = 1 - 2p` on `ℤ`. -/
noncomputable def Parking.threePointLaw (p : ℝ) : Measure ℤ :=
  ENNReal.ofReal p • Measure.dirac 1 + ENNReal.ofReal p • Measure.dirac (-1) +
    ENNReal.ofReal (1 - 2 * p) • Measure.dirac 0

