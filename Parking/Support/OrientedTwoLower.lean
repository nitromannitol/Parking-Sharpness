/- Step 2 of the oriented walk theorem, lower half: the directed particle mean
dominates the directed divisible mean, which grows like `n^{1/4}`
(`parking.tex:3290-3295`). -/
import Parking.Support.DensitySequence
import Parking.Support.OrientedLowerRates
import Parking.Support.OrientedMeanComparison

noncomputable section
namespace Parking
open MeasureTheory LatticeProb

/-- The dimension-two lower bound of Step 2 of `thm:oriented-walk`
(`parking.tex:3290-3295`): the directed particle mean dominates the directed
divisible mean, which grows like `n^{1/4}`. -/
theorem exists_meanU_oriented_two_lower (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      c * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ meanU (orientedLaw 2 ν) n := by
  haveI := hν.prob
  obtain ⟨c, hc, hb⟩ := exists_meanuOriented_two_lower ν hν.nonconst hν.integrable_abs hν.mean
  exact ⟨c, hc, fun n => (hb n).trans (meanuOriented_le_meanU (by norm_num) ν hν n)⟩

end Parking
