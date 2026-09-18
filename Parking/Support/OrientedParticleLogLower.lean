/- A logarithmic lower bound for the directed particle odometer mean. -/
import Parking.Support.OrientedNoArrivalJoint
import Parking.Support.OrientedMeanIncrement
import Parking.Support.ExponentialGrowth

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

theorem oriented_mean_exp_increment (hd : 2 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ c L : ℝ, 0 < c ∧ 0 < L ∧ ∀ n : ℕ,
      c * Real.exp (-L * meanU (orientedLaw d ν) n) ≤
        meanU (orientedLaw d ν) (n + 1) - meanU (orientedLaw d ν) n := by
  let q : ℝ := 1 - (d : ℝ)⁻¹
  let L : ℝ := -(Real.log q * (d : ℝ))
  have hq : 0 < q := oriented_miss_probability_pos hd
  have hq1 : q < 1 := sub_lt_self _ (inv_pos.mpr (show (0 : ℝ) < d by exact_mod_cast (show 0 < d by omega)))
  have hL : 0 < L := neg_pos.mpr (mul_neg_of_neg_of_pos (Real.log_neg hq hq1)
    (show (0 : ℝ) < d by exact_mod_cast (show 0 < d by omega)))
  refine ⟨∫ k : ℤ, max (-(k : ℝ)) 0 ∂ν, L, hν.negativePart_mean_pos, hL, fun n => ?_⟩
  have h := mul_le_mul_of_nonneg_left (oriented_noArrival_exp_joint hd ν hν n 0)
    hν.negativePart_mean_pos.le
  have he : -L * meanU (orientedLaw d ν) n =
      Real.log (1 - (d : ℝ)⁻¹) * (d : ℝ) * meanU (orientedLaw d ν) n := by
    simp only [L, q, neg_neg]
  rw [he]
  exact h.trans (oriented_mean_increment_noArrival (by omega) ν hν n)

theorem exists_meanU_oriented_log_lower (hd : 2 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      c * Real.log ((n : ℝ) + 1) ≤ meanU (orientedLaw d ν) n := by
  obtain ⟨c, L, hc, hL, hs⟩ := oriented_mean_exp_increment hd ν hν
  apply logarithmic_growth_of_exp_increment (meanU (orientedLaw d ν)) _ hc hL hs
  simp [meanU, U, LatticeProb.particleOdometer]

end Parking
