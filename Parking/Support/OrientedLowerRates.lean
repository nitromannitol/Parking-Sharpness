/- Lower rates already determined by the directed Green norm. -/
import Parking.Support.OrientedLowerNorm
import Parking.Support.OrientedNormPositive
import Parking.Support.OrientedTwoMean

noncomputable section
namespace Parking
open MeasureTheory LatticeProb

theorem exists_meanuOriented_two_lower (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hnc : ∀ k : ℤ, ν {k} ≠ 1) (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k : ℤ, (k : ℝ) ∂ν = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      c * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ meanuOriented (orientedLaw 2 ν) n := by
  obtain ⟨c, hc, hb⟩ := exists_meanuOriented_lower_norm ν hnc hint hmean
  refine ⟨c * Real.sqrt (1 / 2 : ℝ), by positivity, fun n => ?_⟩
  have h := mul_le_mul_of_nonneg_left (orientedGreen_two_l2_bounds n).1 hc.le
  calc (c * Real.sqrt (1 / 2 : ℝ)) * (n : ℝ) ^ ((1 : ℝ) / 4)
      ≤ c * l2Norm (orientedGreen 2 n) := by simpa only [mul_assoc] using h
    _ ≤ _ := hb 2 (by norm_num) n

theorem exists_meanuOriented_uniform_lower (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hnc : ∀ k : ℤ, ν {k} ≠ 1) (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k : ℤ, (k : ℝ) ∂ν = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n →
      c ≤ meanuOriented (orientedLaw d ν) n := by
  obtain ⟨c, hc, hb⟩ := exists_meanuOriented_lower_norm ν hnc hint hmean
  refine ⟨c, hc, fun d hd n hn => ?_⟩
  have h := mul_le_mul_of_nonneg_left (one_le_orientedGreen_l2 (d := d) n hn) hc.le
  calc c ≤ c * l2Norm (orientedGreen d n) := by simpa only [mul_one] using h
    _ ≤ _ := hb d hd n

theorem exists_meanuOriented_two_bounds (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hnc : ∀ k : ℤ, ν {k} ≠ 1) (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k : ℤ, (k : ℝ) ∂ν = 0) (r : ℝ) (hr : 4 < r)
    (hmom : Integrable (fun k : ℤ => |(k : ℝ)| ^ r) ν) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      c * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ meanuOriented (orientedLaw 2 ν) n ∧
        meanuOriented (orientedLaw 2 ν) n ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4) := by
  obtain ⟨c, hc, hlo⟩ := exists_meanuOriented_two_lower ν hnc hint hmean
  obtain ⟨C, hC, hhi⟩ := exists_meanuOriented_two_upper ν hmean r hr hmom
  refine ⟨c, c + C, hc, by linarith, fun n hn => ⟨hlo n, (hhi n hn).trans ?_⟩⟩
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

end Parking
