/- The complete directed Green norm profile. -/
import Parking.Support.OrientedGreenRates
import Parking.Support.OrientedLowerNorm
import Parking.Support.VarianceNonconstant

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory LatticeProb
variable {d : ℕ}

theorem exists_orientedGreen_sq_rates (hd : 2 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      c * orientedKappa d n ≤ ∑' x : Site d, orientedGreen d n x ^ 2 ∧
        (∑' x : Site d, orientedGreen d n x ^ 2) ≤ C * orientedKappa d n := by
  by_cases hd2 : d = 2
  · subst d
    refine ⟨1 / 2, 2, by norm_num, by norm_num, fun n _ => ?_⟩
    simpa [orientedKappa, Real.sqrt_eq_rpow] using orientedGreen_two_sq_bounds n
  · by_cases hd3 : d = 3
    · subst d
      obtain ⟨c, C, hc, hC, hb⟩ := exists_orientedGreen_three_sq_bounds
      refine ⟨c, C, hc, hC, fun n hn => ?_⟩
      simpa [orientedKappa] using hb n hn
    · obtain ⟨C, hC, hb⟩ := exists_orientedGreen_high_sq_bound (d := d) (by omega)
      refine ⟨1, C, by norm_num, hC, fun n hn => ?_⟩
      simp only [orientedKappa, if_neg hd2, if_neg hd3, mul_one]
      exact ⟨one_le_orientedGreen_sq n hn, hb n hn⟩

theorem exists_meanuOriented_variance_lower (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k : ℤ, (k : ℝ) ∂ν = 0)
    (hv : 0 < evariance (fun k : ℤ => (k : ℝ)) ν) (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c * Real.sqrt (orientedKappa d n) ≤ meanuOriented (orientedLaw d ν) n := by
  obtain ⟨a, ha, hlo⟩ := exists_meanuOriented_lower_norm ν (nonconstant_of_evariance_pos ν hv) hint hmean
  obtain ⟨c, C, hc, _hC, hb⟩ := exists_orientedGreen_sq_rates hd
  refine ⟨a * Real.sqrt c, by positivity, fun n hn => ?_⟩
  have h := Real.sqrt_le_sqrt (hb n hn).1
  rw [Real.sqrt_mul hc.le] at h
  have hh := mul_le_mul_of_nonneg_left h ha.le
  calc (a * Real.sqrt c) * Real.sqrt (orientedKappa d n) ≤
      a * Real.sqrt (∑' x : Site d, orientedGreen d n x ^ 2) := by simpa only [mul_assoc] using hh
    _ ≤ _ := hlo d (by omega) n

end Parking
