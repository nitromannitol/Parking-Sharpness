/- Exact no-arrival probability from fresh predecessor instructions. -/
import Parking.Support.OrientedIncomingSlots
import Parking.Support.CountableFiberIntegral
import Parking.Support.OrientedGivenBound

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

theorem oriented_miss_probability_nonneg (hd : 1 ≤ d) : 0 ≤ 1 - (d : ℝ)⁻¹ := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  exact sub_nonneg.mpr ((inv_le_one₀ (by positivity)).mpr hdR)

theorem oriented_miss_probability_pos (hd : 2 ≤ d) : 0 < 1 - (d : ℝ)⁻¹ := by
  have hdR : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  exact sub_pos.mpr ((inv_lt_one₀ (by positivity)).mpr hdR)

theorem oriented_noArrival_probability_given (hd : 1 ≤ d) (η : Site d → ℤ)
    (n : ℕ) (x : Site d) :
    (orientedStackLaw d).real {σ : Site d × ℕ → Site d | orientedArrivalCount η σ n x = 0} =
      ∫ σ : Site d × ℕ → Site d, (1 - (d : ℝ)⁻¹) ^
        (∑ i : Fin d, orientedOdometer η σ n (x - unit i)) ∂(orientedStackLaw d) := by
  haveI := orientedStackLaw_isProbability hd
  apply probability_eq_integral_of_fibers (orientedStackLaw d)
    (fun σ : Site d × ℕ → Site d => fun i : Fin d => orientedOdometer η σ n (x - unit i))
    (measurable_pi_lambda _ fun i =>
      measurable_orientedOdometer _ _ measurable_const measurable_id n (x - unit i))
    {σ : Site d × ℕ → Site d | orientedArrivalCount η σ n x = 0}
    (fun m : Fin d → ℕ => (1 - (d : ℝ)⁻¹) ^ (∑ i, m i))
  · intro m
    exact pow_nonneg (oriented_miss_probability_nonneg hd) _
  · intro m
    exact pow_le_one₀ (oriented_miss_probability_nonneg hd)
      (sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg d)))
  · exact fun m => oriented_noArrival_count_fiber hd η n x m

theorem oriented_noArrival_exp_given (hd : 2 ≤ d) (η : Site d → ℤ)
    (n : ℕ) (x : Site d) :
    Real.exp (Real.log (1 - (d : ℝ)⁻¹) * ∑ i : Fin d,
      ∫ σ : Site d × ℕ → Site d,
        (orientedOdometer η σ n (x - unit i) : ℝ) ∂(orientedStackLaw d)) ≤
      (orientedStackLaw d).real {σ : Site d × ℕ → Site d | orientedArrivalCount η σ n x = 0} := by
  have hd1 : 1 ≤ d := by omega
  haveI := orientedStackLaw_isProbability hd1
  let q : ℝ := 1 - (d : ℝ)⁻¹
  let V : (Site d × ℕ → Site d) → ℝ := fun σ =>
    ∑ i : Fin d, (orientedOdometer η σ n (x - unit i) : ℝ)
  have hq : 0 < q := oriented_miss_probability_pos hd
  have hm : Measurable V := Finset.measurable_sum _ fun i _ =>
    (measurable_from_countable' fun k : ℕ => (k : ℝ)).comp
      (measurable_orientedOdometer _ _ measurable_const measurable_id n (x - unit i))
  have hi : Integrable V (orientedStackLaw d) := integrable_finsetSum _ fun i _ =>
    integrable_orientedOdometer_given hd1 η n (x - unit i)
  have hqi : Integrable (fun σ => Real.exp (Real.log q * V σ)) (orientedStackLaw d) := by
    refine (integrable_const (1 : ℝ)).mono' (hm.const_mul (Real.log q)).exp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun σ => ?_)
    rw [Real.norm_eq_abs, Real.abs_exp, ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hq.le
      (sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg d))))
      (sum_nonneg fun i _ => Nat.cast_nonneg _)
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun σ => Set.mem_univ (Real.log q * V σ))
    (hi.const_mul (Real.log q)) hqi
  rw [integral_const_mul, integral_finsetSum _ (fun i _ =>
    integrable_orientedOdometer_given hd1 η n (x - unit i))] at hj
  refine hj.trans_eq ?_
  rw [oriented_noArrival_probability_given hd1 η n x]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun σ => by
    change Real.exp (Real.log q * V σ) = _
    have he : V σ = ((∑ i : Fin d, orientedOdometer η σ n (x - unit i) : ℕ) : ℝ) := by
      simp only [V, Nat.cast_sum]
    rw [he, mul_comm (Real.log q), Real.exp_nat_mul, Real.exp_log hq]

end Parking
