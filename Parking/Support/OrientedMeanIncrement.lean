/- Unfilled scenery forces an increase in the directed particle mean. -/
import Parking.Support.OrientedArrivalJoint
import Parking.Support.OrientedNegativeFactor
import Parking.Support.NegativeMean

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
open scoped Classical
variable {d : ℕ}

theorem toNat_add_lower_with_zero_reward (k : ℤ) (m : ℕ) :
    (k : ℝ) + (m : ℝ) + max (-(k : ℝ)) 0 * (if m = 0 then (1 : ℝ) else 0) ≤
      ((k + (m : ℤ)).toNat : ℝ) := by
  rw [toNat_cast_eq_max, Int.cast_add, Int.cast_natCast]
  by_cases hm : m = 0
  · subst m
    simp only [Nat.cast_zero, add_zero, ↓reduceIte, mul_one]
    by_cases hk : 0 ≤ (k : ℝ)
    · rw [max_eq_right (neg_nonpos.mpr hk), max_eq_left hk, add_zero]
    · have hk0 : (k : ℝ) ≤ 0 := (not_le.mp hk).le
      rw [max_eq_left (neg_nonneg.mpr hk0), max_eq_right hk0]
      linarith
  · simp only [if_neg hm, mul_zero, add_zero]
    exact le_max_left _ _

theorem oriented_mean_increment_noArrival (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (n : ℕ) :
    (∫ k : ℤ, max (-(k : ℝ)) 0 ∂ν) *
      ((iidLaw d ν).prod (orientedStackLaw d)).real
        {z : (Site d → ℤ) × (Site d × ℕ → Site d) | orientedArrivalCount z.1 z.2 n 0 = 0} ≤
      meanU (orientedLaw d ν) (n + 1) - meanU (orientedLaw d ν) n := by
  haveI := hν.prob
  haveI := orientedStackLaw_isProbability hd
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  have hiν : Integrable (fun k : ℤ => (k : ℝ)) ν :=
    (integrable_norm_iff (measurable_of_countable _).aestronglyMeasurable).mp
      (by simpa only [Real.norm_eq_abs] using hν.integrable_abs)
  have hiη : Integrable (fun η : Site d → ℤ => (η 0 : ℝ)) (iidLaw d ν) :=
    integrable_comp_mp (measurePreserving_eval_infinitePi (fun _ : Site d => ν) 0)
      (fun k : ℤ => (k : ℝ)) (measurable_of_countable _).aestronglyMeasurable hiν
  have hiηJ := hiη.comp_fst (orientedStackLaw d)
  have hmeanη : (∫ η : Site d → ℤ, (η 0 : ℝ) ∂(iidLaw d ν)) = 0 :=
    (integral_comp_mp (measurePreserving_eval_infinitePi (fun _ : Site d => ν) 0)
      (fun k : ℤ => (k : ℝ)) (measurable_of_countable _).aestronglyMeasurable).symm.trans hν.mean
  have hiN := integrable_orientedArrivalCount_joint hd ν hν n 0
  have hiR := integrable_oriented_noArrival_negative_joint hd ν hν n 0
  have hiU := integrable_orientedOdometer_joint hd ν hν (n + 1) 0
  have hpt (z : (Site d → ℤ) × (Site d × ℕ → Site d)) :
      (z.1 0 : ℝ) + (orientedArrivalCount z.1 z.2 n 0 : ℝ) +
        max (-(z.1 0 : ℝ)) 0 * (if orientedArrivalCount z.1 z.2 n 0 = 0 then (1 : ℝ) else 0) ≤
          (orientedOdometer z.1 z.2 (n + 1) 0 : ℝ) := by
    rw [orientedOdometer_succ]
    exact toNat_add_lower_with_zero_reward _ _
  have hle := integral_mono ((hiηJ.add hiN).add hiR) hiU hpt
  have heSum := integral_add (hiηJ.add hiN) hiR
  have heSum0 := integral_add hiηJ hiN
  simp only [Pi.add_apply] at heSum heSum0 hle
  rw [heSum, heSum0] at hle
  simp only [integral_orientedArrivalCount_joint hd ν hν n 0,
    integral_orientedOdometer_joint hd ν hν (n + 1) 0,
    integral_oriented_noArrival_negative_joint hd ν hν n 0] at hle
  have heη : (∫ z : (Site d → ℤ) × (Site d × ℕ → Site d), (z.1 0 : ℝ)
      ∂((iidLaw d ν).prod (orientedStackLaw d))) = 0 := by
    rw [integral_prod _ hiηJ]
    simp only [integral_const, probReal_univ, one_smul, hmeanη]
  rw [heη] at hle
  linarith

end Parking
