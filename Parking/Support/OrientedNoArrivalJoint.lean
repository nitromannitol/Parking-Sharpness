/- The directed no-arrival probability and its exponential lower bound. -/
import Parking.Support.OrientedNoArrivalLaw
import Parking.Support.OrientedArrivalJoint

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
open scoped Classical
variable {d : ℕ}

theorem oriented_noArrival_probability_joint (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (n : ℕ) (x : Site d) :
    ((iidLaw d ν).prod (orientedStackLaw d)).real
      {z : (Site d → ℤ) × (Site d × ℕ → Site d) | orientedArrivalCount z.1 z.2 n x = 0} =
        ∫ z : (Site d → ℤ) × (Site d × ℕ → Site d), (1 - (d : ℝ)⁻¹) ^
          (∑ i : Fin d, orientedOdometer z.1 z.2 n (x - unit i))
          ∂((iidLaw d ν).prod (orientedStackLaw d)) := by
  haveI := orientedStackLaw_isProbability hd
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  let E : Set ((Site d → ℤ) × (Site d × ℕ → Site d)) :=
    {z | orientedArrivalCount z.1 z.2 n x = 0}
  have hE : MeasurableSet E :=
    (measurable_orientedArrivalCount _ _ measurable_fst measurable_snd n x) (measurableSet_singleton 0)
  let F : (Site d → ℤ) × (Site d × ℕ → Site d) → ℝ := fun z =>
    (1 - (d : ℝ)⁻¹) ^ (∑ i : Fin d, orientedOdometer z.1 z.2 n (x - unit i))
  have hF : Measurable F := (measurable_from_countable' fun m : ℕ => (1 - (d : ℝ)⁻¹) ^ m).comp
    (Finset.measurable_sum _ fun i _ =>
      measurable_orientedOdometer _ _ measurable_fst measurable_snd n (x - unit i))
  have hFI : Integrable F ((iidLaw d ν).prod (orientedStackLaw d)) :=
    (integrable_const (1 : ℝ)).mono' hF.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (oriented_miss_probability_nonneg hd) _)]
        exact pow_le_one₀ (oriented_miss_probability_nonneg hd)
          (sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg d))))
  have hEI : Integrable (Set.indicator E (fun _ => (1 : ℝ)))
      ((iidLaw d ν).prod (orientedStackLaw d)) := (integrable_const _).indicator hE
  change ((iidLaw d ν).prod (orientedStackLaw d)).real E = ∫ z, F z ∂_
  rw [← integral_indicator_one (μ := (iidLaw d ν).prod (orientedStackLaw d)) hE]
  change (∫ z, Set.indicator E (fun _ => (1 : ℝ)) z ∂((iidLaw d ν).prod (orientedStackLaw d))) = _
  rw [integral_prod _ hEI, integral_prod _ hFI]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun η => by
    have hm : MeasurableSet {σ : Site d × ℕ → Site d | orientedArrivalCount η σ n x = 0} :=
      (measurable_orientedArrivalCount _ _ measurable_const measurable_id n x) (measurableSet_singleton 0)
    have he : (fun σ : Site d × ℕ → Site d => Set.indicator E (fun _ => (1 : ℝ)) (η, σ)) =
        Set.indicator {σ : Site d × ℕ → Site d | orientedArrivalCount η σ n x = 0}
          (fun _ => (1 : ℝ)) := by
      funext σ
      simp only [Set.indicator_apply, E, Set.mem_setOf_eq]
    change (∫ σ, Set.indicator E (fun _ => (1 : ℝ)) (η, σ) ∂(orientedStackLaw d)) = _
    rw [he]
    exact (integral_indicator_one (μ := orientedStackLaw d) hm).trans
      (oriented_noArrival_probability_given hd η n x)

theorem oriented_noArrival_exp_joint (hd : 2 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (n : ℕ) (x : Site d) :
    Real.exp (Real.log (1 - (d : ℝ)⁻¹) * (d : ℝ) * meanU (orientedLaw d ν) n) ≤
      ((iidLaw d ν).prod (orientedStackLaw d)).real
        {z : (Site d → ℤ) × (Site d × ℕ → Site d) | orientedArrivalCount z.1 z.2 n x = 0} := by
  have hd1 : 1 ≤ d := by omega
  haveI := hν.prob
  haveI := orientedStackLaw_isProbability hd1
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  let q : ℝ := 1 - (d : ℝ)⁻¹
  let V : (Site d → ℤ) × (Site d × ℕ → Site d) → ℝ := fun z =>
    ∑ i : Fin d, (orientedOdometer z.1 z.2 n (x - unit i) : ℝ)
  have hq : 0 < q := oriented_miss_probability_pos hd
  have hm : Measurable V := Finset.measurable_sum _ fun i _ =>
    (measurable_from_countable' fun k : ℕ => (k : ℝ)).comp
      (measurable_orientedOdometer _ _ measurable_fst measurable_snd n (x - unit i))
  have hi : Integrable V ((iidLaw d ν).prod (orientedStackLaw d)) :=
    integrable_finsetSum _ fun i _ => integrable_orientedOdometer_joint hd1 ν hν n (x - unit i)
  have hqi : Integrable (fun z => Real.exp (Real.log q * V z))
      ((iidLaw d ν).prod (orientedStackLaw d)) := by
    refine (integrable_const (1 : ℝ)).mono' (hm.const_mul (Real.log q)).exp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, Real.abs_exp, ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hq.le
      (sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg d))))
      (sum_nonneg fun i _ => Nat.cast_nonneg _)
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun z => Set.mem_univ (Real.log q * V z))
    (hi.const_mul (Real.log q)) hqi
  rw [integral_const_mul, integral_finsetSum _ (fun i _ =>
    integrable_orientedOdometer_joint hd1 ν hν n (x - unit i))] at hj
  simp only [integral_orientedOdometer_joint hd1 ν hν, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← mul_assoc] at hj
  refine hj.trans_eq ?_
  rw [oriented_noArrival_probability_joint hd1 ν n x]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    change Real.exp (Real.log q * V z) = _
    have he : V z = ((∑ i : Fin d, orientedOdometer z.1 z.2 n (x - unit i) : ℕ) : ℝ) := by
      simp only [V, Nat.cast_sum]
    rw [he, mul_comm (Real.log q), Real.exp_nat_mul, Real.exp_log hq]

end Parking
