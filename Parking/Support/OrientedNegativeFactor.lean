/- The unused scenery at the arrival layer factors from the no-arrival event. -/
import Parking.Support.OrientedFreshness
import Parking.Support.FiniteRandomCount
import Parking.Support.DensitySequence
import Parking.Support.LinearFirstMoment

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory LatticeProb
open scoped Classical
variable {d : ℕ}

theorem integral_oriented_noArrival_negative_given (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (σ : Site d × ℕ → Site d) (n : ℕ) (x : Site d) :
    (∫ η : Site d → ℤ, max (-(η x : ℝ)) 0 *
      (if orientedArrivalCount η σ n x = 0 then (1 : ℝ) else 0) ∂(iidLaw d ν)) =
      (∫ k : ℤ, max (-(k : ℝ)) 0 ∂ν) *
        (iidLaw d ν).real {η : Site d → ℤ | orientedArrivalCount η σ n x = 0} := by
  let f : ℤ → ℝ := fun k => max (-(k : ℝ)) 0
  let g : ℕ → ℝ := fun k => if k = 0 then 1 else 0
  have hf : Measurable f := measurable_of_countable f
  have hg : Measurable g := measurable_of_countable g
  have hind := (orientedArrivalCount_indep_conf_coord ν σ n x x le_rfl).symm.comp hf hg
  have h := hind.integral_fun_mul_eq_mul_integral
    (hf.comp (measurable_pi_apply x)).aestronglyMeasurable
    (hg.comp (measurable_orientedArrivalCount _ _ measurable_id measurable_const n x)).aestronglyMeasurable
  simp only [Function.comp_apply] at h
  have hmean : (∫ η : Site d → ℤ, f (η x) ∂(iidLaw d ν)) = ∫ k, f k ∂ν :=
    (integral_comp_mp (measurePreserving_eval_infinitePi (fun _ : Site d => ν) x)
      f hf.aestronglyMeasurable).symm
  change (∫ η : Site d → ℤ, f (η x) * g (orientedArrivalCount η σ n x) ∂(iidLaw d ν)) = _
  rw [h, hmean]
  congr 1
  have hN : MeasurableSet {η : Site d → ℤ | orientedArrivalCount η σ n x = 0} :=
    (measurable_orientedArrivalCount _ _ measurable_id measurable_const n x) (measurableSet_singleton 0)
  apply Eq.trans ?_ (integral_event_indicator (iidLaw d ν) hN)
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun η => by
    by_cases hz : orientedArrivalCount η σ n x = 0 <;> simp [g, hz]

theorem integrable_oriented_noArrival_negative_joint (hd : 1 ≤ d) (ν : Measure ℤ)
    (hν : CriticalLaw ν) (n : ℕ) (x : Site d) :
    Integrable (fun z : (Site d → ℤ) × (Site d × ℕ → Site d) => max (-(z.1 x : ℝ)) 0 *
      (if orientedArrivalCount z.1 z.2 n x = 0 then (1 : ℝ) else 0))
      ((iidLaw d ν).prod (orientedStackLaw d)) := by
  haveI := hν.prob
  haveI := orientedStackLaw_isProbability hd
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  have hηI : Integrable (fun η : Site d → ℤ => |(η x : ℝ)|) (iidLaw d ν) :=
    integrable_comp_mp (measurePreserving_eval_infinitePi (fun _ : Site d => ν) x)
      (fun k : ℤ => |(k : ℝ)|) (measurable_of_countable _).aestronglyMeasurable hν.integrable_abs
  have hdom := hηI.comp_fst (orientedStackLaw d)
  have hmN : MeasurableSet {z : (Site d → ℤ) × (Site d × ℕ → Site d) |
      orientedArrivalCount z.1 z.2 n x = 0} :=
    (measurable_orientedArrivalCount _ _ measurable_fst measurable_snd n x) (measurableSet_singleton 0)
  refine hdom.mono' ((by fun_prop : Measurable (fun z : (Site d → ℤ) × (Site d × ℕ → Site d) =>
    max (-(z.1 x : ℝ)) 0)).mul (Measurable.ite hmN measurable_const measurable_const)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : orientedArrivalCount z.1 z.2 n x = 0
  · rw [if_pos hz, mul_one, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  · simp only [if_neg hz, mul_zero, norm_zero]
    exact abs_nonneg _

theorem integral_oriented_noArrival_negative_joint (hd : 1 ≤ d) (ν : Measure ℤ)
    (hν : CriticalLaw ν) (n : ℕ) (x : Site d) :
    (∫ z : (Site d → ℤ) × (Site d × ℕ → Site d), max (-(z.1 x : ℝ)) 0 *
      (if orientedArrivalCount z.1 z.2 n x = 0 then (1 : ℝ) else 0)
      ∂((iidLaw d ν).prod (orientedStackLaw d))) =
      (∫ k : ℤ, max (-(k : ℝ)) 0 ∂ν) *
        ((iidLaw d ν).prod (orientedStackLaw d)).real
          {z : (Site d → ℤ) × (Site d × ℕ → Site d) | orientedArrivalCount z.1 z.2 n x = 0} := by
  haveI := hν.prob
  haveI := orientedStackLaw_isProbability hd
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  rw [integral_prod_symm _ (integrable_oriented_noArrival_negative_joint hd ν hν n x)]
  simp only [integral_oriented_noArrival_negative_given ν]
  rw [integral_const_mul]
  congr 1
  let E : Set ((Site d → ℤ) × (Site d × ℕ → Site d)) :=
    {z | orientedArrivalCount z.1 z.2 n x = 0}
  have hE : MeasurableSet E := (measurable_orientedArrivalCount _ _ measurable_fst measurable_snd n x)
    (measurableSet_singleton 0)
  rw [← integral_indicator_one (μ := (iidLaw d ν).prod (orientedStackLaw d)) hE]
  change _ = ∫ z, Set.indicator E (fun _ => (1 : ℝ)) z ∂((iidLaw d ν).prod (orientedStackLaw d))
  rw [integral_prod_symm _ ((integrable_const (1 : ℝ)).indicator hE)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun σ => by
    have hm : MeasurableSet {η : Site d → ℤ | orientedArrivalCount η σ n x = 0} :=
      (measurable_orientedArrivalCount _ _ measurable_id measurable_const n x) (measurableSet_singleton 0)
    apply (integral_event_indicator (μ := iidLaw d ν) hm).symm.trans
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun η => by
      by_cases hz : orientedArrivalCount η σ n x = 0 <;> simp [E, hz]

end Parking
