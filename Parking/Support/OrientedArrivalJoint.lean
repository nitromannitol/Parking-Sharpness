/- Unconditional arrival means for the directed particle recursion. -/
import Parking.Support.OrientedArrivalMean
import Parking.Support.OrientedCountLaw

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

theorem integrable_orientedArrivalCount_joint (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (n : ℕ) (x : Site d) :
    Integrable (fun z : (Site d → ℤ) × (Site d × ℕ → Site d) =>
      (orientedArrivalCount z.1 z.2 n x : ℝ)) ((iidLaw d ν).prod (orientedStackLaw d)) := by
  have hdom : Integrable (fun z : (Site d → ℤ) × (Site d × ℕ → Site d) =>
      ∑ i : Fin d, (orientedOdometer z.1 z.2 n (x - unit i) : ℝ))
      ((iidLaw d ν).prod (orientedStackLaw d)) :=
    integrable_finsetSum _ fun i _ => integrable_orientedOdometer_joint hd ν hν n (x - unit i)
  have hm : Measurable (fun z : (Site d → ℤ) × (Site d × ℕ → Site d) =>
      (orientedArrivalCount z.1 z.2 n x : ℝ)) :=
    (measurable_from_countable' fun k : ℕ => (k : ℝ)).comp
      (measurable_orientedArrivalCount _ _ measurable_fst measurable_snd n x)
  refine hdom.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  simp only [orientedArrivalCount, Nat.cast_sum]
  apply sum_le_sum
  intro i _
  exact_mod_cast (show arrivals z.2 (x - unit i) x (orientedOdometer z.1 z.2 n (x - unit i)) ≤
    orientedOdometer z.1 z.2 n (x - unit i) by
      simpa only [arrivals, card_range] using card_filter_le
        (range (orientedOdometer z.1 z.2 n (x - unit i))) (fun j => z.2 (x - unit i, j) = x))

theorem integral_orientedArrivalCount_joint (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (n : ℕ) (x : Site d) :
    (∫ z : (Site d → ℤ) × (Site d × ℕ → Site d),
      (orientedArrivalCount z.1 z.2 n x : ℝ) ∂((iidLaw d ν).prod (orientedStackLaw d))) =
        meanU (orientedLaw d ν) n := by
  haveI := hν.prob
  haveI := orientedStackLaw_isProbability hd
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  rw [integral_prod _ (integrable_orientedArrivalCount_joint hd ν hν n x)]
  simp only [integral_orientedArrivalCount_given hd, orientedOp]
  rw [integral_div, integral_finsetSum _ (fun i _ =>
    (integrable_orientedOdometer_joint hd ν hν n (x - unit i)).integral_prod_left)]
  simp only [integral_orientedOdometer_given_mean hd ν hν, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (ne_of_gt (show (0 : ℝ) < d by exact_mod_cast hd))

theorem integral_orientedOdometer_joint (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (n : ℕ) (x : Site d) :
    (∫ z : (Site d → ℤ) × (Site d × ℕ → Site d),
      (orientedOdometer z.1 z.2 n x : ℝ) ∂((iidLaw d ν).prod (orientedStackLaw d))) =
        meanU (orientedLaw d ν) n := by
  haveI := hν.prob
  haveI := orientedStackLaw_isProbability hd
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  rw [integral_prod _ (integrable_orientedOdometer_joint hd ν hν n x)]
  exact integral_orientedOdometer_given_mean hd ν hν n x

end Parking
