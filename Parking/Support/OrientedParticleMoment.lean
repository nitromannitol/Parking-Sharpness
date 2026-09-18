/- Higher moments and monotonicity of the directed count recursion. -/
import Parking.Support.OrientedCountLaw
import Parking.Support.Monotone

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

theorem orientedOdometer_mono_time (η : Site d → ℤ) (σ : Site d × ℕ → Site d) (x : Site d) :
    Monotone (fun n => orientedOdometer η σ n x) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n generalizing x with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    change (η x + ∑ i : Fin d, (arrivals σ (x - unit i) x
      (orientedOdometer η σ n (x - unit i)) : ℤ)).toNat ≤
      (η x + ∑ i : Fin d, (arrivals σ (x - unit i) x
      (orientedOdometer η σ (n + 1) (x - unit i)) : ℤ)).toNat
    apply Int.toNat_le_toNat
    apply add_le_add le_rfl
    exact sum_le_sum fun i _ => by exact_mod_cast arrivals_mono σ _ _ (ih (x - unit i))

theorem integrable_orientedOdometer_joint_rpow (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    {r : ℝ} (hr : 1 ≤ r) (n : ℕ) (x : Site d) :
    Integrable (fun z : (Site d → ℤ) × (Site d × ℕ → Site d) =>
      (orientedOdometer z.1 z.2 n x : ℝ) ^ r) ((iidLaw d ν).prod (orientedStackLaw d)) := by
  haveI := hν.prob
  obtain ⟨θ, hθ, he⟩ := hν.expMoment
  have hm : Measurable (fun z : (Site d → ℤ) × (Site d × ℕ → Site d) =>
      (orientedOdometer z.1 z.2 n x : ℝ) ^ r) :=
    (measurable_from_countable' fun m : ℕ => (m : ℝ) ^ r).comp
      (measurable_orientedOdometer _ _ measurable_fst measurable_snd n x)
  rw [← orientedLaw_map_confStack hd ν]
  apply (integrable_map_measure hm.aestronglyMeasurable (by fun_prop)).mpr
  exact (integrable_oriented_U_rpow hd ν hθ (integrable_expMax_of_expAbs hθ he) hr n x).congr
    ((orientedOdometer_ae_eq_U hd ν n x).mono fun ω hω => congrArg (fun k : ℕ => (k : ℝ) ^ r) hω.symm)

theorem integral_oriented_U_rpow_shift (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (r : ℝ) (n : ℕ) (x : Site d) :
    (∫ ω : Data d, (U ω n x : ℝ) ^ r ∂(orientedLaw d ν)) =
      ∫ ω : Data d, (U ω n 0 : ℝ) ^ r ∂(orientedLaw d ν) := by
  have hm : Measurable (fun ω : Data d => (U ω n x : ℝ) ^ r) :=
    (measurable_from_countable' fun m : ℕ => (m : ℝ) ^ r).comp (measurable_U n x)
  have h := integral_map (μ := orientedLaw d ν) (φ := shiftData (-x))
    (f := fun ω : Data d => (U ω n x : ℝ) ^ r) (measurable_shiftData _).aemeasurable hm.aestronglyMeasurable
  rw [orientedLaw_map_shiftData hd ν (-x)] at h
  simpa only [U_shiftData, add_neg_cancel] using h

theorem integral_orientedOdometer_joint_rpow (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (r : ℝ) (n : ℕ) (x : Site d) :
    (∫ z : (Site d → ℤ) × (Site d × ℕ → Site d), (orientedOdometer z.1 z.2 n x : ℝ) ^ r
      ∂((iidLaw d ν).prod (orientedStackLaw d))) =
      ∫ ω : Data d, (U ω n 0 : ℝ) ^ r ∂(orientedLaw d ν) := by
  have hm : Measurable (fun z : (Site d → ℤ) × (Site d × ℕ → Site d) =>
      (orientedOdometer z.1 z.2 n x : ℝ) ^ r) :=
    (measurable_from_countable' fun m : ℕ => (m : ℝ) ^ r).comp
      (measurable_orientedOdometer _ _ measurable_fst measurable_snd n x)
  calc
    _ = ∫ ω : Data d, (orientedOdometer ω.1 ω.2.1 n x : ℝ) ^ r ∂(orientedLaw d ν) :=
      (integral_oriented_confStack hd ν hm).symm
    _ = ∫ ω : Data d, (U ω n x : ℝ) ^ r ∂(orientedLaw d ν) :=
      integral_congr_ae ((orientedOdometer_ae_eq_U hd ν n x).mono
        fun ω hω => congrArg (fun k : ℕ => (k : ℝ) ^ r) hω)
    _ = _ := integral_oriented_U_rpow_shift hd ν r n x

end Parking
