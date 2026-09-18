/-
The probability-law correspondence for the critical lower tail cited at
`parking.tex:1807-1833`, in the mass normalization of `sandpile.tex:1696-1720`.
The initial mass is σ = 1 + 2dη. The output odometer equals Parking.u η
exactly; independent instruction and rank coordinates do not affect its law.
-/
import Parking.Support.NearestCriticalModel
import Parking.Support.CriticalLawReal

noncomputable section
open MeasureTheory ProbabilityTheory LatticeProb Filter Topology Parking.CriticalScale

theorem Parking.CriticalScale.relax_centered {d : ℕ} (hd : 1 ≤ d)
    (η f : Site d → ℝ) (x : Site d) :
    relax (fun y => 1 + 2 * (d : ℝ) * η y) f x = max 0 (η x + walkOp f x) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  unfold relax walkOp
  congr 1
  field_simp
  ring

/-- Centering the mass by `1+2dη` gives the parking odometer exactly. -/
theorem Parking.CriticalScale.odometer_centered {d : ℕ} (hd : 1 ≤ d)
    (η : Site d → ℝ) (t : ℕ) :
    odometer (fun y => 1 + 2 * (d : ℝ) * η y) t = Parking.u η t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext x
    rw [odometer, ih, relax_centered hd, Parking.u]

theorem Parking.CriticalScale.measurable_centered (d : ℕ) :
    Measurable (fun η : Site d → ℝ => fun x => 1 + 2 * (d : ℝ) * η x) := by
  exact measurable_pi_lambda _ fun x => measurable_const.add ((measurable_pi_apply x).const_mul _)

theorem Parking.CriticalScale.centeredMassLaw_eq_map (d : ℕ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] : centeredMassLaw d ν =
      (iidLaw d ν).map (fun η : Site d → ℝ => fun x => 1 + 2 * (d : ℝ) * η x) := by
  symm
  unfold centeredMassLaw iidLaw
  exact Measure.infinitePi_map_pi _ (fun _ : Site d =>
    measurable_const.add (measurable_id.const_mul (2 * (d : ℝ))))

theorem Parking.CriticalScale.measurable_odometer {d : ℕ} (t : ℕ) (x : Site d) :
    Measurable (fun σ : Site d → ℝ => odometer σ t x) := by
  induction t generalizing x with
  | zero => exact measurable_const
  | succ t ih =>
    change Measurable (fun σ : Site d → ℝ => max 0 ((σ x - 1 +
      (∑ i : Fin d, (odometer σ t (x + unit i) + odometer σ t (x - unit i)))) /
        (2 * (d : ℝ))))
    exact measurable_const.max ((((measurable_pi_apply x).sub measurable_const).add
      (Finset.measurable_sum Finset.univ (fun i _ =>
        (ih (x + unit i)).add (ih (x - unit i))))).div_const _)

theorem Parking.CriticalScale.centeredMassLaw_isProbability (d : ℕ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (centeredMassLaw d ν) := by
  unfold centeredMassLaw
  haveI : IsProbabilityMeasure (ν.map fun z => 1 + 2 * (d : ℝ) * z) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  unfold iidLaw
  infer_instance

theorem Parking.CriticalScale.lowerTailRemainder_nonneg (d t : ℕ) {L a : ℝ}
    (hL : 0 ≤ L) : 0 ≤ lowerTailRemainder d t L a := by
  unfold lowerTailRemainder
  split <;> exact mul_nonneg
    (mul_nonneg (Real.rpow_nonneg (Real.log_natCast_nonneg t) _)
      (Real.rpow_nonneg (Nat.cast_nonneg t) _)) (Real.rpow_nonneg hL _)

/-- Transport the source lower-tail event along the affine product law. -/
theorem Parking.CriticalScale.odometer_lowerTail_eq {d : ℕ} (hd : 1 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℕ) (x : Site d) (b : ℝ) :
    centeredMassLaw d ν {σ | odometer σ t x ≤ b} =
      (iidLaw d ν) {η | Parking.u η t x ≤ b} := by
  rw [centeredMassLaw_eq_map, Measure.map_apply (measurable_centered d)
    (measurableSet_le (measurable_odometer t x) measurable_const)]
  congr 1
  ext η
  simp only [Set.mem_preimage, Set.mem_setOf_eq, odometer_centered hd]

theorem Parking.CriticalScale.uOf_lowerTail_eq {d : ℕ} (hd : 1 ≤ d)
    (ν : Measure ℤ) [IsProbabilityMeasure ν] (t : ℕ) (x : Site d) (b : ℝ) :
    (Parking.law d ν) {ω | Parking.uOf ω t x ≤ b} =
      (iidLaw d (Parking.realLaw ν)) {η | Parking.u η t x ≤ b} := by
  have h := Measure.map_apply (μ := Parking.law d ν) Parking.measurable_confReal
    (measurableSet_le (Parking.measurable_u_eval t x) (measurable_const (a := b)))
  rw [Parking.law_map_confReal hd ν] at h
  exact h.symm

end
