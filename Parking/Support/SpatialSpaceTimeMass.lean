/- Uniform first moments of the divisible odometer on compact space-time sets. -/
import Parking.Support.SpatialSpaceTimeMeasurable
import Parking.Support.MeanuGrowthBounds
import Parking.Support.UDivisibleShift

open MeasureTheory LatticeProb Set Filter Topology
noncomputable section
namespace Parking
variable {d : ℕ}

theorem integral_uOf_shift (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (n : ℕ) (x : Site d) :
    ∫ w, uOf w n x ∂law d ν = meanu (law d ν) n := by
  have hm := law_map_shiftData hd ν x
  have hi := integral_map (μ := law d ν) (φ := shiftData x)
    (f := fun w => uOf w n 0) (measurable_shiftData x).aemeasurable
    (by rw [hm]; exact (measurable_uOf n 0).aestronglyMeasurable)
  rw [hm] at hi
  simpa only [uOf_shiftData, zero_add, meanu] using hi.symm

theorem barDivisible_nonneg (w : Data d) {R : ℝ} (hR : 0 ≤ R)
    (t : ℝ) (x : Fin d → ℝ) : 0 ≤ barDivisible w R t x := by
  exact mul_nonneg (Real.rpow_nonneg hR _) (by cases ⌊t * R ^ 2⌋₊ <;> simp [uOf, u])

theorem integral_barDivisible_eq (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (R t : ℝ) (x : Fin d → ℝ) :
    ∫ w, barDivisible w R t x ∂law d ν =
      R ^ ((d : ℝ) / 2 - 2) * meanu (law d ν) ⌊t * R ^ 2⌋₊ := by
  unfold barDivisible
  rw [integral_const_mul, integral_uOf_shift hd]

/-- A fixed upper time horizon controls all one-point means at all large scales. -/
theorem exists_integral_barDivisible_le (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : External.SandpileGrowth) (ν : Measure ℤ) (hν : CriticalLaw ν)
    {H : ℝ} (hH : 1 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 2 ≤ R → ∀ t : ℝ, t ≤ H → ∀ x,
      ∫ w, barDivisible w R t x ∂law d ν ≤ C := by
  haveI := hν.prob
  obtain ⟨b, B, _, hB, hb⟩ := exists_meanu_growth_bounds hGrowth d hd hd3 ν hν
  have hHpos : 0 < H := lt_of_lt_of_le one_pos hH
  let a : ℝ := (4 - (d : ℝ)) / 4
  have ha : 0 ≤ a := by
    have : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
    dsimp [a]
    linarith
  refine ⟨B * H ^ a, by positivity, fun R hR t ht x => ?_⟩
  have hRpos : 0 < R := by linarith
  have hn : 2 ≤ ⌊H * R ^ 2⌋₊ :=
    (Nat.le_floor_iff (by positivity)).mpr (by norm_num; nlinarith [sq_nonneg R])
  have hmean := (meanu_monotone d hd ν hν
    (Nat.floor_le_floor (mul_le_mul_of_nonneg_right ht (sq_nonneg R)))).trans (hb _ hn).2
  have hpow : (⌊H * R ^ 2⌋₊ : ℝ) ^ a ≤ (H * R ^ 2) ^ a :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by positivity)) ha
  have hcancel : R ^ ((d : ℝ) / 2 - 2) * (R ^ 2) ^ a = 1 := by
    rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hRpos.le, ← Real.rpow_add hRpos]
    have he : (d : ℝ) / 2 - 2 + (2 : ℕ) * a = 0 := by dsimp [a]; ring
    rw [he, Real.rpow_zero]
  rw [integral_barDivisible_eq hd]
  calc
    R ^ ((d : ℝ) / 2 - 2) * meanu (law d ν) ⌊t * R ^ 2⌋₊
      ≤ R ^ ((d : ℝ) / 2 - 2) * (B * (⌊H * R ^ 2⌋₊ : ℝ) ^ a) :=
        mul_le_mul_of_nonneg_left hmean (Real.rpow_nonneg hRpos.le _)
    _ ≤ R ^ ((d : ℝ) / 2 - 2) * (B * (H * R ^ 2) ^ a) := by gcongr
    _ = B * H ^ a := by
      rw [Real.mul_rpow hHpos.le (sq_nonneg R)]
      calc
        _ = (B * H ^ a) * (R ^ ((d : ℝ) / 2 - 2) * (R ^ 2) ^ a) := by ring
        _ = _ := by rw [hcancel, mul_one]

/-- Joint integrability, followed by a uniform bound for the expected local mass. -/
theorem exists_integral_local_spaceTime_barDivisible_le (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : External.SandpileGrowth) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (K : Set (ℝ × (Fin d → ℝ))) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 2 ≤ R →
      Integrable (fun p : Data d × (ℝ × (Fin d → ℝ)) => barDivisible p.1 R p.2.1 p.2.2)
        ((law d ν).prod (volume.restrict K)) ∧
      Integrable (fun w => ∫ p in K, barDivisible w R p.1 p.2) (law d ν) ∧
      (∫ w, (∫ p in K, barDivisible w R p.1 p.2) ∂law d ν) ≤ C := by
  haveI := hν.prob
  haveI := law_isProb hd ν
  haveI : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top (μ := volume)⟩
  obtain ⟨H, hHK⟩ := hK.exists_bound_of_continuousOn continuous_fst.continuousOn
  obtain ⟨C, hC, hbound⟩ := exists_integral_barDivisible_le hd hd3 hGrowth ν hν
    (H := max H 1) (le_max_right _ _)
  have htime : ∀ p ∈ K, p.1 ≤ max H 1 := fun p hp =>
    (le_abs_self p.1).trans ((hHK p hp).trans (le_max_left _ _))
  refine ⟨volume.real K * C, mul_nonneg ENNReal.toReal_nonneg hC, fun R hR => ?_⟩
  have hRpos : 0 < R := by linarith
  have hmeanmeas : Measurable (fun p : ℝ × (Fin d → ℝ) =>
      ∫ w, barDivisible w R p.1 p.2 ∂law d ν) :=
    ((measurable_uncurry_spaceTime_barDivisible R).comp measurable_swap).stronglyMeasurable.integral_prod_right'.measurable
  have hi : Integrable (fun p : Data d × (ℝ × (Fin d → ℝ)) =>
      barDivisible p.1 R p.2.1 p.2.2) ((law d ν).prod (volume.restrict K)) := by
    apply (integrable_prod_iff' (measurable_uncurry_spaceTime_barDivisible R).aestronglyMeasurable).mpr
    constructor
    · exact ae_of_all _ fun p => (integrable_uOf hd ν hν.integrable_abs ⌊p.1 * R ^ 2⌋₊ (latticePoint R p.2)).const_mul _
    · simp_rw [Real.norm_eq_abs, abs_of_nonneg (barDivisible_nonneg _ hRpos.le _ _)]
      apply Integrable.of_bound hmeanmeas.aestronglyMeasurable C
      filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun w => barDivisible_nonneg w hRpos.le _ _)]
      exact hbound R hR _ (htime p hp) _
  refine ⟨hi, hi.integral_prod_left, ?_⟩
  rw [integral_integral_swap hi]
  calc
    (∫ p in K, ∫ w, barDivisible w R p.1 p.2 ∂law d ν) ≤ ∫ _p in K, C :=
      integral_mono_ae hi.integral_prod_right (integrable_const _)
        ((ae_restrict_mem hK.measurableSet).mono fun p hp => hbound R hR _ (htime p hp) _)
    _ = volume.real K * C := by simp [Measure.real, smul_eq_mul]

end Parking
