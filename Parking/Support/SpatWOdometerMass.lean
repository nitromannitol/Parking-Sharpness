/- Integrability and uniform expectation bounds for local rescaled odometer mass. -/
import Parking.Support.SpatWWalkGrid
import Parking.Support.SceneryCenter
import Parking.Frozen.Growth
open Set Filter Topology LatticeProb MeasureTheory
noncomputable section
namespace Parking
variable {d : ℕ}

/-- Joint measurability of the rescaled parking odometer in the sample and spatial point. -/
theorem measurable_uncurry_barOdometer (R t : ℝ) :
    Measurable (fun p : Data d × (Fin d → ℝ) => barOdometer p.1 R t p.2) := by
  let n := ⌊t * R ^ 2⌋₊
  have hq : Measurable (fun p : Data d × (Fin d → ℝ) => latticePoint R p.2) :=
    (measurable_pi_lambda _ (fun i => Int.measurable_floor.comp
      (measurable_const.mul (measurable_pi_apply i)))).comp measurable_snd
  have hf : ∀ y : Site d, Measurable (fun p : Data d × (Fin d → ℝ) => (U p.1 n y : ℝ)) :=
    fun y => ((measurable_from_countable' fun k : ℕ => (k : ℝ)).comp (measurable_U n y)).comp measurable_fst
  have hj := measurable_eval_var (fun p : Data d × (Fin d → ℝ) => latticePoint R p.2) hq
    (fun p y => (U p.1 n y : ℝ)) hf
  exact hj.const_mul _

/-- The rescaled parking odometer is nonnegative at nonnegative scales. -/
theorem barOdometer_nonneg (w : Data d) {R : ℝ} (hR : 0 ≤ R) (t : ℝ) (x : Fin d → ℝ) :
    0 ≤ barOdometer w R t x := by
  unfold barOdometer
  positivity

/-- Translation invariance identifies every rescaled one-point mean. -/
theorem integral_barOdometer_eq (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (R t : ℝ) (x : Fin d → ℝ) :
    ∫ w, barOdometer w R t x ∂law d ν =
      R ^ ((d : ℝ) / 2 - 2) * meanU (law d ν) ⌊t * R ^ 2⌋₊ := by
  unfold barOdometer
  rw [integral_const_mul, integral_U_shift hd]

/-- The rescaled odometer is integrable jointly on a compact spatial set and the sample space. -/
theorem integrable_uncurry_barOdometer (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    {R : ℝ} (hR : 0 ≤ R) (t : ℝ) (K : Set (Fin d → ℝ)) (hK : IsCompact K) :
    Integrable (fun p : Data d × (Fin d → ℝ) => barOdometer p.1 R t p.2)
      ((law d ν).prod (volume.restrict K)) := by
  haveI := law_isProb hd ν
  haveI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  apply (integrable_prod_iff' (measurable_uncurry_barOdometer R t).aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun x => (integrable_U_law hd ν hint ⌊t * R ^ 2⌋₊ (latticePoint R x)).const_mul _
  · have heq : (fun x => ∫ w, ‖barOdometer w R t x‖ ∂law d ν) =
        fun _ : Fin d → ℝ => R ^ ((d : ℝ) / 2 - 2) * meanU (law d ν) ⌊t * R ^ 2⌋₊ := by
      funext x
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (barOdometer_nonneg _ hR _ _)]
      exact integral_barOdometer_eq hd ν R t x
    rw [heq]
    exact integrable_const _

/-- Fubini identifies the expected local mass, with integrability included. -/
theorem integral_local_barOdometer_eq (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    {R : ℝ} (hR : 0 ≤ R) (t : ℝ) (K : Set (Fin d → ℝ)) (hK : IsCompact K) :
    Integrable (fun w => ∫ x in K, barOdometer w R t x) (law d ν) ∧
      (∫ w, (∫ x in K, barOdometer w R t x) ∂law d ν) =
        volume.real K * (R ^ ((d : ℝ) / 2 - 2) * meanU (law d ν) ⌊t * R ^ 2⌋₊) := by
  haveI := law_isProb hd ν
  have hi := integrable_uncurry_barOdometer hd ν hint hR t K hK
  refine ⟨hi.integral_prod_left, ?_⟩
  rw [integral_integral_swap hi]
  simp_rw [integral_barOdometer_eq hd ν R t]
  simp [Measure.real, smul_eq_mul]

/-- The growth theorem bounds the expected local rescaled mass uniformly in large scales. -/
theorem exists_integral_local_barOdometer_le (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : External.SandpileGrowth) (hBernstein : External.Bernstein)
    (hConcentration : External.UConcentration) (hGreenNorms : External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν)
    (K : Set (Fin d → ℝ)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 2 ≤ R →
      Integrable (fun w => ∫ x in K, barOdometer w R 1 x) (law d ν) ∧
        (∫ w, (∫ x in K, barOdometer w R 1 x) ∂law d ν) ≤ C := by
  haveI := hν.prob
  obtain ⟨c, C, hc, hcC, hmean, _⟩ :=
    (Frozen.growth hGrowth hBernstein hConcentration hGreenNorms d hd ν hν).1 hd3
  have hC : 0 ≤ C := hc.le.trans hcC
  refine ⟨volume.real K * C, mul_nonneg ENNReal.toReal_nonneg hC, fun R hR => ?_⟩
  have hRpos : 0 < R := by linarith
  obtain ⟨hi, heq⟩ := integral_local_barOdometer_eq hd ν hν.integrable_abs hRpos.le 1 K hK
  refine ⟨hi, ?_⟩
  rw [heq, one_mul]
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  have ht2 : 2 ≤ ⌊R ^ 2⌋₊ := (Nat.le_floor_iff (by positivity)).mpr (by norm_num; nlinarith)
  have hmeanBound := (hmean ⌊R ^ 2⌋₊ ht2).2
  have htR : (⌊R ^ 2⌋₊ : ℝ) ≤ R ^ 2 := Nat.floor_le (by positivity)
  have hexp : 0 ≤ (4 - (d : ℝ)) / 4 := by
    have hd3' : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
    linarith
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg ⌊R ^ 2⌋₊) htR hexp
  have hcancel : R ^ ((d : ℝ) / 2 - 2) * (R ^ 2) ^ ((4 - (d : ℝ)) / 4) = 1 := by
    rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hRpos.le, ← Real.rpow_add hRpos]
    ring_nf
    simp
  calc
    R ^ ((d : ℝ) / 2 - 2) * meanU (law d ν) ⌊R ^ 2⌋₊ ≤
        R ^ ((d : ℝ) / 2 - 2) * (C * (⌊R ^ 2⌋₊ : ℝ) ^ ((4 - (d : ℝ)) / 4)) :=
      mul_le_mul_of_nonneg_left hmeanBound (Real.rpow_nonneg hRpos.le _)
    _ ≤ R ^ ((d : ℝ) / 2 - 2) * (C * (R ^ 2) ^ ((4 - (d : ℝ)) / 4)) := by gcongr
    _ = C := by rw [mul_left_comm, hcancel, mul_one]
end Parking
