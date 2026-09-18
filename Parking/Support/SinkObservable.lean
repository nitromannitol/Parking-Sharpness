import Parking.Support.SinkMean
import Parking.Support.FlatMean

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- A real odometer for the process with a fixed finite-horizon sink. -/
def sparseSinkTableU (T : ℕ) (v x : Site d) (z : (Site d → ℤ) × FlatRoundNoise d) : ℝ :=
  ((matchedState (sparseSinkField T v z.1) 0 (curryRoundNoise z.2) T).departures x : ℝ)

theorem sparseSinkTableU_nonneg (T : ℕ) (v x : Site d) (z : (Site d → ℤ) × FlatRoundNoise d) :
    0 ≤ sparseSinkTableU T v x z := Nat.cast_nonneg _

theorem sparseSinkTableU_le (T : ℕ) (v x : Site d) (z : (Site d → ℤ) × FlatRoundNoise d) :
    sparseSinkTableU T v x z ≤ clippedTableU T x z :=
  Nat.cast_le.mpr (sparseSink_odometer_le T v z.1 0 (curryRoundNoise z.2) T x)

theorem sparseSinkTableU_bound (T : ℕ) (v x : Site d) (z : (Site d → ℤ) × FlatRoundNoise d) :
    |sparseSinkTableU T v x z| ≤ ((T * (2 * T + 1) ^ d : ℕ) : ℝ) := by
  rw [abs_of_nonneg (sparseSinkTableU_nonneg T v x z)]
  exact (sparseSinkTableU_le T v x z).trans ((le_abs_self _).trans (clippedTableU_bound T x z))

theorem measurable_sparseSinkTableU (hd : 1 ≤ d) (T : ℕ) (v x : Site d) :
    Measurable (sparseSinkTableU T v x) := by
  have hS := measurableState_matchedState ⟨0, hd⟩
    (fun z : (Site d → ℤ) × FlatRoundNoise d => sparseSinkField T v z.1) (fun _ => 0)
    (fun z => curryRoundNoise z.2) ((measurable_sparseSinkField T v).comp measurable_fst)
    measurable_const (measurable_curryRoundNoise.comp measurable_snd) T
  exact (measurable_from_countable' fun n : ℕ => (n : ℝ)).comp (hS.2.2.2 x)

/-- Integrating a sink table odometer first over its directions gives its conditional mean. -/
theorem integral_sparseSinkTableU (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (T : ℕ) (v x : Site d) :
    ∫ z, sparseSinkTableU T v x z ∂((iidLaw d ν).prod (flatRoundNoiseLaw d)) =
      ∫ η, matchedMeanU (sparseSinkField T v η) 0 T x ∂(iidLaw d ν) := by
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  haveI := flatRoundNoiseLaw_isProbability hd
  have hi : Integrable (sparseSinkTableU T v x) ((iidLaw d ν).prod (flatRoundNoiseLaw d)) :=
    Integrable.of_bound (measurable_sparseSinkTableU hd T v x).aestronglyMeasurable _
      (ae_of_all _ (sparseSinkTableU_bound T v x))
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ fun η => integral_flat_matchedOdometer hd (sparseSinkField T v η) 0 T x

/-- The predictable total number of entrances to the sink. -/
def sparseSinkLambda (T : ℕ) (z : (Site d → ℤ) × FlatRoundNoise d) : ℝ :=
  walkOp (fun x => sparseSinkTableU T 0 x z) 0

theorem sparseSinkLambda_nonneg (T : ℕ) (z : (Site d → ℤ) × FlatRoundNoise d) :
    0 ≤ sparseSinkLambda T z := by
  unfold sparseSinkLambda
  rw [walkOp_eq_nbrFinset]
  exact div_nonneg (Finset.sum_nonneg fun x _ => sparseSinkTableU_nonneg T 0 x z) (by positivity)

theorem measurable_sparseSinkLambda (hd : 1 ≤ d) (T : ℕ) : Measurable (sparseSinkLambda (d := d) T) := by
  change Measurable (fun z => sparseSinkLambda T z)
  simp only [sparseSinkLambda, walkOp_eq_nbrFinset]
  exact (Finset.measurable_sum _ fun x _ => measurable_sparseSinkTableU hd T 0 x).div_const _

theorem sparseSinkLambda_bound (hd : 1 ≤ d) (T : ℕ) (z : (Site d → ℤ) × FlatRoundNoise d) :
    |sparseSinkLambda T z| ≤ ((T * (2 * T + 1) ^ d : ℕ) : ℝ) := by
  rw [abs_of_nonneg (sparseSinkLambda_nonneg T z)]
  exact walkOp_le_of_nbr hd (fun x _ => (le_abs_self _).trans (sparseSinkTableU_bound T 0 x z))

/-- The compensator mean is the neighbor average of the expected sink odometer. -/
theorem integral_sparseSinkLambda (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp4 : p ≤ 1 / 4) (T : ℕ) :
    ∫ z, sparseSinkLambda T z ∂((iidLaw d (threePointLaw p)).prod (flatRoundNoiseLaw d)) =
      walkOp (sparseSinkMean (d := d) p T) 0 := by
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  haveI : IsProbabilityMeasure (iidLaw d (threePointLaw p)) := by unfold iidLaw; infer_instance
  haveI := flatRoundNoiseLaw_isProbability hd
  unfold sparseSinkLambda
  rw [integral_walkOp _ _ _ (fun x _ => Integrable.of_bound (measurable_sparseSinkTableU hd T 0 x).aestronglyMeasurable _
    (ae_of_all _ (sparseSinkTableU_bound T 0 x)))]
  congr 1
  funext x
  exact integral_sparseSinkTableU hd _ T 0 x
end Parking
