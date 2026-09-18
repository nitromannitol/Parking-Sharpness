import Parking.Support.TableHoleLaw
import Parking.Support.SceneryHole

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Bounded initial counts and common rounds determine the whole count history. -/
def clippedRoundHistory (ω : (Site d → ℤ) × RoundNoise d) : CountHistory d := tableHistory (clippedField ω.1, ω.2)

def clippedRoundH (T : ℕ) (x : Site d) (ω : (Site d → ℤ) × RoundNoise d) : ℕ :=
  (matchedState (clippedField ω.1) 0 ω.2 T).holes x

def clippedRoundU (T : ℕ) (x : Site d) (ω : (Site d → ℤ) × RoundNoise d) : ℝ :=
  ((matchedState (clippedField ω.1) 0 ω.2 T).departures x : ℝ)

theorem measurable_clippedRoundHistory (hd : 1 ≤ d) : Measurable (clippedRoundHistory (d := d)) :=
  (measurable_tableHistory hd).comp ((measurable_clippedField.comp measurable_fst).prodMk measurable_snd)

theorem measurable_clippedRoundH (hd : 1 ≤ d) (T : ℕ) (x : Site d) : Measurable (clippedRoundH T x) :=
  ((measurable_pi_apply (T, x)).comp (measurable_snd.comp measurable_snd)).comp (measurable_clippedRoundHistory hd)

theorem measurable_clippedRoundU (hd : 1 ≤ d) (T : ℕ) (x : Site d) : Measurable (clippedRoundU T x) :=
  (measurable_from_countable' fun n : ℕ => (n : ℝ)).comp
    (((measurable_pi_apply (T, x)).comp measurable_fst).comp (measurable_clippedRoundHistory hd))

theorem clippedRoundH_le_one (T : ℕ) (x : Site d) (ω : (Site d → ℤ) × RoundNoise d) : clippedRoundH T x ω ≤ 1 := by
  have h := matchedHoles_le_initial (clippedField ω.1) 0 ω.2 T x
  have hb : -1 ≤ clippedField ω.1 x := (clipSparse_bounds (ω.1 x)).1
  change (matchedState (clippedField ω.1) 0 ω.2 T).holes x ≤ 1
  omega

theorem clippedRoundU_bounds (T : ℕ) (x : Site d) (ω : (Site d → ℤ) × RoundNoise d) :
    0 ≤ clippedRoundU T x ω ∧ clippedRoundU T x ω ≤ ((T * (2 * T + 1) ^ d : ℕ) : ℝ) := by
  refine ⟨Nat.cast_nonneg _, ?_⟩
  apply Nat.cast_le.mpr
  simpa only [mul_one] using matchedOdometer_le_box (clippedField ω.1) 1
    (clippedField_particle_bound ω.1) 0 ω.2 T x

/-- Clipping preserves the joint law of all holes and odometers. -/
theorem map_clippedRoundHistory (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hclip : ∀ᵐ k ∂ν, clipSparse k = k) :
    ((iidLaw d ν).prod (roundNoiseLaw d)).map clippedRoundHistory =
      (law d ν).map (fun ω => countHistory (Parking.stackObservables ω)) := by
  haveI := roundNoiseLaw_isProbability hd
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  have hae : ∀ᵐ ω ∂((iidLaw d ν).prod (roundNoiseLaw d)), clippedField ω.1 = ω.1 :=
    measurePreserving_fst.quasiMeasurePreserving.ae (ae_clippedField ν hclip)
  have he : clippedRoundHistory =ᵐ[((iidLaw d ν).prod (roundNoiseLaw d))] tableHistory := by
    filter_upwards [hae] with ω hω
    change tableHistory (clippedField ω.1, ω.2) = tableHistory ω
    rw [hω]
  exact (Measure.map_congr he).trans (map_tableHistory hd ν)

/-- Every measurable observable of the count history has its original expectation. -/
theorem integral_clippedRoundHistory (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hclip : ∀ᵐ k ∂ν, clipSparse k = k) (F : CountHistory d → ℝ) (hF : Measurable F) :
    (∫ ω, F (clippedRoundHistory ω) ∂((iidLaw d ν).prod (roundNoiseLaw d))) =
      ∫ ω, F (countHistory (Parking.stackObservables ω)) ∂(law d ν) := by
  rw [← integral_map (measurable_clippedRoundHistory hd).aemeasurable hF.aestronglyMeasurable,
    map_clippedRoundHistory hd ν hclip]
  exact integral_map (measurable_countHistory.comp Parking.measurable_stackObservables).aemeasurable hF.aestronglyMeasurable

/-- Every measurable event of the count history has its original probability. -/
theorem measure_clippedRoundHistory (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hclip : ∀ᵐ k ∂ν, clipSparse k = k) (S : Set (CountHistory d)) (hS : MeasurableSet S) :
    ((iidLaw d ν).prod (roundNoiseLaw d)) {ω | clippedRoundHistory ω ∈ S} =
      (law d ν) {ω | countHistory (Parking.stackObservables ω) ∈ S} := by
  have h := congrArg (fun μ => μ S) (map_clippedRoundHistory hd ν hclip)
  have hs : Measurable (fun ω : Data d => countHistory (Parking.stackObservables ω)) :=
    measurable_countHistory.comp Parking.measurable_stackObservables
  rw [Measure.map_apply (measurable_clippedRoundHistory hd) hS,
    Measure.map_apply hs hS] at h
  exact h
end Parking
