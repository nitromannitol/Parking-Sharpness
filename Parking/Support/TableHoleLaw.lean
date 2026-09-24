import Parking.Support.ClippedTable

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Hole counts under common round tables have the original marginal law. -/
theorem map_tableHole (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (T : ℕ) (x : Site d) :
    ((iidLaw d ν).prod (roundNoiseLaw d)).map
        (fun ω => (matchedState ω.1 0 ω.2 T).holes x) =
      (law d ν).map (fun ω => H ω T x) := by
  have h := congrArg (fun μ => μ.map (fun O : CountHistory d => O.2.2 (T, x))) (map_tableHistory hd ν)
  have hm : Measurable (fun O : CountHistory d => O.2.2 (T, x)) :=
    (measurable_pi_apply (T, x)).comp (measurable_snd.comp measurable_snd)
  have hs : Measurable (fun ω : Data d => countHistory (Parking.stackObservables ω)) :=
    measurable_countHistory.comp Parking.measurable_stackObservables
  rw [Measure.map_map hm (measurable_tableHistory hd), Measure.map_map hm hs] at h
  exact h

theorem measurable_clippedTableHole (hd : 1 ≤ d) (T : ℕ) (x : Site d) :
    Measurable (fun z : (Site d → ℤ) × FlatRoundNoise d =>
      (matchedState (clippedField z.1) 0 (curryRoundNoise z.2) T).holes x) :=
  (measurableState_matchedState ⟨0, hd⟩ _ _ _ (measurable_clippedField.comp measurable_fst)
    measurable_const (measurable_curryRoundNoise.comp measurable_snd) T).2.2.1 x

/-- Clipping and flattening preserve the hole-count law as well as the odometer law. -/
theorem map_clippedTableHole (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hclip : ∀ᵐ k ∂ν, clipSparse k = k) (T : ℕ) (x : Site d) :
    ((iidLaw d ν).prod (flatRoundNoiseLaw d)).map
        (fun ω => (matchedState (clippedField ω.1) 0 (curryRoundNoise ω.2) T).holes x) =
      (law d ν).map (fun ω => H ω T x) := by
  have h := map_tableHole hd ν T x
  have hΨ := measurePreserving_clippedTable hd ν hclip
  have hm : Measurable (fun ω : (Site d → ℤ) × RoundNoise d => (matchedState ω.1 0 ω.2 T).holes x) :=
    (measurableState_matchedState ⟨0, hd⟩ Prod.fst (fun _ => 0) Prod.snd
      measurable_fst measurable_const measurable_snd T).2.2.1 x
  rw [← hΨ.map_eq, Measure.map_map hm hΨ.measurable] at h
  exact h

/-- The hole survival probability can be computed with bounded clipped table dynamics. -/
theorem holeProb_eq_clippedTable (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hclip : ∀ᵐ k ∂ν, clipSparse k = k) (T : ℕ) :
    holeProb d ν T = (((iidLaw d ν).prod (flatRoundNoiseLaw d))
      {z | (matchedState (clippedField z.1) 0 (curryRoundNoise z.2) T).holes 0 = 1}).toReal := by
  have h := congrArg (fun μ : Measure ℕ => μ {1}) (map_clippedTableHole hd ν hclip T 0)
  rw [Measure.map_apply (measurable_clippedTableHole hd T 0) (measurableSet_singleton 1),
    Measure.map_apply (measurable_H T 0) (measurableSet_singleton 1)] at h
  exact (congrArg ENNReal.toReal h).symm
end Parking
