import Parking.Support.CoupledMeans
import Parking.Support.MeanLaw
import Parking.Support.MatchedBellman
import Parking.Support.UpperTarget

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Count observables, without the names of individual particles. -/
abbrev CountHistory (d : ℕ) := (ℕ × Site d → ℕ) × (ℕ × Site d → ℕ) × (ℕ × Site d → ℕ)

def countHistory (O : ProcessObservables d) : CountHistory d := (O.1, O.2.1, O.2.2.1)

/-- Configurations and common tables suffice to construct the entire count history. -/
def tableHistory (ω : (Site d → ℤ) × RoundNoise d) : CountHistory d :=
  countHistory (matchedObservables ω.1 0 ω.2)

theorem measurable_countHistory : Measurable (countHistory (d := d)) := by
  exact measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
    (measurable_fst.comp (measurable_snd.comp measurable_snd)))

theorem measurable_tableHistory (hd : 1 ≤ d) : Measurable (tableHistory (d := d)) :=
  measurable_countHistory.comp (measurable_matchedObservables ⟨0, hd⟩ Prod.fst (fun _ => 0) Prod.snd
    measurable_fst measurable_const measurable_snd)

/-- Every count history has the original law when all table priorities are fixed to zero. -/
theorem map_tableHistory (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    ((iidLaw d ν).prod (roundNoiseLaw d)).map tableHistory =
      (law d ν).map (fun ω => countHistory (Parking.stackObservables ω)) := by
  haveI := rankLaw_isProbability d
  haveI := roundNoiseLaw_isProbability hd
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  let Ω := ((Site d → ℤ) × (Label d × ℕ → ℝ)) × RoundNoise d
  have hbase : MeasurePreserving (fun ω : Ω => (ω.1.1, ω.2))
      (((iidLaw d ν).prod (rankLaw d)).prod (roundNoiseLaw d))
      ((iidLaw d ν).prod (roundNoiseLaw d)) :=
    measurePreserving_fst.prod (MeasurePreserving.id _)
  have hm := measurable_matchedObservables ⟨0, hd⟩
    (Ω := Ω) (fun ω => ω.1.1) (fun ω => ω.1.2) Prod.snd
    (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst) measurable_snd
  have h := congrArg (fun μ => μ.map countHistory) (map_matchedObservables hd ν)
  change Measure.map countHistory (Measure.map (fun ω : Ω => matchedObservables ω.1.1 ω.1.2 ω.2) _) =
    Measure.map countHistory (Measure.map (fun ω : Data d => Parking.stackObservables ω) (law d ν)) at h
  have hs : Measurable (fun ω : Data d => Parking.stackObservables ω) :=
    Parking.measurable_stackObservables
  rw [Measure.map_map measurable_countHistory hm,
    Measure.map_map measurable_countHistory hs] at h
  rw [← hbase.map_eq, Measure.map_map (measurable_tableHistory hd) hbase.measurable]
  refine (congrArg (fun f => Measure.map f _) (funext fun ω : Ω => ?_)).trans h
  apply Prod.ext
  · funext tx
    exact (matchedState_counts_priority ω.1.1 0 ω.1.2 ω.2 tx.1).2.2 tx.2
  · apply Prod.ext
    · funext tx
      exact (matchedState_counts_priority ω.1.1 0 ω.1.2 ω.2 tx.1).1 tx.2
    · funext tx
      exact (matchedState_counts_priority ω.1.1 0 ω.1.2 ω.2 tx.1).2.1 tx.2

/-- In particular, each table odometer has the original marginal law. -/
theorem map_tableOdometer (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (T : ℕ) (x : Site d) :
    ((iidLaw d ν).prod (roundNoiseLaw d)).map
        (fun ω => (matchedState ω.1 0 ω.2 T).departures x) =
      (law d ν).map (fun ω => U ω T x) := by
  have h := congrArg (fun μ => μ.map (fun O : CountHistory d => O.1 (T, x))) (map_tableHistory hd ν)
  have hm : Measurable (fun O : CountHistory d => O.1 (T, x)) :=
    (measurable_pi_apply (T, x)).comp measurable_fst
  have hs : Measurable (fun ω : Data d => countHistory (Parking.stackObservables ω)) :=
    measurable_countHistory.comp Parking.measurable_stackObservables
  rw [Measure.map_map hm (measurable_tableHistory hd),
    Measure.map_map hm hs] at h
  exact h

/-- The unconditional finite-horizon table odometer is integrable under a first moment. -/
theorem integrable_tableOdometer (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (T : ℕ) (x : Site d) :
    Integrable (fun ω : (Site d → ℤ) × RoundNoise d => ((matchedState ω.1 0 ω.2 T).departures x : ℝ))
      ((iidLaw d ν).prod (roundNoiseLaw d)) := by
  have hm : Measurable (fun ω : (Site d → ℤ) × RoundNoise d => (matchedState ω.1 0 ω.2 T).departures x) :=
    (measurable_pi_apply (T, x)).comp (measurable_fst.comp (measurable_tableHistory hd))
  have hmap := map_tableOdometer hd ν T x
  have hcast : Measurable (fun n : ℕ => (n : ℝ)) := measurable_from_countable' _
  have hi : Integrable (fun n : ℕ => (n : ℝ)) ((law d ν).map (fun ω => U ω T x)) :=
    (integrable_map_measure hcast.aestronglyMeasurable (measurable_U T x).aemeasurable).mpr
      (integrable_U_law hd ν hint T x)
  rw [← hmap] at hi
  exact (integrable_map_measure hcast.aestronglyMeasurable hm.aemeasurable).mp hi

/-- Averaging the conditional table mean gives the mean of the original process. -/
theorem integral_matchedMeanU (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (T : ℕ) (x : Site d) :
    ∫ η, matchedMeanU η 0 T x ∂(iidLaw d ν) = ∫ ω, (U ω T x : ℝ) ∂(law d ν) := by
  haveI := roundNoiseLaw_isProbability hd
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  have hm : Measurable (fun ω : (Site d → ℤ) × RoundNoise d => (matchedState ω.1 0 ω.2 T).departures x) :=
    (measurable_pi_apply (T, x)).comp (measurable_fst.comp (measurable_tableHistory hd))
  have hcast : Measurable (fun n : ℕ => (n : ℝ)) := measurable_from_countable' _
  rw [show (∫ η, matchedMeanU η 0 T x ∂(iidLaw d ν)) =
    ∫ ω, ((matchedState ω.1 0 ω.2 T).departures x : ℝ) ∂((iidLaw d ν).prod (roundNoiseLaw d)) from
      (integral_prod _ (integrable_tableOdometer hd ν hint T x)).symm]
  rw [← integral_map hm.aemeasurable hcast.aestronglyMeasurable,
    map_tableOdometer hd ν T x]
  exact integral_map (measurable_U T x).aemeasurable hcast.aestronglyMeasurable
end Parking
