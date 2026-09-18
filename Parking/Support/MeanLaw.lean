import Parking.Support.SingleMean
import Parking.Support.MatchedPriority
import Parking.Support.MatchedLaw

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Expected common-table odometers are independent of all priorities. -/
theorem matchedMeanU_priority (η : Site d → ℤ) (ρ ρ' : Label d × ℕ → ℝ)
    (T : ℕ) (x : Site d) : matchedMeanU η ρ T x = matchedMeanU η ρ' T x := by
  apply integral_congr_ae
  exact ae_of_all _ fun σ => congrArg (fun k : ℕ => (k : ℝ)) ((matchedState_counts_priority η ρ ρ' σ T).2.2 x)

/-- The conditional mean odometer is measurable as a function of the initial field. -/
theorem measurable_matchedMeanU (hd : 1 ≤ d) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) :
    Measurable (fun η : Site d → ℤ => matchedMeanU η ρ T x) := by
  haveI := roundNoiseLaw_isProbability hd
  have hS := measurableState_matchedState ⟨0, hd⟩
    (Ω := (Site d → ℤ) × RoundNoise d) Prod.fst (fun _ => ρ) Prod.snd
    measurable_fst measurable_const measurable_snd T
  exact ((measurable_from_countable' fun k : ℕ => (k : ℝ)).comp
    (hS.2.2.2 x)).stronglyMeasurable.integral_prod_right'.measurable

/-- The table expectation is the particle-driver expectation, for each fixed configuration and priorities. -/
theorem matchedMeanU_eq_integral_pOdometer (hd : 1 ≤ d) (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) :
    matchedMeanU η ρ T x = ∫ m, (pOdometer ⟨η, m, ρ⟩ T x : ℝ) ∂(moveLaw d) := by
  have hme : Measurable (matchedMoves η ρ) :=
    measurable_matchedMoves ⟨0, hd⟩ (fun _ => η) (fun _ => ρ) id
      measurable_const measurable_const measurable_id
  have hS := measurableState_pState (Ω := Label d × ℕ → Fin d × Bool)
    (fun _ => η) id (fun _ => ρ) measurable_const measurable_id measurable_const T
  have hf : Measurable (fun m => (pOdometer ⟨η, m, ρ⟩ T x : ℝ)) :=
    (measurable_from_countable' fun k : ℕ => (k : ℝ)).comp (hS.2.2.2 x)
  rw [← map_matchedMoves hd η ρ, integral_map hme.aemeasurable hf.aestronglyMeasurable]
  unfold matchedMeanU
  apply integral_congr_ae
  apply ae_of_all
  intro σ
  simp only [pOdometer, pState_matchedMoves]
end Parking
