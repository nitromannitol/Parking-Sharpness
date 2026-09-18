import Parking.Support.FlatNoise
import Parking.Support.MeanLaw

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Reshaping independent instructions preserves the conditional odometer mean. -/
theorem integral_flat_matchedOdometer (hd : 1 ≤ d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (T : ℕ) (x : Site d) :
    ∫ ω, ((matchedState η ρ (curryRoundNoise ω) T).departures x : ℝ) ∂(flatRoundNoiseLaw d) =
      matchedMeanU η ρ T x := by
  have hS := measurableState_matchedState ⟨0, hd⟩ (fun _ : RoundNoise d => η) (fun _ => ρ) id
    measurable_const measurable_const measurable_id T
  have hm : Measurable (fun σ : RoundNoise d => ((matchedState η ρ σ T).departures x : ℝ)) :=
    (measurable_from_countable' fun n : ℕ => (n : ℝ)).comp (hS.2.2.2 x)
  have he := integral_map (μ := flatRoundNoiseLaw d) measurable_curryRoundNoise.aemeasurable hm.aestronglyMeasurable
  rw [map_curryRoundNoise hd] at he
  exact he.symm
end Parking
