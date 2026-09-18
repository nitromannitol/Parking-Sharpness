import Parking.Support.MatchedCounts
import Parking.Support.MatchedLaw

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Round and slot coordinates in a single product space. -/
abbrev FlatRoundNoise (d : ℕ) := ℕ × RoundSlot d → Fin d × Bool

def flatRoundNoiseLaw (d : ℕ) : Measure (FlatRoundNoise d) :=
  Measure.infinitePi fun _ : ℕ × RoundSlot d => stepLaw d

def curryRoundNoise (ω : FlatRoundNoise d) : RoundNoise d := fun t q => ω (t, q)

theorem measurable_curryRoundNoise : Measurable (curryRoundNoise (d := d)) :=
  measurable_pi_lambda _ fun t => measurable_pi_lambda _ fun q => measurable_pi_apply (t, q)

theorem flatRoundNoiseLaw_isProbability (hd : 1 ≤ d) : IsProbabilityMeasure (flatRoundNoiseLaw d) := by
  haveI := stepLaw_isProbability hd
  unfold flatRoundNoiseLaw
  infer_instance

/-- Flattening the independent round tables preserves their law. -/
theorem map_curryRoundNoise (hd : 1 ≤ d) :
    (flatRoundNoiseLaw d).map curryRoundNoise = roundNoiseLaw d := by
  haveI := stepLaw_isProbability hd
  exact Measure.infinitePi_map_curry (fun _ : ℕ => fun _ : RoundSlot d => stepLaw d)

/-- A fresh entry cannot change the state before its round. -/
theorem matchedState_flatUpdate (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (ω : FlatRoundNoise d) (t s : ℕ) (q : RoundSlot d) (a : Fin d × Bool) (ht : t ≤ s) :
    matchedState η ρ (curryRoundNoise (Function.update ω (s, q) a)) t =
      matchedState η ρ (curryRoundNoise ω) t := by
  classical
  apply matchedState_congr
  intro k hk
  funext r
  apply Function.update_of_ne
  intro he
  have hs := congrArg Prod.fst he
  omega

/-- At its own round, a flattened update is exactly a one-slot update. -/
theorem curryRoundNoise_update (ω : FlatRoundNoise d) (s : ℕ) (q : RoundSlot d) (a : Fin d × Bool) :
    curryRoundNoise (Function.update ω (s, q) a) s = Function.update (curryRoundNoise ω s) q a := by
  classical
  funext r
  by_cases hr : r = q
  · subst r; simp [curryRoundNoise]
  · simp [curryRoundNoise, hr]
end Parking
