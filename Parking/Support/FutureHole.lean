import Parking.Support.HoleMean
import Parking.Support.InstructionUnused
import Parking.Support.RoundMeanField

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The expected final hole count after conditioning on completed rounds. -/
def futureHoleValue (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d)
    (T s : ℕ) (x : Site d) : ℝ := matchedMeanH (matchedRestart η ρ σ s) ρ (T - s) x

theorem futureHoleValue_zero (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d)
    (T : ℕ) (x : Site d) : futureHoleValue η ρ σ T 0 x = matchedMeanH η ρ T x := by
  rw [futureHoleValue, matchedRestart_zero, Nat.sub_zero]

theorem futureHoleValue_terminal (hd : 1 ≤ d) (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (T : ℕ) (x : Site d) :
    futureHoleValue η ρ σ T T x = ((matchedState η ρ σ T).holes x : ℝ) := by
  rw [futureHoleValue, Nat.sub_self, matchedMeanH_zero hd, (matchedRestart_parts η ρ σ T x).2]

theorem futureHoleValue_bounds (hd : 1 ≤ d) (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (T s : ℕ) (x : Site d) :
    0 ≤ futureHoleValue η ρ σ T s x ∧ futureHoleValue η ρ σ T s x ≤ ((-η x).toNat : ℝ) := by
  refine ⟨matchedMeanH_nonneg _ _ _ _, ?_⟩
  have h := matchedMeanH_le_initial hd (matchedRestart η ρ σ s) ρ (T - s) x
  rw [(matchedRestart_parts η ρ σ s x).2] at h
  exact h.trans (Nat.cast_le.mpr (matchedHoles_le_initial η ρ σ s x))

theorem measurable_futureHoleValue (hd : 1 ≤ d) (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) (T s : ℕ) (x : Site d) :
    Measurable (fun σ : RoundNoise d => futureHoleValue η ρ σ T s x) := by
  have hS := measurableState_matchedState ⟨0, hd⟩ (fun _ : RoundNoise d => η) (fun _ => ρ) id
    measurable_const measurable_const measurable_id s
  have hA := measurable_matchedCount ⟨0, hd⟩ (fun _ : RoundNoise d => η) (fun _ => ρ) id
    measurable_const measurable_const measurable_id s
  apply (measurable_matchedMeanH hd ρ (T - s) x).comp
  apply measurable_pi_lambda
  intro y
  exact ((measurable_from_countable' fun n : ℕ => (n : ℤ)).comp ((measurable_pi_apply y).comp hA)).sub
    ((measurable_from_countable' fun n : ℕ => (n : ℤ)).comp (hS.2.2.1 y))

/-- A fresh table determines only the next signed field in the remaining hole value. -/
theorem futureHoleValue_update_succ (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (T s : ℕ) (x : Site d) (τ : RoundSlot d → Fin d × Bool) :
    futureHoleValue η ρ (Function.update σ s τ) T (s + 1) x =
      matchedMeanH (roundSigned (matchedCount η ρ σ s) (matchedState η ρ σ s).holes τ) ρ (T - s - 1) x := by
  rw [futureHoleValue, matchedRestart_succ, matchedCount_update _ _ _ _ _ _ le_rfl,
    matchedState_update _ _ _ _ _ _ le_rfl, Function.update_self]
  congr 1

/-- The conditional future hole count is a bounded martingale in complete rounds. -/
theorem futureHoleValue_bellman (hd : 1 ≤ d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (T s : ℕ) (hs : s < T) (x : Site d) :
    ∫ τ, futureHoleValue η ρ (Function.update σ s τ) T (s + 1) x
      ∂(Measure.infinitePi fun _ : RoundSlot d => stepLaw d) = futureHoleValue η ρ σ T s x := by
  simp_rw [futureHoleValue_update_succ]
  unfold futureHoleValue
  rw [show T - s = (T - s - 1) + 1 by omega, matchedMeanH_bellman hd]
  have hA : (fun y => (matchedRestart η ρ σ s y).toNat) = matchedCount η ρ σ s :=
    funext fun y => (matchedRestart_parts η ρ σ s y).1
  have hH : (fun y => (-(matchedRestart η ρ σ s y)).toNat) = (matchedState η ρ σ s).holes :=
    funext fun y => (matchedRestart_parts η ρ σ s y).2
  rw [hA, hH]
  congr 1
end Parking
