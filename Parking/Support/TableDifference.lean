import Parking.Support.RoundDifference
import Parking.Support.FlatNoise
import Parking.Support.ProductFresh

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d K : ℕ}

/-- The chronological reveal increment, indexed from one. -/
def tableDiff (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d)
    (e : Fin K ↪ Site d × ℕ) (hK : 0 < K) (n : ℕ) (ω : FlatRoundNoise d) : ℝ :=
  if n = 0 then 0 else
    roundDiff e (matchedCount η ρ (curryRoundNoise ω) ((n - 1) / K))
      (matchedState η ρ (curryRoundNoise ω) ((n - 1) / K)).holes ρ
      (T - (n - 1) / K - 1) x ⟨(n - 1) % K, Nat.mod_lt _ hK⟩
      (curryRoundNoise ω ((n - 1) / K))

theorem tableDiff_zero (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d)
    (e : Fin K ↪ Site d × ℕ) (hK : 0 < K) (ω : FlatRoundNoise d) :
    tableDiff η ρ T x e hK 0 ω = 0 := by simp [tableDiff]

theorem tableDiff_succ (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d)
    (e : Fin K ↪ Site d × ℕ) (hK : 0 < K) (n : ℕ) (ω : FlatRoundNoise d) :
    tableDiff η ρ T x e hK (n + 1) ω =
      roundDiff e (matchedCount η ρ (curryRoundNoise ω) (n / K))
        (matchedState η ρ (curryRoundNoise ω) (n / K)).holes ρ (T - n / K - 1) x
        ⟨n % K, Nat.mod_lt n hK⟩ (curryRoundNoise ω (n / K)) := by
  simp [tableDiff]

/-- The reveal increment is measurable in all the independent table entries. -/
theorem measurable_tableDiff (hd : 1 ≤ d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (T : ℕ) (x : Site d) (e : Fin K ↪ Site d × ℕ) (hK : 0 < K) (n : ℕ) :
    Measurable (tableDiff η ρ T x e hK n) := by
  cases n with
  | zero =>
      change Measurable (fun ω => tableDiff η ρ T x e hK 0 ω)
      simp only [tableDiff_zero]
      exact measurable_const
  | succ n =>
      have hS := measurableState_matchedState ⟨0, hd⟩ (fun _ : FlatRoundNoise d => η)
        (fun _ => ρ) curryRoundNoise measurable_const measurable_const measurable_curryRoundNoise (n / K)
      have hA := measurable_matchedCount ⟨0, hd⟩ (fun _ : FlatRoundNoise d => η)
        (fun _ => ρ) curryRoundNoise measurable_const measurable_const measurable_curryRoundNoise (n / K)
      change Measurable (fun ω => tableDiff η ρ T x e hK (n + 1) ω)
      simp only [tableDiff_succ]
      exact measurable_roundDiff hd e _ _ _ hA (measurable_pi_lambda _ hS.2.2.1)
        ((measurable_pi_apply (n / K)).comp measurable_curryRoundNoise) ρ _ x _

/-- Updating the fresh coordinate changes only the current table in the reveal increment. -/
theorem tableDiff_update (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d)
    (e : Fin K ↪ Site d × ℕ) (hK : 0 < K) (n : ℕ) (ω : FlatRoundNoise d) (a : Fin d × Bool) :
    let j : Fin K := ⟨n % K, Nat.mod_lt n hK⟩
    tableDiff η ρ T x e hK (n + 1) (Function.update ω (n / K, Sum.inl (e j)) a) =
      roundDiff e (matchedCount η ρ (curryRoundNoise ω) (n / K))
        (matchedState η ρ (curryRoundNoise ω) (n / K)).holes ρ (T - n / K - 1) x j
        (Function.update (curryRoundNoise ω (n / K)) (Sum.inl (e j)) a) := by
  dsimp only
  rw [tableDiff_succ, curryRoundNoise_update,
    matchedState_flatUpdate η ρ ω (n / K) (n / K) _ a le_rfl]
  have hA : matchedCount η ρ (curryRoundNoise (Function.update ω
      (n / K, Sum.inl (e ⟨n % K, Nat.mod_lt n hK⟩)) a)) (n / K) =
      matchedCount η ρ (curryRoundNoise ω) (n / K) := by
    funext y
    unfold matchedCount
    rw [matchedState_flatUpdate η ρ ω (n / K) (n / K) _ a le_rfl]
  rw [hA]
end Parking
