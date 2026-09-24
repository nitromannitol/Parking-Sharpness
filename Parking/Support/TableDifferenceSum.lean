import Parking.Support.TableDifference
import Parking.Support.RoundDifferenceSum
import Parking.Support.FutureValue
import Parking.Support.BlockSum
import Parking.Support.MatchedUniform

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d K : ℕ}

/-- The constructed chronological martingale sums to the odometer minus its conditional mean. -/
theorem sum_tableDiff (hd : 1 ≤ d) (η : Site d → ℤ) (hη : ∀ y, (η y).toNat ≤ 1)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) (e : Fin K ↪ Site d × ℕ) (hK : 0 < K)
    (hcover : ∀ y ∈ boxFinset x T, ∀ j < (2 * T + 1) ^ d, ∃ i, e i = (y, j))
    (ω : FlatRoundNoise d) :
    ∑ n ∈ Finset.Icc 1 (T * K), tableDiff η ρ T x e hK n ω =
      ((matchedState η ρ (curryRoundNoise ω) T).departures x : ℝ) - matchedMeanU η ρ T x := by
  let σ := curryRoundNoise ω
  let f : ℕ → Fin K → ℝ := fun s j => roundDiff e (matchedCount η ρ σ s)
    (matchedState η ρ σ s).holes ρ (T - s - 1) x j (σ s)
  rw [sum_Icc_one_eq_range_succ]
  simp only [tableDiff_succ]
  change (∑ n ∈ Finset.range (T * K), f (n / K) ⟨n % K, Nat.mod_lt n hK⟩) = _
  rw [sum_range_blocks T K hK f]
  have hround (s : ℕ) (hs : s ∈ Finset.range T) :
      (∑ j : Fin K, f s j) = futureValue η ρ σ T (s + 1) x - futureValue η ρ σ T s x := by
    have hsT : s < T := Finset.mem_range.mp hs
    have hA : ∀ y, matchedCount η ρ σ s y ≤ (2 * T + 1) ^ d := by
      intro y
      have h := matchedCount_le_box η 1 hη ρ σ s y
      simp only [mul_one] at h
      exact h.trans (Nat.pow_le_pow_left (by omega) d)
    have hc : ∀ y ∈ boxFinset x (T - s - 1 + 1), ∀ j < (2 * T + 1) ^ d, ∃ i, e i = (y, j) := by
      intro y hy j hj
      exact hcover y (boxFinset_mono (by omega) hy) j hj
    have h := sum_roundDiff hd e (matchedCount η ρ σ s) (matchedState η ρ σ s).holes
      ((2 * T + 1) ^ d) hA ρ (T - s - 1) x hc (σ s)
    change _ = _ at h
    change (∑ j : Fin K, roundDiff e (matchedCount η ρ σ s)
      (matchedState η ρ σ s).holes ρ (T - s - 1) x j (σ s)) = _
    rw [h, futureValue_succ, futureValue_bellman hd η ρ σ T s hsT x]
    ring
  rw [Finset.sum_congr rfl hround,
    Finset.sum_range_sub (fun s => futureValue η ρ σ T s x) T,
    futureValue_terminal, futureValue_zero]
end Parking
