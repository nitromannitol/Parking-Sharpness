import Parking.Support.RoundEnumeration
import Parking.Support.MatchedBounds
import Parking.Support.BlockSum

noncomputable section
namespace Parking
open LatticeProb
variable {d : ℕ}

/-- Summing over the enumeration is summing over its finite rectangle. -/
theorem sum_roundEnumeration {α : Type*} [AddCommMonoid α] (x : Site d) (R N : ℕ)
    (f : Site d × ℕ → α) :
    ∑ i, f (roundEnumeration x R N i) = ∑ q ∈ roundEntrySet x R N, f q := by
  exact (Equiv.sum_comp (roundEntrySet x R N).equivFin.symm
    (fun q : roundEntrySet x R N => f q.val)).trans (Finset.sum_coe_sort _ f)

/-- Each used rank is counted exactly once at its departure site. -/
theorem sum_roundEnumeration_used (x : Site d) (R N : ℕ) (A : Site d → ℕ)
    (hA : ∀ y ∈ boxFinset x R, A y ≤ N) (w : Site d → ℝ) :
    (∑ i, if (roundEnumeration x R N i).2 < A (roundEnumeration x R N i).1 then
        w (roundEnumeration x R N i).1 else 0) =
      ∑ y ∈ boxFinset x R, w y * (A y : ℝ) := by
  classical
  rw [sum_roundEnumeration x R N (fun q : Site d × ℕ => if q.2 < A q.1 then w q.1 else 0)]
  unfold roundEntrySet
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro y hy
  dsimp only
  rw [← Finset.sum_filter]
  have he : (Finset.range N).filter (fun j => j < A y) = Finset.range (A y) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    have h := hA y hy
    omega
  rw [he]
  simp [mul_comm]

/-- Departures count all preceding active particles at the site. -/
theorem matchedOdometer_eq_sum (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (T : ℕ) (x : Site d) :
    (matchedState η ρ σ T).departures x = ∑ s ∈ Finset.range T, matchedCount η ρ σ s x := by
  induction T with
  | zero => simp [matchedState, initial]
  | succ T ih =>
      change (matchedState η ρ σ T).departures x + matchedCount η ρ σ T x = _
      rw [Finset.sum_range_succ, ih]

/-- Summing the used-entry weights over rounds charges the final odometer. -/
theorem sum_rounds_used_eq_odometer (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (T : ℕ) (x : Site d) (R N : ℕ)
    (hA : ∀ s < T, ∀ y ∈ boxFinset x R, matchedCount η ρ σ s y ≤ N) (w : Site d → ℝ) :
    (∑ s ∈ Finset.range T, ∑ i,
      if (roundEnumeration x R N i).2 < matchedCount η ρ σ s (roundEnumeration x R N i).1 then
        w (roundEnumeration x R N i).1 else 0) =
      ∑ y ∈ boxFinset x R, w y * ((matchedState η ρ σ T).departures y : ℝ) := by
  classical
  have hs (s : ℕ) (hs : s ∈ Finset.range T) :=
    sum_roundEnumeration_used x R N (matchedCount η ρ σ s) (hA s (Finset.mem_range.mp hs)) w
  rw [Finset.sum_congr rfl hs, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.mul_sum, matchedOdometer_eq_sum, Nat.cast_sum]
end Parking
