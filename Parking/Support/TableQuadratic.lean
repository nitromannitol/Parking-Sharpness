import Parking.Support.TableMomentBounds
import Parking.Support.RoundEnumerationSum
import Parking.Support.GreenSquareSum

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The odometer charge bounding the predictable variance of the reveal martingale. -/
def greenWeightedOdometer (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d)
    (T : ℕ) (x : Site d) (R : ℕ) : ℝ :=
  ∑ v ∈ boxFinset x R, walkOp (fun y => fullGreen d (y - x) ^ 2) v * ((matchedState η ρ σ T).departures v : ℝ)

theorem greenWeightedOdometer_nonneg (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (T : ℕ) (x : Site d) (R : ℕ) : 0 ≤ greenWeightedOdometer η ρ σ T x R :=
  Finset.sum_nonneg fun v _ => mul_nonneg (greenSquareWeight_nonneg x v) (Nat.cast_nonneg _)

/-- The actual chronological predictable variance is bounded by the Green-weighted odometer. -/
theorem tableDiff_qv_le (hd : 3 ≤ d) (base : FlatRoundNoise d)
    (η : Site d → ℤ) (hη : ∀ y, (η y).toNat ≤ 1) (ρ : Label d × ℕ → ℝ)
    (T : ℕ) (x : Site d) (R N : ℕ) (hN : (2 * T + 1) ^ d ≤ N)
    (hK : 0 < (roundEntrySet x R N).card) :
    ∀ᵐ ω ∂(flatRoundNoiseLaw d),
      (∑ i ∈ Finset.Icc 1 (T * (roundEntrySet x R N).card),
        ((flatRoundNoiseLaw d)[fun ζ => tableDiff η ρ T x (roundEnumeration x R N) hK i ζ ^ 2 |
          tableFiltration base (roundEnumeration x R N) (i - 1)]) ω) ≤
        greenWeightedOdometer η ρ (curryRoundNoise ω) T x R := by
  classical
  let K := (roundEntrySet x R N).card
  let e := roundEnumeration x R N
  have ha : ∀ᵐ ω ∂(flatRoundNoiseLaw d), ∀ n : ℕ,
      ((flatRoundNoiseLaw d)[fun ζ => tableDiff η ρ T x e hK (n + 1) ζ ^ 2 |
        tableFiltration base e n]) ω ≤
      (if (e ⟨n % K, Nat.mod_lt n hK⟩).2 < matchedCount η ρ (curryRoundNoise ω) (n / K)
        (e ⟨n % K, Nat.mod_lt n hK⟩).1 then
          walkOp (fun y => fullGreen d (y - x) ^ 2) (e ⟨n % K, Nat.mod_lt n hK⟩).1 else 0) :=
    ae_all_iff.mpr fun n => condExp_tableDiff_sq_le hd base η hη ρ T x e hK n
  filter_upwards [ha] with ω hω
  let f : ℕ → Fin K → ℝ := fun s j =>
    if (e j).2 < matchedCount η ρ (curryRoundNoise ω) s (e j).1 then
      walkOp (fun y => fullGreen d (y - x) ^ 2) (e j).1 else 0
  have hsum : (∑ i ∈ Finset.Icc 1 (T * K),
      ((flatRoundNoiseLaw d)[fun ζ => tableDiff η ρ T x e hK i ζ ^ 2 | tableFiltration base e (i - 1)]) ω) ≤
      ∑ i ∈ Finset.Icc 1 (T * K), f ((i - 1) / K) ⟨(i - 1) % K, Nat.mod_lt _ hK⟩ := by
    apply Finset.sum_le_sum
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have h := hω (i - 1)
    rw [Nat.sub_add_cancel hi1] at h
    exact h
  refine hsum.trans_eq ?_
  rw [sum_Icc_one_eq_range_succ]
  simp only [Nat.add_sub_cancel]
  rw [sum_range_blocks T K hK f]
  apply sum_rounds_used_eq_odometer
  intro s hs y _hy
  exact (matchedCount_one_bound η hη ρ _ s y).trans
    ((Nat.pow_le_pow_left (by omega : 2 * s + 1 ≤ 2 * T + 1) d).trans hN)
end Parking
