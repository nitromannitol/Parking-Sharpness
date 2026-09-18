import Parking.Support.TableReads
import Parking.Support.MatchedUniform

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d K : ℕ}

/-- The count bound needed in each conditional current-round estimate. -/
theorem matchedCount_one_bound (η : Site d → ℤ) (hη : ∀ y, (η y).toNat ≤ 1)
    (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (s : ℕ) :
    ∀ y, matchedCount η ρ σ s y ≤ (2 * s + 1) ^ d := by
  intro y
  simpa only [mul_one] using matchedCount_le_box η 1 hη ρ σ s y

/-- Every chronological reveal increment is bounded by the Green function at zero. -/
theorem abs_tableDiff_le (hd : 3 ≤ d) (η : Site d → ℤ) (hη : ∀ y, (η y).toNat ≤ 1)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d)
    (e : Fin K ↪ Site d × ℕ) (hK : 0 < K) (n : ℕ) (ω : FlatRoundNoise d) :
    |tableDiff η ρ T x e hK n ω| ≤ escapeConst d := by
  cases n with
  | zero => rw [tableDiff_zero, abs_zero]; exact zero_le_one.trans (one_le_escapeConst hd)
  | succ n =>
      have h := (roundDiff_section_bounds hd e (matchedCount η ρ (curryRoundNoise ω) (n / K))
        (matchedState η ρ (curryRoundNoise ω) (n / K)).holes ((2 * (n / K) + 1) ^ d)
        (matchedCount_one_bound η hη ρ _ _) ρ (T - n / K - 1) x
        ⟨n % K, Nat.mod_lt n hK⟩ (curryRoundNoise ω (n / K))).1
          ((curryRoundNoise ω (n / K)) (Sum.inl (e ⟨n % K, Nat.mod_lt n hK⟩)))
      simpa only [Function.update_eq_self, tableDiff_succ] using h

/-- The reveal increment and its square are integrable. -/
theorem integrable_tableDiff (hd : 3 ≤ d) (η : Site d → ℤ) (hη : ∀ y, (η y).toNat ≤ 1)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d)
    (e : Fin K ↪ Site d × ℕ) (hK : 0 < K) (n : ℕ) :
    Integrable (tableDiff η ρ T x e hK n) (flatRoundNoiseLaw d) ∧
      Integrable (fun ω => tableDiff η ρ T x e hK n ω ^ 2) (flatRoundNoiseLaw d) := by
  haveI := flatRoundNoiseLaw_isProbability (by omega : 1 ≤ d)
  have hm := measurable_tableDiff (by omega) η ρ T x e hK n
  have hb := abs_tableDiff_le hd η hη ρ T x e hK n
  constructor
  · exact Integrable.of_bound hm.aestronglyMeasurable _ (ae_of_all _ hb)
  · apply Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable (escapeConst d ^ 2)
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb ω) 2

/-- Conditional mean zero for the actual chronological process increments. -/
theorem condExp_tableDiff_zero (hd : 3 ≤ d) (base : FlatRoundNoise d)
    (η : Site d → ℤ) (hη : ∀ y, (η y).toNat ≤ 1) (ρ : Label d × ℕ → ℝ)
    (T : ℕ) (x : Site d) (e : Fin K ↪ Site d × ℕ) (hK : 0 < K) (n : ℕ) :
    (flatRoundNoiseLaw d)[tableDiff η ρ T x e hK (n + 1) | tableFiltration base e n] =ᵐ[flatRoundNoiseLaw d] 0 := by
  have hd1 : 1 ≤ d := by omega
  haveI := stepLaw_isProbability hd1
  apply condExp_zero_of_fresh_coordinate (fun _ : ℕ × RoundSlot d => stepLaw d) base
    (blockReveal (slotEnumeration e) n) (n / K, Sum.inl (e ⟨n % K, Nat.mod_lt n hK⟩))
    (notMem_blockReveal_next (slotEnumeration e) hK n) _ (measurable_tableDiff hd1 η ρ T x e hK (n + 1))
    (integrable_tableDiff hd η hη ρ T x e hK (n + 1)).1 (tableDiff_reads η ρ T x e hK n)
  intro ω
  simp_rw [tableDiff_update]
  exact roundDiff_section_zero hd1 e _ _ ((2 * (n / K) + 1) ^ d)
    (matchedCount_one_bound η hη ρ _ _) ρ _ x _ _

/-- The predictable variance is charged only for a used entry, with weight PG² at its departure site. -/
theorem condExp_tableDiff_sq_le (hd : 3 ≤ d) (base : FlatRoundNoise d)
    (η : Site d → ℤ) (hη : ∀ y, (η y).toNat ≤ 1) (ρ : Label d × ℕ → ℝ)
    (T : ℕ) (x : Site d) (e : Fin K ↪ Site d × ℕ) (hK : 0 < K) (n : ℕ) :
    (flatRoundNoiseLaw d)[fun ω => tableDiff η ρ T x e hK (n + 1) ω ^ 2 | tableFiltration base e n] ≤ᵐ[flatRoundNoiseLaw d]
      (fun ω => let j : Fin K := ⟨n % K, Nat.mod_lt n hK⟩
        if (e j).2 < matchedCount η ρ (curryRoundNoise ω) (n / K) (e j).1 then
          walkOp (fun y => fullGreen d (y - x) ^ 2) (e j).1 else 0) := by
  have hd1 : 1 ≤ d := by omega
  haveI := stepLaw_isProbability hd1
  have hc := condExp_eq_coordinate_integral (fun _ : ℕ × RoundSlot d => stepLaw d) base
    (blockReveal (slotEnumeration e) n) (n / K, Sum.inl (e ⟨n % K, Nat.mod_lt n hK⟩))
    (notMem_blockReveal_next (slotEnumeration e) hK n)
    (fun ω => tableDiff η ρ T x e hK (n + 1) ω ^ 2)
    ((measurable_tableDiff hd1 η ρ T x e hK (n + 1)).pow_const 2)
    (integrable_tableDiff hd η hη ρ T x e hK (n + 1)).2
    (fun ω ω' hω => congrArg (fun r : ℝ => r ^ 2) (tableDiff_reads η ρ T x e hK n ω ω' hω))
  filter_upwards [hc] with ω hω
  change (flatRoundNoiseLaw d)[fun ω => tableDiff η ρ T x e hK (n + 1) ω ^ 2 |
    tableFiltration base e n] ω = _ at hω
  rw [hω]
  simp_rw [tableDiff_update]
  exact (roundDiff_section_bounds hd e _ _ ((2 * (n / K) + 1) ^ d)
    (matchedCount_one_bound η hη ρ _ _) ρ _ x _ _).2
end Parking
