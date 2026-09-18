/-
The level-`0` base term of route A: the maximum of `Parking.Yfield` over the level-`0` grid
(spacing `1`) inside a box of coordinate radius `R`, a genuine `Finset.sup'` over
`LatticeProb.boxIdx R 0` — `(2R+1)^2` points, POLYNOMIAL in `R` (unlike the level-`n1` grid,
which has `Θ(4^{n1})` points).  Its `p`-th moment is bounded by `card · M` via the SAME
per-point moment bound `Parking.exists_Yfield_moment` already used throughout
`TightBoxSupMoment.lean`.  Combined with `TightBoxSupBase.lean`'s finite telescoping bound, this
gives `|Yfield(dtruncPi R z)| ≤ level0Max R + 2·(telescoping sum)` for every `z` with
`∀ i, |z i| ≤ R`.
-/
import Parking.Support.TightBoxSupBase

open MeasureTheory LatticeProb Filter Topology

noncomputable section

namespace Parking

theorem boxIdx_zero_nonempty (R : ℕ) : (LatticeProb.boxIdx (k := 2) R 0).Nonempty := by
  refine ⟨0, ?_⟩
  rw [LatticeProb.mem_boxIdx_iff]
  intro i
  simp

/-- **The maximum of `Yfield` over the level-`0` grid of the box of coordinate radius `R`.** -/
def level0Max (A : ℝ) (hA : 0 ≤ A) (R n : ℕ) (η : Site 2 → ℝ) : ℝ :=
  (LatticeProb.boxIdx (k := 2) R 0).sup' (boxIdx_zero_nonempty R)
    (fun j => |Yfield A hA n η (LatticeProb.gridPt 0 j)|)

theorem level0Max_nonneg (A : ℝ) (hA : 0 ≤ A) (R n : ℕ) (η : Site 2 → ℝ) :
    0 ≤ level0Max A hA R n η := by
  obtain ⟨j, hj⟩ := boxIdx_zero_nonempty R
  exact le_trans (abs_nonneg _) (Finset.le_sup' (fun j => |Yfield A hA n η (LatticeProb.gridPt 0 j)|) hj)

/-- **`|Yfield(dtruncPi 0 z)| ≤ level0Max R`, for every `z` with `∀ i, |z i| ≤ R`.** -/
theorem abs_Yfield_dtruncPi_zero_le (A : ℝ) (hA : 0 ≤ A) (n R : ℕ) (η : Site 2 → ℝ)
    {z : Fin 2 → ℝ} (hz : ∀ i, |z i| ≤ (R : ℝ)) :
    |Yfield A hA n η (LatticeProb.dtruncPi 0 z)| ≤ level0Max A hA R n η := by
  set j : Fin 2 → ℤ := fun i => ⌊z i * 2 ^ (0:ℕ)⌋ with hjdef
  have hjmem : j ∈ LatticeProb.boxIdx (k := 2) R 0 := by
    rw [LatticeProb.mem_boxIdx_iff]
    intro i
    have hb : |j i| ≤ (R:ℤ) * 2 ^ (0:ℕ) := floor_range_fixed (R := R) (m := 0) (hz i)
    push_cast at hb ⊢
    linarith [hb]
  have heq : LatticeProb.dtruncPi 0 z = LatticeProb.gridPt 0 j := rfl
  rw [heq]
  exact Finset.le_sup' (fun j => |Yfield A hA n η (LatticeProb.gridPt 0 j)|) hjmem

theorem measurable_level0Max (A : ℝ) (hA : 0 ≤ A) (R n : ℕ) :
    Measurable (fun η : Site 2 → ℝ => level0Max A hA R n η) := by
  have heq : (fun η : Site 2 → ℝ => level0Max A hA R n η) =
      (LatticeProb.boxIdx (k := 2) R 0).sup' (boxIdx_zero_nonempty R)
        (fun j (η : Site 2 → ℝ) => |Yfield A hA n η (LatticeProb.gridPt 0 j)|) := by
    funext η
    rw [level0Max, Finset.sup'_apply]
  rw [heq]
  apply Finset.measurable_sup'
  intro j _
  exact (measurable_Yfield hA n (LatticeProb.gridPt 0 j)).abs

theorem card_boxIdx_zero (R : ℕ) :
    ((LatticeProb.boxIdx (k := 2) R 0).card : ℝ) = (2 * (R : ℝ) + 1) ^ 2 := by
  rw [LatticeProb.card_boxIdx]
  push_cast
  ring

/-- **The `p`-th moment of `level0Max R` is bounded by `M · (2R+1)^2`, uniform in `n`.** -/
theorem exists_level0Max_moment (ν : Measure ℤ) (hν : CriticalLaw ν) (p : ℝ) (hp2 : 2 ≤ p) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (A : ℝ) (hA : 0 ≤ A) (R n : ℕ), 1 ≤ n →
      Integrable (fun η : Site 2 → ℝ => (level0Max A hA R n η) ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, (level0Max A hA R n η) ^ p ∂(iidLaw 2 (realLaw ν))) ≤
        M * (2 * (R:ℝ) + 1) ^ 2 := by
  obtain ⟨M0, hM0, hb⟩ := exists_Yfield_moment ν hν p hp2
  refine ⟨M0, hM0, fun A hA R n hn => ?_⟩
  have hterm : ∀ j ∈ LatticeProb.boxIdx (k := 2) R 0,
      Integrable (fun η => |Yfield A hA n η (LatticeProb.gridPt 0 j)| ^ p)
        (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, |Yfield A hA n η (LatticeProb.gridPt 0 j)| ^ p
          ∂(iidLaw 2 (realLaw ν))) ≤ M0 := fun j _ => hb A hA n hn (LatticeProb.gridPt 0 j)
  have hintSum : Integrable (fun η : Site 2 → ℝ =>
      ∑ j ∈ LatticeProb.boxIdx (k := 2) R 0, |Yfield A hA n η (LatticeProb.gridPt 0 j)| ^ p)
      (iidLaw 2 (realLaw ν)) :=
    integrable_finsetSum (LatticeProb.boxIdx (k := 2) R 0) fun j hj => (hterm j hj).1
  have hmeasPow : Measurable (fun η : Site 2 → ℝ => (level0Max A hA R n η) ^ p) := by
    have heq : (fun η : Site 2 → ℝ => (level0Max A hA R n η) ^ p) =
        (fun η : Site 2 → ℝ => |level0Max A hA R n η| ^ p) := by
      funext η
      rw [abs_of_nonneg (level0Max_nonneg A hA R n η)]
    rw [heq]
    exact LatticeProb.measurable_abs_rpow (measurable_level0Max A hA R n) p
  have hrpow_le : ∀ η : Site 2 → ℝ, (level0Max A hA R n η) ^ p ≤
      ∑ j ∈ LatticeProb.boxIdx (k := 2) R 0, |Yfield A hA n η (LatticeProb.gridPt 0 j)| ^ p := by
    intro η
    obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_sup' (boxIdx_zero_nonempty R)
      (fun j => |Yfield A hA n η (LatticeProb.gridPt 0 j)|)
    rw [level0Max, heq]
    exact Finset.single_le_sum
      (f := fun j => |Yfield A hA n η (LatticeProb.gridPt 0 j)| ^ p)
      (fun j _ => Real.rpow_nonneg (abs_nonneg _) p) hj
  have hintPow : Integrable (fun η : Site 2 → ℝ => (level0Max A hA R n η) ^ p)
      (iidLaw 2 (realLaw ν)) := by
    refine hintSum.mono' hmeasPow.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun η => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (level0Max_nonneg A hA R n η) p)]
    exact hrpow_le η
  refine ⟨hintPow, ?_⟩
  calc (∫ η : Site 2 → ℝ, (level0Max A hA R n η) ^ p ∂(iidLaw 2 (realLaw ν)))
      ≤ ∫ η : Site 2 → ℝ, ∑ j ∈ LatticeProb.boxIdx (k := 2) R 0,
          |Yfield A hA n η (LatticeProb.gridPt 0 j)| ^ p ∂(iidLaw 2 (realLaw ν)) :=
        integral_mono_ae hintPow hintSum (Filter.Eventually.of_forall hrpow_le)
    _ = ∑ j ∈ LatticeProb.boxIdx (k := 2) R 0, ∫ η : Site 2 → ℝ,
          |Yfield A hA n η (LatticeProb.gridPt 0 j)| ^ p ∂(iidLaw 2 (realLaw ν)) :=
        integral_finsetSum (LatticeProb.boxIdx (k := 2) R 0) fun j hj => (hterm j hj).1
    _ ≤ ∑ _j ∈ LatticeProb.boxIdx (k := 2) R 0, M0 :=
        Finset.sum_le_sum fun j hj => (hterm j hj).2
    _ = ((LatticeProb.boxIdx (k := 2) R 0).card : ℝ) * M0 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = M0 * (2 * (R:ℝ) + 1) ^ 2 := by
        rw [card_boxIdx_zero]; ring

end Parking

end
