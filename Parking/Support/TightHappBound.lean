/-
The per-scenery comparison `happ` needs, carried out in full: a bound on
`|n^{-1/4} u⃗_n(0) - Y' A n η|` (the potential-inclusive form of `Parking.Y`, read directly at
the scenery `η` rather than at the driving data `w`), UNIFORM over the scenery, in terms of the
walk's own bad event `{p | ∃ k ≤ n, 4A√n ≤ |Parking.walkPartialSum k p|}` (`TightWalkMaximal.lean`)
and the two quantities that control it off that event: the walk's own maximal potential
functional `Parking.orientedMax` (the odometer side) and the box-clamped reward field's sup norm
`‖Parking.boxRewardMap ...‖` (the reward-field side).

The Dynkin decomposition `Parking.uOriented_eq_potential_add_stoppingSup` and the origin value of
`Parking.orientedCutoffValuePot` both carry the SAME potential term `n^{-1/4}Φ_n(0)`, which
cancels: `n^{-1/4}u⃗_n(0) - Y' A n η` is exactly the difference of the two terminal-reward
stopping values at reward `-n^{-1/4}Φ_{n-·}(·)` (`Ftrue`, homogeneity via
`Parking.orientedStoppingSup_const_mul`) and at the box-clamped reward (`Fcut`, the reward
`Parking.orientedCutoffValue` itself uses). `Fcut` and `Ftrue` agree EXACTLY at the walk's own
grid point whenever the walk's rescaled position lies inside the cutoff box
(`Parking.rewardOfBox_boxRewardMap_eq_orientedGridReward`), so the difference of the two
terminal values, for EVERY admissible stopping rule, is supported on the bad event and bounded
there by the sum of the two UNCONDITIONAL bounds (`Parking.abs_orientedGridReward_orientedPath_le`,
`Parking.abs_rewardOfBox_orientedScaledSite_le`) — giving a bound that is the SAME for every rule,
exactly the hypothesis `Parking.abs_orientedStoppingSup_sub_le_of_terminal` needs.
-/
import Parking.Support.TightStoppingHomog
import Parking.Support.TightStoppingCompare
import Parking.Support.TightHappExact
import Parking.Support.TightGYBoxBound

open MeasureTheory Filter Topology LatticeProb

noncomputable section

namespace Parking

/-! ### The bad event -/

/-- **The walk's bad event**: the rescaled coordinate-difference partial sum exits
`[-4A√n, 4A√n]` at some time up to `n`.  The exact event `Parking.
measureReal_sup_walkPartialSum_sq_le` bounds. -/
def walkBad (n : ℕ) (A : ℝ) : Set (ℕ → Fin 2 × Bool) :=
  {p | ∃ k ≤ n, 4 * A * Real.sqrt n ≤ |walkPartialSum k p|}

theorem measurableSet_walkBad (n : ℕ) (A : ℝ) : MeasurableSet (walkBad n A) := by
  have heq : walkBad n A = ⋃ k ∈ Finset.range (n + 1),
      {p : ℕ → Fin 2 × Bool | 4 * A * Real.sqrt n ≤ |walkPartialSum k p|} := by
    ext p
    simp only [walkBad, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨k, hk, hp⟩; exact ⟨k, by omega, hp⟩
    · rintro ⟨k, hk, hp⟩; exact ⟨k, by omega, hp⟩
  rw [heq]
  exact MeasurableSet.biUnion (Finset.range (n + 1)).countable_toSet
    (fun k _ => measurableSet_le measurable_const (measurable_walkPartialSum k).abs)

/-! ### The exact identity between `Ftrue` and the grid reward at the walk's own point -/

/-- **`Ftrue`'s value at the walk's own point is exactly the grid reward there.** -/
theorem Ftrue_eq_orientedGridReward (n : ℕ) (η : Site 2 → ℝ) (p : ℕ → Fin 2 × Bool) (k : ℕ) :
    (n : ℝ) ^ (-(1 : ℝ) / 4) * (-orientedPotential η (n - k) (orientedPath (0 : Site 2) p k))
      = orientedGridReward n n η (k : ℤ) (-(orientedPath (0 : Site 2) p k) 0) := by
  set z : Site 2 := orientedPath (0 : Site 2) p k with hzdef
  have hlayer : orientedLayerIndex z = (k : ℤ) := orientedLayerIndex_orientedPath_zero p k
  have hzeq : z = orientedLayerPoint k (-z 0) := eq_orientedLayerPoint_of_layerIndex hlayer
  have htoNat : ((k : ℤ)).toNat = k := Int.toNat_natCast k
  unfold orientedGridReward
  rw [htoNat, ← hzeq]
  ring

/-! ### The pointwise bound on the terminal reward, uniform over stopping rules -/

/-- **The `Ftrue`-side reward is bounded, at the walk's own point, by `n^{-1/4}` times the
walk's own maximal potential functional, at EVERY time `k ≤ n`.** -/
theorem abs_Ftrue_orientedPath_le (n : ℕ) (η : Site 2 → ℝ) (p : ℕ → Fin 2 × Bool) (k : ℕ)
    (hk : k ≤ n) :
    |(n : ℝ) ^ (-(1 : ℝ) / 4) *
        (-orientedPotential η (n - k) (orientedPath (0 : Site 2) p k))| ≤
      (n : ℝ) ^ (-(1 : ℝ) / 4) * orientedMax (orientedPotential η) n 0 p := by
  rw [Ftrue_eq_orientedGridReward]
  exact abs_orientedGridReward_orientedPath_le n η p k hk

/-- **`Ftrue` and `Fcut` agree exactly at the walk's own point whenever the walk's rescaled
position at that time lies inside the cutoff box.** -/
theorem Ftrue_eq_Fcut_orientedPath_of_not_bad {A : ℝ} (hA : 0 ≤ A) (n : ℕ) (hn : 1 ≤ n)
    (η : Site 2 → ℝ) (p : ℕ → Fin 2 × Bool) (k : ℕ) (hk : k ≤ n)
    (hgood : |walkPartialSum k p| ≤ 4 * A * Real.sqrt n) :
    (n : ℝ) ^ (-(1 : ℝ) / 4) *
        (-orientedPotential η (n - k) (orientedPath (0 : Site 2) p k))
      = rewardOfBox (zero_le_one) hA (boxRewardMap 1 (zero_le_one) A hA n η) ((k : ℝ) / n)
          (orientedScaledSite n (orientedPath (0 : Site 2) p k)) := by
  have hbox : |orientedScaledSite n (orientedPath (0 : Site 2) p k)| ≤ 2 * A :=
    (abs_orientedScaledSite_le_iff n hn p k A).mpr hgood
  rw [rewardOfBox_boxRewardMap_eq_orientedGridReward hA n hn η k hk
    (orientedPath (0 : Site 2) p k) (orientedLayerIndex_orientedPath_zero p k) hbox]
  exact Ftrue_eq_orientedGridReward n η p k

/-- **The per-`p` bound on the bad event**: `n^{-1/4}` times the walk's own maximal
potential functional, plus the sup norm of the box-clamped reward field. -/
def happBadBound {A : ℝ} (hA : 0 ≤ A) (n : ℕ) (η : Site 2 → ℝ) (p : ℕ → Fin 2 × Bool) : ℝ :=
  (n : ℝ) ^ (-(1 : ℝ) / 4) * orientedMax (orientedPotential η) n 0 p +
    ‖boxRewardMap 1 (zero_le_one) A hA n η‖

/-- **The pointwise difference of the two rewards at the walk's own point, at any time `k ≤
n`, is bounded by the bad-event indicator of `Parking.happBadBound`.** -/
theorem abs_Ftrue_sub_Fcut_orientedPath_le {A : ℝ} (hA : 0 < A) (n : ℕ) (hn : 1 ≤ n)
    (η : Site 2 → ℝ) (p : ℕ → Fin 2 × Bool) (k : ℕ) (hk : k ≤ n) :
    |(n : ℝ) ^ (-(1 : ℝ) / 4) *
          (-orientedPotential η (n - k) (orientedPath (0 : Site 2) p k)) -
        rewardOfBox (zero_le_one) hA.le (boxRewardMap 1 (zero_le_one) A hA.le n η)
          ((k : ℝ) / n) (orientedScaledSite n (orientedPath (0 : Site 2) p k))| ≤
      Set.indicator (walkBad n A) (happBadBound hA.le n η) p := by
  by_cases hbad : p ∈ walkBad n A
  · rw [Set.indicator_of_mem hbad]
    show _ ≤ happBadBound hA.le n η p
    unfold happBadBound
    have h1 := abs_Ftrue_orientedPath_le n η p k hk
    have h2 := abs_rewardOfBox_orientedScaledSite_le (zero_le_one) hA.le
      (boxRewardMap 1 (zero_le_one) A hA.le n η) n k (orientedPath (0 : Site 2) p k)
    calc |(n : ℝ) ^ (-(1 : ℝ) / 4) *
            (-orientedPotential η (n - k) (orientedPath (0 : Site 2) p k)) -
          rewardOfBox (zero_le_one) hA.le (boxRewardMap 1 (zero_le_one) A hA.le n η)
            ((k : ℝ) / n) (orientedScaledSite n (orientedPath (0 : Site 2) p k))|
        ≤ |(n : ℝ) ^ (-(1 : ℝ) / 4) *
              (-orientedPotential η (n - k) (orientedPath (0 : Site 2) p k))| +
            |rewardOfBox (zero_le_one) hA.le (boxRewardMap 1 (zero_le_one) A hA.le n η)
              ((k : ℝ) / n) (orientedScaledSite n (orientedPath (0 : Site 2) p k))| :=
          abs_sub _ _
      _ ≤ (n : ℝ) ^ (-(1 : ℝ) / 4) * orientedMax (orientedPotential η) n 0 p +
            ‖boxRewardMap 1 (zero_le_one) A hA.le n η‖ := add_le_add h1 h2
  · rw [Set.indicator_of_notMem hbad]
    have hgood : |walkPartialSum k p| ≤ 4 * A * Real.sqrt n := by
      by_contra hcon
      exact hbad ⟨k, hk, (not_le.mp hcon).le⟩
    rw [Ftrue_eq_Fcut_orientedPath_of_not_bad hA.le n hn η p k hk hgood, sub_self, abs_zero]

end Parking

end
