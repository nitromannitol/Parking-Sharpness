/-
Assembles `Parking.abs_orientedTerminalValue_Ftrue_sub_Fcut_le` into the master bound: for
every scale `n ≥ 1` and every scenery `η`, the RESCALED odometer at the origin and `Parking.Y`'s
potential-inclusive value differ by at most the integral of the bad-event bound
`Parking.happBadBound`, uniformly in `η`.  The two potential terms of the Dynkin decomposition
`Parking.uOriented_eq_potential_add_stoppingSup` and of `Parking.orientedCutoffValuePot`'s own
origin evaluation cancel exactly, leaving the difference of the two terminal-reward stopping
values that `Parking.abs_orientedStoppingSup_sub_le_of_terminal` bounds.
-/
import Parking.Support.TightHappTerminal
import Parking.Support.OrientedCutoffValuePot

open MeasureTheory Filter Topology LatticeProb

noncomputable section

namespace Parking

/-! ### `BddAbove` of the two terminal-value sets -/

theorem bddAbove_orientedTerminalValues_FtrueScaled (η : Site 2 → ℝ) (n : ℕ) :
    BddAbove (orientedTerminalValues 2 (FtrueScaled η n) n 0) := by
  have hraw : IsLUB (orientedTerminalValues 2 (FtrueReward η n) n 0)
      (uOriented η n 0 - orientedPotential η n 0) :=
    isLUB_orientedTerminalValues (by norm_num) η n 0
  exact bddAbove_orientedTerminalValues_const_mul
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) (FtrueReward η n) n 0 hraw.bddAbove

theorem bddAbove_orientedTerminalValues_FcutReward {A : ℝ} (hA : 0 ≤ A) (n : ℕ)
    (η : Site 2 → ℝ) :
    BddAbove (orientedTerminalValues 2 (FcutReward hA n η) n 0) :=
  bddAbove_orientedTerminalValues (by norm_num) (FcutReward hA n η) n 0
    (M := ‖boxRewardMap 1 (zero_le_one) A hA n η‖)
    (fun k y => abs_rewardOfBox_orientedScaledSite_le (zero_le_one) hA
      (boxRewardMap 1 (zero_le_one) A hA n η) n k y)

/-! ### The two stopping-sup identities -/

theorem orientedStoppingSup_FtrueScaled_eq (η : Site 2 → ℝ) (n : ℕ) :
    orientedStoppingSup 2 (FtrueScaled η n) n 0
      = (n : ℝ) ^ (-(1 : ℝ) / 4) * (uOriented η n 0 - orientedPotential η n 0) := by
  show orientedStoppingSup 2 (fun k z => (n : ℝ) ^ (-(1 : ℝ) / 4) * FtrueReward η n k z) n 0 = _
  rw [orientedStoppingSup_const_mul (Real.rpow_nonneg (Nat.cast_nonneg n) _) (FtrueReward η n) n 0]
  congr 1
  exact orientedStoppingSup_potential (by norm_num) η n 0

theorem orientedStoppingSup_FcutReward_eq {A : ℝ} (hA : 0 ≤ A) (n : ℕ) (η : Site 2 → ℝ) :
    orientedStoppingSup 2 (FcutReward hA n η) n 0
      = orientedCutoffValue (T := 1) (zero_le_one) hA n (boxRewardMap 1 (zero_le_one) A hA n η) := by
  have hfl : ⌊(n : ℝ) * 1⌋₊ = n := by rw [mul_one, Nat.floor_natCast]
  unfold orientedCutoffValue
  rw [hfl]
  rfl

/-! ### `Fcut`'s reward at the origin -/

theorem FcutReward_zero_zero_eq {A : ℝ} (hA : 0 ≤ A) (n : ℕ) (hn : 1 ≤ n) (η : Site 2 → ℝ) :
    FcutReward hA n η 0 (0 : Site 2) = -(n : ℝ) ^ (-(1 : ℝ) / 4) * orientedPotential η n 0 := by
  have hz : orientedLayerIndex (0 : Site 2) = ((0 : ℕ) : ℤ) := by simp [orientedLayerIndex]
  have hbox : |orientedScaledSite n (0 : Site 2)| ≤ 2 * A := by
    have : orientedScaledSite n (0 : Site 2) = 0 := by simp [orientedScaledSite]
    rw [this]; simpa using hA
  have h := rewardOfBox_boxRewardMap_eq_orientedGridReward hA n hn η 0 (Nat.zero_le n)
    (0 : Site 2) hz hbox
  show rewardOfBox (zero_le_one) hA (boxRewardMap 1 (zero_le_one) A hA n η)
      (((0 : ℕ) : ℝ) / n) (orientedScaledSite n (0 : Site 2)) = _
  rw [h]
  have hid := Ftrue_eq_orientedGridReward n η (fun _ => (⟨0, by norm_num⟩, true)) 0
  simp only [orientedPath] at hid
  rw [Nat.sub_zero] at hid
  rw [← hid]
  ring

theorem orientedCutoffValuePot_eq {A : ℝ} (hA : 0 ≤ A) (n : ℕ) (hn : 1 ≤ n) (η : Site 2 → ℝ) :
    orientedCutoffValuePot (zero_le_one) hA n (boxRewardMap 1 (zero_le_one) A hA n η)
      = orientedCutoffValue (zero_le_one) hA n (boxRewardMap 1 (zero_le_one) A hA n η)
        + (n : ℝ) ^ (-(1 : ℝ) / 4) * orientedPotential η n 0 := by
  unfold orientedCutoffValuePot
  have hshow : (boxRewardMap 1 (zero_le_one) A hA n η : C(rewardBox 1 A, ℝ))
      (boxPoint (zero_le_one) hA 0 0) = FcutReward hA n η 0 (0 : Site 2) := by
    show (boxRewardMap 1 (zero_le_one) A hA n η : C(rewardBox 1 A, ℝ))
      (boxPoint (zero_le_one) hA 0 0)
      = rewardOfBox (zero_le_one) hA (boxRewardMap 1 (zero_le_one) A hA n η)
        (((0:ℕ) : ℝ) / n) (orientedScaledSite n (0 : Site 2))
    norm_num [rewardOfBox, orientedScaledSite]
  rw [hshow, FcutReward_zero_zero_eq hA n hn η]
  ring

/-! ### The master bound -/

/-- **`n^{-1/4} u⃗_n(0)` and `Parking.orientedCutoffValuePot`'s value at the box-clamped reward
differ by at most the bad-event bound's integral, for every scenery `η`.** -/
theorem abs_rescaled_uOriented_sub_Y_le {A : ℝ} (hA : 0 < A) (n : ℕ) (hn : 1 ≤ n)
    (η : Site 2 → ℝ) :
    |(n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented η n 0 -
        orientedCutoffValuePot (zero_le_one) hA.le n
          (boxRewardMap 1 (zero_le_one) A hA.le n η)| ≤
      ∫ p, Set.indicator (walkBad n A) (happBadBound hA.le n η) p ∂(walkLaw 2) := by
  have hBddF := bddAbove_orientedTerminalValues_FtrueScaled η n
  have hBddG := bddAbove_orientedTerminalValues_FcutReward hA.le n η
  have hkey := abs_orientedStoppingSup_sub_le_of_terminal (by norm_num : (1:ℕ) ≤ 2)
    (FtrueScaled η n) (FcutReward hA.le n η) n 0 hBddF hBddG
    (fun σ hσ => abs_orientedTerminalValue_Ftrue_sub_Fcut_le hA n hn η hσ)
  rw [orientedStoppingSup_FtrueScaled_eq, orientedStoppingSup_FcutReward_eq] at hkey
  rw [orientedCutoffValuePot_eq hA.le n hn η]
  have heq : (n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented η n 0 -
      (orientedCutoffValue (zero_le_one) hA.le n (boxRewardMap 1 (zero_le_one) A hA.le n η)
        + (n : ℝ) ^ (-(1 : ℝ) / 4) * orientedPotential η n 0)
      = (n : ℝ) ^ (-(1 : ℝ) / 4) * (uOriented η n 0 - orientedPotential η n 0) -
          orientedCutoffValue (zero_le_one) hA.le n
            (boxRewardMap 1 (zero_le_one) A hA.le n η) := by ring
  rw [heq]
  exact hkey

end Parking

end
