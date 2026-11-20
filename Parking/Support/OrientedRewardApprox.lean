import Parking.Support.OrientedValueHorizon
import Parking.Support.OrientedScaling

/-!
# Approximation of oriented stopping rewards

Uniform approximation on the elapsed-time interval controls the corresponding
finite-horizon oriented stopping values, with no measurability assumption on the
approximating reward.
-/

noncomputable section

namespace Parking

/-- Uniform approximation of rewards on the elapsed-time interval bounds the
    difference between the oriented stopping values. -/
theorem abs_orientedStoppingSup_sub_le_of_uniform_reward
    {n : ℕ} (hn : 0 < n) {T M ε : ℝ} (hT : 0 ≤ T)
    (G G' : ℝ → ℝ → ℝ)
    (hG : ∀ s y, |G s y| ≤ M) (hG' : ∀ s y, |G' s y| ≤ M)
    (hdiff : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y, |G' s y - G s y| ≤ ε) :
    |orientedStoppingSup 2
      (fun k z => G' ((k : ℝ) / n) (orientedScaledSite n z)) ⌊(n : ℝ) * T⌋₊ 0 -
     orientedStoppingSup 2
      (fun k z => G ((k : ℝ) / n) (orientedScaledSite n z)) ⌊(n : ℝ) * T⌋₊ 0| ≤ ε := by
  apply abs_orientedStoppingSup_sub_le_of_le (by norm_num) _ _ _ _
    (fun k y => hG' _ _) (fun k y => hG _ _)
  intro k hk z
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (k : ℝ) ≤ (n : ℝ) * T := by
    calc (k : ℝ) ≤ (⌊(n : ℝ) * T⌋₊ : ℝ) := by exact_mod_cast hk
      _ ≤ (n : ℝ) * T := Nat.floor_le (mul_nonneg hn'.le hT)
  apply hdiff _ ⟨by positivity, ?_⟩
  apply (div_le_iff₀ hn').2
  nlinarith

end Parking
