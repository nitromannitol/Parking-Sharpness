/- A deterministic envelope for a finite path, obtained by successive bisection. -/
import Parking.Support.FinitePowerNorm

noncomputable section
namespace Parking
open MeasureTheory Finset

def dyadicEnvelope (r : ℝ) (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => |f 1 - f 0|
  | L + 1 => dyadicEnvelope r (fun i => f (2 * i)) L +
      finitePowerNorm r (range (2 ^ (L + 1))) (fun i => f (i + 1) - f i)

theorem dyadicEnvelope_nonneg (r : ℝ) (f : ℕ → ℝ) (L : ℕ) :
    0 ≤ dyadicEnvelope r f L := by
  induction L generalizing f with
  | zero => exact abs_nonneg _
  | succ L ih => exact add_nonneg (ih _) (finitePowerNorm_nonneg _ _ _)

theorem abs_sub_le_dyadicEnvelope {r : ℝ} (hr : 0 < r) (f : ℕ → ℝ)
    (L j : ℕ) (hj : j ≤ 2 ^ L) : |f j - f 0| ≤ dyadicEnvelope r f L := by
  induction L generalizing f j with
  | zero =>
    have : j = 0 ∨ j = 1 := by simp only [pow_zero] at hj; omega
    rcases this with rfl | rfl
    · simp [dyadicEnvelope]
    · rfl
  | succ L ih =>
    have hjq : j / 2 ≤ 2 ^ L := by
      rw [pow_succ] at hj
      omega
    have hc := ih (fun i => f (2 * i)) (j / 2) hjq
    simp only [mul_zero] at hc
    have he : |f j - f (2 * (j / 2))| ≤
        finitePowerNorm r (range (2 ^ (L + 1))) (fun i => f (i + 1) - f i) := by
      have hp : j = 2 * (j / 2) ∨ j = 2 * (j / 2) + 1 := by omega
      rcases hp with hp | hp
      · rw [← hp, sub_self, abs_zero]
        exact finitePowerNorm_nonneg _ _ _
      · have hm : 2 * (j / 2) ∈ range (2 ^ (L + 1)) := by
          apply mem_range.mpr
          omega
        have hb := abs_le_finitePowerNorm hr (range (2 ^ (L + 1)))
          (fun i => f (i + 1) - f i) hm
        simpa only [← hp] using hb
    calc |f j - f 0| ≤ |f j - f (2 * (j / 2))| + |f (2 * (j / 2)) - f 0| :=
        abs_sub_le _ _ _
      _ ≤ _ := by simpa only [dyadicEnvelope, add_comm] using add_le_add he hc

theorem measurable_dyadicEnvelope {Ω : Type} [MeasurableSpace Ω] (r : ℝ)
    (F : ℕ → Ω → ℝ) (hm : ∀ i, Measurable (F i)) (L : ℕ) :
    Measurable fun ω => dyadicEnvelope r (fun i => F i ω) L := by
  induction L generalizing F with
  | zero => exact ((hm 1).sub (hm 0)).abs
  | succ L ih =>
    exact (ih (fun i => F (2 * i)) (fun i => hm _)).add
      (measurable_finitePowerNorm r _ _ (fun i _ => (hm (i + 1)).sub (hm i)))

end Parking
