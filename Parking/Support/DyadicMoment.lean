/- Moment control of a finite dyadic envelope. -/
import Parking.Support.DyadicEnvelope
import Parking.Support.DyadicFactor

noncomputable section
namespace Parking
open MeasureTheory Finset
variable {Ω : Type} [MeasurableSpace Ω]

theorem dyadicEnvelope_moment (μ : Measure Ω) {r : ℝ} (hr : 1 ≤ r)
    (a : ℝ) (L : ℕ) (F : ℕ → Ω → ℝ) (hm : ∀ i, Measurable (F i))
    {C : ℝ} (hC : 0 ≤ C)
    (hinc : ∀ j k : ℕ, j ≤ k → k ≤ 2 ^ L →
      Integrable (fun ω => |F k ω - F j ω| ^ r) μ ∧
      rNorm μ r (fun ω => F k ω - F j ω) ≤ C * ((k - j : ℕ) : ℝ) ^ a) :
    Integrable (fun ω => |dyadicEnvelope r (fun i => F i ω) L| ^ r) μ ∧
      rNorm μ r (fun ω => dyadicEnvelope r (fun i => F i ω) L) ≤
        C * dyadicFactor (2 ^ a) (2 ^ (1 / r)) L := by
  have hr0 : 0 < r := by linarith
  induction L generalizing C F with
  | zero =>
    obtain ⟨hi, hb⟩ := hinc 0 1 (by omega) (by simp)
    simpa only [dyadicEnvelope, abs_abs, rNorm, dyadicFactor, Nat.sub_zero,
      Nat.cast_one, Real.one_rpow, mul_one] using And.intro hi hb
  | succ L ih =>
    let G : ℕ → Ω → ℝ := fun i => F (2 * i)
    have hG : ∀ j k : ℕ, j ≤ k → k ≤ 2 ^ L →
        Integrable (fun ω => |G k ω - G j ω| ^ r) μ ∧
        rNorm μ r (fun ω => G k ω - G j ω) ≤
          (C * 2 ^ a) * ((k - j : ℕ) : ℝ) ^ a := by
      intro j k hjk hk
      obtain ⟨hi, hb⟩ := hinc (2 * j) (2 * k) (by omega) (by
        rw [pow_succ]
        omega)
      have he : ((2 * k - 2 * j : ℕ) : ℝ) = 2 * ((k - j : ℕ) : ℝ) := by
        rw [← Nat.mul_sub_left_distrib, Nat.cast_mul, Nat.cast_ofNat]
      rw [he, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg _),
        ← mul_assoc] at hb
      exact ⟨hi, hb⟩
    obtain ⟨hci, hcb⟩ := ih G (fun i => hm _) (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)) hG
    let H : Ω → ℝ := fun ω => finitePowerNorm r (range (2 ^ (L + 1)))
      (fun i => F (i + 1) ω - F i ω)
    have hhm : Measurable H := measurable_finitePowerNorm r _ _
      (fun i _ => (hm (i + 1)).sub (hm i))
    have hfi (i : ℕ) (hi : i ∈ range (2 ^ (L + 1))) :=
      hinc i (i + 1) (by omega) (by have := mem_range.mp hi; omega)
    obtain ⟨hhi, hhb⟩ := finitePowerNorm_moment μ hr0 (range (2 ^ (L + 1)))
      (fun i ω => F (i + 1) ω - F i ω) (fun i hi => (hfi i hi).1) hC (fun i hi => by
        simpa only [Nat.add_sub_cancel_left, Nat.cast_one, Real.one_rpow, mul_one] using (hfi i hi).2)
    have hcm := measurable_dyadicEnvelope r G (fun i => hm _) L
    have hsum := integrable_rpow_add μ hr hcm hhm hci hhi
    have hmink := rNorm_add_le μ hr hcm.aestronglyMeasurable hhm.aestronglyMeasurable hci hhi hsum
    refine ⟨hsum, hmink.trans ?_⟩
    have he : ((range (2 ^ (L + 1))).card : ℝ) ^ (1 / r) = (2 ^ (1 / r) : ℝ) ^ (L + 1) := by
      rw [card_range, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_pow_comm (by norm_num)]
    rw [he] at hhb
    have hh := add_le_add hcb hhb
    exact hh.trans_eq (by simp only [dyadicFactor]; ring)

end Parking
