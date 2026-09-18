/- Testing the divisible recursion on its positive set. -/
import Parking.Basic
import Parking.Generic.DiscreteTesting

open LatticeProb

noncomputable section
namespace Parking

/-- At a positive value, the positive part in the divisible recursion is inactive. -/
theorem divisible_increment_eq_of_pos {d : ℕ} (η : Site d → ℝ) (n : ℕ) (x : Site d)
    (hpos : 0 < u η (n + 1) x) :
    u η (n + 1) x - u η n x = η x + walkOp (u η n) x - u η n x := by
  have h : 0 < η x + walkOp (u η n) x := by
    simpa only [u, lt_max_iff, lt_self_iff_false, false_or] using hpos
  change max 0 (η x + walkOp (u η n) x) - u η n x = _
  rw [max_eq_right h.le]

/-- The exact spatial weak equation for a test supported where the next odometer
is positive. No summability of the environment or odometer is needed. -/
theorem divisible_tested_increment {d : ℕ} (η : Site d → ℝ) (n : ℕ)
    (ψ : Site d → ℝ) (hψ : Function.HasFiniteSupport ψ)
    (hpos : ∀ x, ψ x ≠ 0 → 0 < u η (n + 1) x) :
    (∑' x : Site d, ψ x * (u η (n + 1) x - u η n x)) =
      (∑' x : Site d, ψ x * η x) +
        ∑' x : Site d, (walkOp ψ x - ψ x) * u η n x := by
  have heq : ∀ x, ψ x * (u η (n + 1) x - u η n x) =
      ψ x * η x + (ψ x * walkOp (u η n) x - ψ x * u η n x) := by
    intro x
    by_cases hx : ψ x = 0
    · simp [hx]
    · rw [divisible_increment_eq_of_pos η n x (hpos x hx)]
      ring
  have hη : Summable fun x => ψ x * η x := summable_of_hasFiniteSupport (hψ.mul_left η)
  have hP : Summable fun x => ψ x * walkOp (u η n) x :=
    summable_of_hasFiniteSupport (hψ.mul_left _)
  have hu : Summable fun x => ψ x * u η n x := summable_of_hasFiniteSupport (hψ.mul_left _)
  have hA := Generic.DiscreteTesting.summable_walkOp_mul (u η n) ψ hψ
  rw [tsum_congr heq, hη.tsum_add (hP.sub hu), hP.tsum_sub hu,
    Generic.DiscreteTesting.tsum_mul_walkOp (u η n) ψ hψ, ← hA.tsum_sub hu]
  congr 1
  apply tsum_congr
  intro x
  ring

/-- The exact space-time weak equation, with both temporal boundary terms zero.
Positivity is required only at the nonzero values of the test. -/
theorem divisible_tested_spaceTime {d : ℕ} (η : Site d → ℝ) (N : ℕ)
    (ψ : ℕ → Site d → ℝ) (hψ : ∀ n, Function.HasFiniteSupport (ψ n))
    (hzero : ∀ x, ψ 0 x = 0) (hfinal : ∀ x, ψ N x = 0)
    (hpos : ∀ n < N, ∀ x, ψ (n + 1) x ≠ 0 → 0 < u η (n + 1) x) :
    -(∑ n ∈ Finset.range N, ∑' x : Site d, u η n x * (ψ (n + 1) x - ψ n x)) =
      (∑ n ∈ Finset.range N, ∑' x : Site d, ψ (n + 1) x * η x) +
        ∑ n ∈ Finset.range N, ∑' x : Site d,
          (walkOp (ψ (n + 1)) x - ψ (n + 1) x) * u η n x := by
  have ht := Generic.DiscreteTesting.sum_tsum_time_difference (u η) ψ hψ N
  simp only [hzero, hfinal, mul_zero, tsum_zero, sub_zero] at ht
  have hs : (∑ n ∈ Finset.range N, ∑' x : Site d, ψ (n + 1) x *
      (u η (n + 1) x - u η n x)) =
      (∑ n ∈ Finset.range N, ∑' x : Site d, ψ (n + 1) x * η x) +
        ∑ n ∈ Finset.range N, ∑' x : Site d,
          (walkOp (ψ (n + 1)) x - ψ (n + 1) x) * u η n x := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    exact divisible_tested_increment η n (ψ (n + 1)) (hψ (n + 1))
      (hpos n (Finset.mem_range.mp hn))
  linarith

end Parking
