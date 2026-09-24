/-
Convexity and positive homogeneity of the divisible sandpile odometer.
-/
import Parking.Support.UBound
import Mathlib.Analysis.Convex.Function

noncomputable section
namespace Parking
open LatticeProb
variable {d : ℕ}

/-- Positive combinations of initial fields bound the corresponding odometer. -/
theorem u_positive_combination_le (hd : 1 ≤ d) (η ξ : Site d → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (n : ℕ) (x : Site d) :
    u (fun y => a * η y + b * ξ y) n x ≤ a * u η n x + b * u ξ n x := by
  induction n generalizing x with
  | zero => simp [u]
  | succ n ih =>
    have hp := walkOp_mono hd (fun y => ih y) x
    have hlin : walkOp (fun y => a * u η n y + b * u ξ n y) x =
        a * walkOp (u η n) x + b * walkOp (u ξ n) x := by
      simp only [walkOp, nbrSum]
      simp_rw [show ∀ i : Fin d,
        (a * u η n (x + unit i) + b * u ξ n (x + unit i)) +
          (a * u η n (x - unit i) + b * u ξ n (x - unit i)) =
            a * (u η n (x + unit i) + u η n (x - unit i)) +
              b * (u ξ n (x + unit i) + u ξ n (x - unit i)) by intro i; ring]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    rw [hlin] at hp
    change max 0 (a * η x + b * ξ x + walkOp (u (fun y => a * η y + b * ξ y) n) x) ≤
      a * max 0 (η x + walkOp (u η n) x) + b * max 0 (ξ x + walkOp (u ξ n) x)
    apply max_le
    · exact add_nonneg (mul_nonneg ha (le_max_left _ _)) (mul_nonneg hb (le_max_left _ _))
    · have hη := mul_le_mul_of_nonneg_left (le_max_right (0 : ℝ) (η x + walkOp (u η n) x)) ha
      have hξ := mul_le_mul_of_nonneg_left (le_max_right (0 : ℝ) (ξ x + walkOp (u ξ n) x)) hb
      nlinarith only [hp, hη, hξ]

/-- The sandpile odometer is convex as a function of its initial field. -/
theorem convexOn_u (hd : 1 ≤ d) (n : ℕ) (x : Site d) :
    ConvexOn ℝ Set.univ (fun η : Site d → ℝ => u η n x) := by
  refine ⟨convex_univ, fun η _ ξ _ a b ha hb _ => ?_⟩
  change u (fun y => a * η y + b * ξ y) n x ≤ a * u η n x + b * u ξ n x
  exact u_positive_combination_le hd η ξ ha hb n x

/-- Positive homogeneity of the sandpile odometer. -/
theorem u_const_mul (η : Site d → ℝ) {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (x : Site d) :
    u (fun y => a * η y) n x = a * u η n x := by
  induction n generalizing x with
  | zero => simp [u]
  | succ n ih =>
    change max 0 (a * η x + walkOp (u (fun y => a * η y) n) x) =
      a * max 0 (η x + walkOp (u η n) x)
    have hw : walkOp (u (fun y => a * η y) n) x = a * walkOp (u η n) x := by
      simp only [walkOp, nbrSum, ih]
      simp_rw [← mul_add]
      rw [← Finset.mul_sum]
      ring
    rw [hw, ← mul_add, mul_max_of_nonneg (0 : ℝ) (η x + walkOp (u η n) x) ha, mul_zero]
end Parking
