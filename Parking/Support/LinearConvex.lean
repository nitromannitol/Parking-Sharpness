/- Convexity and Lipschitz bounds for the absolute value of a finite linear sum. -/
import Parking.Support.ConvexProduct

noncomputable section
namespace Parking
open Finset
open scoped NNReal

theorem convexOn_abs_linear_sum (N : ℕ) (a : Fin N → ℝ) :
    ConvexOn ℝ Set.univ (fun ξ : Fin N → ℝ => |∑ i, a i * ξ i|) := by
  refine ⟨convex_univ, fun x _ y _ b c hb hc _ => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, sum_add_distrib]
  have he (v : Fin N → ℝ) (z : ℝ) : (∑ i, a i * (z * v i)) = z * ∑ i, a i * v i := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  rw [he x b, he y c]
  simpa only [abs_mul, abs_of_nonneg hb, abs_of_nonneg hc] using
    abs_add_le (b * ∑ i, a i * x i) (c * ∑ i, a i * y i)

theorem lipschitzWith_abs_linear_sum (N : ℕ) (a : Fin N → ℝ) :
    LipschitzWith ⟨∑ i, |a i|, sum_nonneg (fun _ _ => abs_nonneg _)⟩
      (fun ξ : Fin N → ℝ => |∑ i, a i * ξ i|) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc dist |∑ i, a i * x i| |∑ i, a i * y i| ≤ dist (∑ i, a i * x i) (∑ i, a i * y i) :=
      abs_abs_sub_abs_le_abs_sub _ _
    _ = |∑ i, a i * (x i - y i)| := by rw [Real.dist_eq, ← sum_sub_distrib]; congr 1; apply sum_congr rfl; intros; ring
    _ ≤ ∑ i, |a i * (x i - y i)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a i| * dist x y := by
      apply sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) (abs_nonneg _)
    _ = _ := by change _ = (∑ i, |a i|) * dist x y; rw [sum_mul]

end Parking
