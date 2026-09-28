import Parking.Support.OrientedPathMax
import Parking.Support.OrientedMaximum
import Parking.Support.WStarMoment

/-!
# The `r`-th power of the maximum is at most a sum of `r`-th powers

The r-th power of the directed maximum along the walk is at most the sum of
the r-th powers of the error at the path times.
-/

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

/-- For `r ≥ 1`, the `r`-th power of `orientedMax F n x p` is at most the sum over path
times `j ≤ n` of the `r`-th powers `|F (n - j) (orientedPath x p j)| ^ r`, obtained by
bounding each term of the maximum by the `r`-th root of the total sum via
`Finset.sup'_le` and raising back to the `r`-th power. -/
theorem orientedMax_rpow_le_sum (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d) {r : ℝ}
    (hr : 1 ≤ r) (p : ℕ → Fin d × Bool) :
    orientedMax F n x p ^ r
      ≤ ∑ j ∈ Finset.range (n + 1), |F (n - j) (orientedPath x p j)| ^ r := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  set T : ℝ := ∑ j ∈ Finset.range (n + 1), |F (n - j) (orientedPath x p j)| ^ r with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun j _ => Real.rpow_nonneg (abs_nonneg _) r
  have hstep : ∀ j ∈ Finset.range (n + 1), |F (n - j) (orientedPath x p j)| ≤ T ^ (1 / r) := by
    intro j hj
    have hle : |F (n - j) (orientedPath x p j)| ^ r ≤ T :=
      Finset.single_le_sum (f := fun k => |F (n - k) (orientedPath x p k)| ^ r)
        (fun k _ => Real.rpow_nonneg (abs_nonneg _) r) hj
    have h1 : (|F (n - j) (orientedPath x p j)| ^ r) ^ (1 / r) ≤ T ^ (1 / r) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) r) hle (by positivity)
    rwa [← Real.rpow_mul (abs_nonneg _), mul_one_div, div_self (ne_of_gt hr0),
      Real.rpow_one] at h1
  have hmax : orientedMax F n x p ≤ T ^ (1 / r) := by
    rw [orientedMax_eq_sup]
    exact Finset.sup'_le _ _ hstep
  have h2 : orientedMax F n x p ^ r ≤ (T ^ (1 / r)) ^ r :=
    Real.rpow_le_rpow (orientedMax_nonneg F n x p) hmax (le_of_lt hr0)
  rwa [← Real.rpow_mul hT0, one_div, inv_mul_cancel₀ (ne_of_gt hr0), Real.rpow_one] at h2

end Parking
end
