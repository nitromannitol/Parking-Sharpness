import Parking.Support.OrientedBinomial
import Parking.Support.BinomialNorm
import Parking.Support.OrientedVariance

/-!
# Green norms and departure-increment bounds

Green norms and uniform departure-increment bounds for the oriented walk.
-/

noncomputable section
namespace Parking
open LatticeProb Finset
variable {d : ℕ}

/-- In dimension `2`, the squared Green norm `∑' x, orientedGreen 2 n x ^ 2` is sandwiched
between `(1/2) * √n` and `2 * √n`, transferred from the diagonal convolution bounds
`sum_conv_zero_lower` and `sum_conv_zero_upper` via the collision identity
`tsum_orientedGreen_two_sq`. -/
theorem orientedGreen_two_sq_bounds (n : ℕ) :
    (1 / 2 : ℝ) * Real.sqrt n ≤ ∑' x : Site 2, orientedGreen 2 n x ^ 2 ∧
      (∑' x : Site 2, orientedGreen 2 n x ^ 2) ≤ 2 * Real.sqrt n := by
  rw [tsum_orientedGreen_two_sq]
  exact ⟨sum_conv_zero_lower n, sum_conv_zero_upper n⟩

/-- The supremum of `|orientedGreen d n x|` over all sites `x` is at most `1`, since each
value is nonnegative and at most `1` by `orientedGreen_le_one`. -/
theorem orientedGreen_supAbs_le (hd : 1 ≤ d) (n : ℕ) : supAbs (orientedGreen d n) ≤ 1 := by
  apply ciSup_le
  intro x
  rw [abs_of_nonneg (orientedGreen_nonneg n x)]
  exact orientedGreen_le_one hd n x

/-- The iterated square root `√(√n)` equals the fourth root `n ^ (1/4)`, by rewriting both
square roots as `rpow` and combining the exponents. -/
theorem sqrt_sqrt_nat (n : ℕ) : Real.sqrt (Real.sqrt (n : ℝ)) = (n : ℝ) ^ ((1 : ℝ) / 4) := by
  simp only [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num

/-- In dimension `2`, the `ℓ²`-norm `l2Norm (orientedGreen 2 n)` is sandwiched between
constant multiples of `n ^ (1/4)`, obtained by taking square roots in
`orientedGreen_two_sq_bounds` and simplifying with `sqrt_sqrt_nat`. -/
theorem orientedGreen_two_l2_bounds (n : ℕ) :
    Real.sqrt (1 / 2 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ l2Norm (orientedGreen 2 n) ∧
      l2Norm (orientedGreen 2 n) ≤ Real.sqrt 2 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
  obtain ⟨hlo, hhi⟩ := orientedGreen_two_sq_bounds n
  have hl := Real.sqrt_le_sqrt hlo
  have hu := Real.sqrt_le_sqrt hhi
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), sqrt_sqrt_nat] at hl
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), sqrt_sqrt_nat] at hu
  exact ⟨hl, hu⟩

/-- The Green function's departure increment `orientedGreen d m (x + unit i) -
(average of orientedGreen d m over the d successors of x)` has absolute value at most
`1`, since both `orientedGreen d m (x + unit i)` and the average lie in `[0, 1]`
by `orientedGreen_nonneg` and `orientedGreen_le_one`. -/
theorem orientedGreen_increment_le (hd : 1 ≤ d) (m : ℕ) (x : Site d) (i : Fin d) :
    |orientedGreen d m (x + unit i) - (∑ j : Fin d, orientedGreen d m (x + unit j)) / d| ≤ 1 := by
  have h0 : 0 ≤ (∑ j : Fin d, orientedGreen d m (x + unit j)) / (d : ℝ) :=
    div_nonneg (sum_nonneg fun j _ => orientedGreen_nonneg m _) (Nat.cast_nonneg _)
  have h1 : (∑ j : Fin d, orientedGreen d m (x + unit j)) / (d : ℝ) ≤ 1 := by
    apply (div_le_iff₀ (show (0 : ℝ) < d by exact_mod_cast hd)).mpr
    have h := sum_le_sum (s := (univ : Finset (Fin d)))
      (fun j _ => orientedGreen_le_one hd m (x + unit j))
    simpa using h
  exact abs_le.mpr ⟨by linarith [orientedGreen_nonneg m (x + unit i)],
    by linarith [orientedGreen_le_one hd m (x + unit i)]⟩

/-- For any finite set `S` and any horizon function `m` bounded by `N` on `S`, the sum
`∑ x ∈ S, orientedGamma d (m x) x` is at most `1`, by monotonicity of `orientedGamma` in
its horizon argument and the total-mass bound `tsum_orientedGamma_le_one`. -/
theorem sum_orientedGamma_horizons_le_one (hd : 1 ≤ d) (N : ℕ) (S : Finset (Site d))
    (m : Site d → ℕ) (hm : ∀ x ∈ S, m x ≤ N) : ∑ x ∈ S, orientedGamma d (m x) x ≤ 1 := by
  have hs : Summable (orientedGamma d N) :=
    (summable_sum (s := range N) (fun l _ => summable_orientedCharge hd l)).congr
      (fun x => (orientedGamma_eq_sum N x).symm)
  calc (∑ x ∈ S, orientedGamma d (m x) x) ≤ ∑ x ∈ S, orientedGamma d N x :=
      sum_le_sum fun x hx => orientedGamma_mono x (hm x hx)
    _ ≤ ∑' x, orientedGamma d N x := hs.sum_le_tsum S (fun x _ => by
      rw [orientedGamma_eq_sum]
      exact sum_nonneg fun l _ => orientedCharge_nonneg l x)
    _ ≤ 1 := tsum_orientedGamma_le_one hd N

end Parking
