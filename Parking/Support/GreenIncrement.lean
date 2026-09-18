/-
The increment bound `eq:increment` of `parking.tex:1037-1046`:

  `sup_{m ≥ 1} sup_y sup_{z ∼ y} |g_m(z) - (P g_m)(y)| ≤ C`,

a bound on `greenIncrement d n` that does not grow with the horizon `n`.  The
repository's `abs_greenDiff_le` gives only `2m`, which is what makes the `r·a`
of the martingale moment inequality into `r·n` rather than the paper's `r`.

The route here is not the paper's splitting
`g_m(z)-(Pg_m)(y) = (g_m(z)-g_m(y)) + ((I-P)g_m)(y)` but the observation that
the discrepancy at one neighbour is already controlled by the variance over all
of them: `Γ_m(y)` is an average of the squared discrepancies with the weights
`1/(2d)`, so a single squared discrepancy is at most `2d Γ_m(y)`.  A uniform
bound on `Γ` therefore bounds the increment, and a uniform bound on `Γ` is what
the two halves of `lem:gamma-sum` already prove: `4C²(1+|y|)^{2-2d} ≤ 4C²` from
the gradient in dimension two and above, and `4(min(1, m/|y|²))² ≤ 4` from the
exact one-dimensional computation.

Also here: the increment is positive once `n ≥ 2`, which the martingale moment
inequality needs because its bound `a` is required to be positive.  The witness
is the horizon `m = 1`, where `g_1` is the indicator of the origin, at a site
adjacent to the origin, where the discrepancy is `1 - 1/(2d)`.
-/
import Parking.Support.WQuadratic
import Parking.External.GreenGradient

noncomputable section

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-! ### One discrepancy against the variance of all of them -/

/-- **A single squared discrepancy is at most `2d` times the variance.**  The
term of `Γ_m(y)` at the neighbour `z` carries the weight `1/(2d)` and every
other term is nonnegative. -/
theorem sq_greenDiff_le_gamma (hd : 1 ≤ d) (m : ℕ) {y z : Site d}
    (hz : z ∈ nbrFinset y) :
    (green d m z - walkOp (green d m) y) ^ 2 ≤ 2 * (d : ℝ) * gamma d m y := by
  have hdpos : (0 : ℝ) < 2 * (d : ℝ) := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have hgam : gamma d m y
      = ∑ z' ∈ nbrFinset y, kern d y z' * (green d m z' - walkOp (green d m) y) ^ 2 := rfl
  have hterm : kern d y z * (green d m z - walkOp (green d m) y) ^ 2 ≤ gamma d m y := by
    rw [hgam]
    refine Finset.single_le_sum
      (f := fun z' : Site d => kern d y z' * (green d m z' - walkOp (green d m) y) ^ 2)
      (fun z' _ => ?_) hz
    have hk : 0 ≤ kern d y z' := by
      rw [kern]
      by_cases hcase : z' ∈ nbrFinset y
      · rw [if_pos hcase]; positivity
      · rw [if_neg hcase]
    positivity
  rw [kern, if_pos hz] at hterm
  rw [inv_mul_le_iff₀ hdpos] at hterm
  linarith

/-! ### A uniform bound on the variance -/

/-- **`Γ` is bounded, uniformly in the horizon and in the site.**  In dimension
one this is the exact computation of Step 3 of `lem:gamma-sum`, and in dimension
two and above it is the gradient estimate at its largest, at the origin. -/
theorem exists_gamma_le (d : ℕ) (hd : 1 ≤ d) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (m : ℕ) (y : Site d), gamma d m y ≤ B := by
  rcases Nat.lt_or_ge d 2 with hlt | hge
  · have hd1 : d = 1 := by omega
    subst hd1
    refine ⟨4, by norm_num, fun m y => ?_⟩
    rw [site_one_eq y]
    refine le_trans (gamma_one_le (le_refl m) (y 0)) ?_
    have hnn : (0 : ℝ) ≤ ((m : ℝ) / (((y 0).natAbs : ℕ) : ℝ) ^ 2) := by positivity
    have hmin0 : (0 : ℝ) ≤ min 1 ((m : ℝ) / (((y 0).natAbs : ℕ) : ℝ) ^ 2) := le_min zero_le_one hnn
    have hmin1 : min 1 ((m : ℝ) / (((y 0).natAbs : ℕ) : ℝ) ^ 2) ≤ 1 := min_le_left _ _
    nlinarith
  · obtain ⟨C, hC, hgrad⟩ := Parking.External.greenGradient d hge
    refine ⟨4 * C ^ 2, by positivity, fun m y => ?_⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [gamma_zero]; positivity
    · refine le_trans (gamma_le_of_gradient hd hC (fun z hz => hgrad m hm y z hz)) ?_
      have hbase : (1 : ℝ) ≤ 1 + (graphNorm y : ℝ) := by
        have : (0 : ℝ) ≤ (graphNorm y : ℝ) := by positivity
        linarith
      have hexp : (1 : ℝ) - (d : ℝ) ≤ 0 := by
        have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        linarith
      have hle : (1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hbase hexp
      have hnn : (0 : ℝ) ≤ (1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ)) := by
        refine le_of_lt (Real.rpow_pos_of_pos ?_ _)
        positivity
      have hsq : ((1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ))) ^ 2 ≤ 1 := by nlinarith
      have hCnn : (0 : ℝ) ≤ 4 * C ^ 2 := by positivity
      calc 4 * C ^ 2 * ((1 + (graphNorm y : ℝ)) ^ (1 - (d : ℝ))) ^ 2
          ≤ 4 * C ^ 2 * 1 := mul_le_mul_of_nonneg_left hsq hCnn
        _ = 4 * C ^ 2 := by ring

/-! ### The increment bound -/

/-- Every term of the supremum defining `greenIncrement` is below `K`, so the
supremum is.  The nonnegativity of `K` covers the branches on which the
conditional supremum is the supremum of the empty set. -/
theorem greenIncrement_le_of_forall {K : ℝ} (hK : 0 ≤ K) (n : ℕ)
    (h : ∀ (m : ℕ) (y z : Site d), z ∈ nbrFinset y →
      |green d m z - walkOp (green d m) y| ≤ K) :
    greenIncrement d n ≤ K := by
  refine ciSup_le fun m => ?_
  by_cases hm : m ∈ Set.Iio n
  · rw [ciSup_pos hm]
    refine ciSup_le fun y => ?_
    refine ciSup_le fun z => ?_
    by_cases hz : z ∈ nbrFinset y
    · rw [ciSup_pos hz]; exact h m y z hz
    · rw [ciSup_neg hz, Real.sSup_empty]; exact hK
  · rw [ciSup_neg hm, Real.sSup_empty]; exact hK

/-- **The increment bound `eq:increment`.**  There is a constant, depending only
on the dimension, that bounds `greenIncrement d n` for every horizon `n`. -/
theorem exists_greenIncrement_le (d : ℕ) (hd : 1 ≤ d) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, greenIncrement d n ≤ K := by
  obtain ⟨B, hB, hgamma⟩ := exists_gamma_le d hd
  refine ⟨Real.sqrt (2 * (d : ℝ) * B) + 1, by positivity, fun n => ?_⟩
  refine greenIncrement_le_of_forall (by positivity) n fun m y z hz => ?_
  have hsq : (green d m z - walkOp (green d m) y) ^ 2 ≤ 2 * (d : ℝ) * B := by
    refine le_trans (sq_greenDiff_le_gamma hd m hz) ?_
    have hdnn : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left (hgamma m y) hdnn
  have : |green d m z - walkOp (green d m) y| ≤ Real.sqrt (2 * (d : ℝ) * B) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  linarith

/-! ### The increment is positive -/

theorem green_one_apply (d : ℕ) (x : Site d) : green d 1 x = if x = 0 then 1 else 0 := by
  rw [green, Finset.sum_range_one, heat]

theorem unit_add_unit_ne_zero (i j : Fin d) : unit i + unit j ≠ (0 : Site d) := by
  intro h
  have := congrFun h i
  rw [unit, unit] at this
  simp only [Pi.add_apply, Pi.zero_apply, Pi.single_eq_same] at this
  rcases eq_or_ne j i with rfl | hji
  · simp at this
  · rw [Pi.single_eq_of_ne (Ne.symm hji)] at this
    simp at this

theorem unit_sub_unit_eq_zero_iff (i j : Fin d) :
    unit i - unit j = (0 : Site d) ↔ j = i := by
  constructor
  · intro h
    by_contra hji
    have := congrFun h i
    rw [unit, unit] at this
    simp only [Pi.sub_apply, Pi.zero_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (Ne.symm hji)] at this
    simp at this
  · rintro rfl
    simp

/-- **The increment is positive once the horizon is at least two.**  At the
horizon `m = 1` the truncated Green function is the indicator of the origin, and
at a site adjacent to the origin its discrepancy is `1 - 1/(2d)`. -/
theorem greenIncrement_pos (hd : 1 ≤ d) {n : ℕ} (hn : 2 ≤ n) :
    0 < greenIncrement d n := by
  set i₀ : Fin d := ⟨0, hd⟩ with hi₀
  have hmem : (0 : Site d) ∈ nbrFinset (unit i₀) := by
    rw [nbrFinset]
    refine Finset.mem_biUnion.mpr ⟨i₀, Finset.mem_univ _, ?_⟩
    refine Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr ?_))
    exact ((unit_sub_unit_eq_zero_iff i₀ i₀).mpr rfl).symm
  have hwalk : walkOp (green d 1) (unit i₀) = (2 * (d : ℝ))⁻¹ := by
    rw [walkOp, nbrSum]
    have hterm : ∀ i : Fin d,
        green d 1 (unit i₀ + unit i) + green d 1 (unit i₀ - unit i)
          = if i = i₀ then 1 else 0 := by
      intro i
      rw [green_one_apply, green_one_apply, if_neg (unit_add_unit_ne_zero i₀ i)]
      by_cases h : i = i₀
      · rw [if_pos ((unit_sub_unit_eq_zero_iff i₀ i).mpr h), if_pos h, zero_add]
      · rw [if_neg (fun hc => h ((unit_sub_unit_eq_zero_iff i₀ i).mp hc)), if_neg h, zero_add]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq' Finset.univ i₀
      (fun _ : Fin d => (1 : ℝ)), if_pos (Finset.mem_univ i₀)]
    exact one_div _
  have hdpos : (0 : ℝ) < 2 * (d : ℝ) := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hd2 : (2 : ℝ) ≤ 2 * (d : ℝ) := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hinvpos : (0 : ℝ) < (2 * (d : ℝ))⁻¹ := inv_pos.mpr hdpos
  have hinv : (2 * (d : ℝ))⁻¹ * (2 * (d : ℝ)) = 1 := inv_mul_cancel₀ (ne_of_gt hdpos)
  have hpos : (0 : ℝ) < 1 - (2 * (d : ℝ))⁻¹ := by
    nlinarith [mul_le_mul_of_nonneg_left hd2 (le_of_lt hinvpos)]
  have hval : |green d 1 (0 : Site d) - walkOp (green d 1) (unit i₀)|
      = 1 - (2 * (d : ℝ))⁻¹ := by
    rw [green_one_apply, if_pos rfl, hwalk]
    rw [abs_of_nonneg (by linarith)]
  calc (0 : ℝ) < 1 - (2 * (d : ℝ))⁻¹ := hpos
    _ = |green d 1 (0 : Site d) - walkOp (green d 1) (unit i₀)| := hval.symm
    _ ≤ greenIncrement d n := le_greenIncrement hd (by omega) hmem

end Parking

end
