/-
**The SPACE-direction two-point comparison of the truncated Green function, dimension three
and above.**  The other half (alongside the already-proved TIME direction,
`Parking.Support.LinTimeShift`) of the translated-kernel-difference bound
`parking.tex:1745-1747` needs for the Kolmogorov chaining of the equicontinuity clause of
`prop:spatial-scaling`: a bound on

    l2Norm (fun z => green d n (x - z) - green d n (y - z))
    supAbs (fun z => green d n (x - z) - green d n (y - z))

for the SAME horizon `n` and two sites `x, y`, decaying in `graphNorm (x - y)`, UNIFORMLY in
`n` (unlike the time direction, whose bound decays as `n → ∞` at fixed gap; here the bound is
exactly LINEAR in the graph distance and does not improve with `n`, matching the fact that
`Parking.External.GreenGradient` itself carries no horizon dependence).

Route: chain `Parking.External.GreenGradient` (`d ≥ 2`, already proved in the
shared library) along ONE neighbour step at a time from `x` towards `y`
(`exists_nbr_graphNorm_pred`, an elementary fact about the `ℓ¹` norm: some coordinate of
`x - y` is nonzero, and moving it one unit towards zero is a neighbour step that reduces
`graphNorm (x - y)` by exactly one), giving a ONE-STEP comparison
(`exists_green_space_step_l2_bound`/`_sup_bound`) whose `l2Norm` half needs the shell-sum
computation `sum_sq_rpow_le` (the same shape as `Parking.Support.GammaSum`'s own shell
machinery, reused: `sum_box_radial`, `shellCard_le`, `rpow_shell_combine`,
`sum_inv_sq_succ_le_one`), and CHAINING the one-step bound over `graphNorm (x - y)` steps by a
two-term Minkowski/triangle inequality for finitely-supported fields
(`l2Norm_add_le_of_support`/`supAbs_add_le_of_support`, proved here from finite Cauchy-Schwarz,
`Finset.sum_mul_sq_le_sq_mul_sq`, since `green d n` vanishes outside a ball of radius `n`,
`Parking.green_eq_zero_of_le`, so every difference in sight is finitely supported and no
genuine infinite-series Minkowski inequality is needed).

Dimension three is the CLEAN case handled here in full: the shell sum
`Σ_k shellCard(d,k) · (1+k)^(2(1-d))` is bounded by a dimension-only constant, UNIFORMLY in the
box radius (`sum_sq_rpow_le`, exactly `gamma_sum_of_gradient`'s own "dimension three and above"
arithmetic, transcribed for this different quantity).  Dimensions one and two need the
truncation-by-vanishing-support trick `GammaSum.lean` uses for a different quantity (the log
divergence at `d = 2`, and `GammaSum.lean`'s own exact `srwTail` identity in place of
`GreenGradient` at `d = 1`, since `GreenGradient` is `d ≥ 2`-only); they are treated in
`Parking.Support.SpatGreenShiftLowDim`, not here.

No External beyond `Parking.External.GreenGradient` (already proved in the shared library,
`Parking.External.greenGradient`) is used or registered.
-/
import Parking.Support.GammaSum
import Parking.Support.LinTimeShift
import Parking.Support.Odometer
import Parking.External.GreenGradient

noncomputable section

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-! ### Elementary sup-norm and box facts -/

theorem mem_boxFinset_iff' {x z : Site d} {r : ℕ} :
    z ∈ boxFinset x r ↔ supNorm (x - z) ≤ r := by
  rw [LatticeProb.mem_boxFinset_iff, supNorm_le_iff]
  constructor
  · intro h i
    have := h i
    rw [abs_sub_comm] at this
    simpa using this
  · intro h i
    have := h i
    rw [abs_sub_comm]
    simpa using this

theorem supNorm_add_le' (x y : Site d) : supNorm (x + y) ≤ supNorm x + supNorm y := by
  refine Finset.sup_le fun i _ => ?_
  have h : ((x + y) i).natAbs ≤ (x i).natAbs + (y i).natAbs := by
    simpa using Int.natAbs_add_le (x i) (y i)
  refine le_trans h (Nat.add_le_add ?_ ?_)
  · exact Finset.le_sup (f := fun j : Fin d => (x j).natAbs) (Finset.mem_univ i)
  · exact Finset.le_sup (f := fun j : Fin d => (y j).natAbs) (Finset.mem_univ i)

theorem supNorm_zero' : supNorm (0 : Site d) = 0 := by
  unfold supNorm; simp

theorem sum_boxFinset_shift (x : Site d) (r : ℕ) (g : ℕ → ℝ) :
    ∑ z ∈ boxFinset x r, g (supNorm (x - z)) = ∑ w ∈ boxFinset (0 : Site d) r, g (supNorm w) := by
  refine Finset.sum_nbij' (fun z => x - z) (fun w => x - w) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    rw [mem_boxFinset_zero_iff]
    exact mem_boxFinset_iff'.mp hz
  · intro w hw
    rw [mem_boxFinset_iff']
    rw [mem_boxFinset_zero_iff] at hw
    simpa using hw
  · intro z _; abel
  · intro w _; abel
  · intro z _; rfl

theorem green_diff_eq_zero_of_notMem_box {n R : ℕ} {a b c : Site d}
    (ha : supNorm (c - a) + n ≤ R) (hb : supNorm (c - b) + n ≤ R)
    {z : Site d} (hz : z ∉ boxFinset c R) :
    green d n (a - z) - green d n (b - z) = 0 := by
  rw [mem_boxFinset_iff'] at hz
  have hz1 : R < supNorm (c - z) := not_le.mp hz
  have haz : n ≤ graphNorm (a - z) := by
    have hsplit : c - z = (c - a) + (a - z) := by abel
    have hadd : supNorm (c - z) ≤ supNorm (c - a) + supNorm (a - z) := by
      rw [hsplit]; exact supNorm_add_le' _ _
    have : n ≤ supNorm (a - z) := by omega
    exact le_trans this (supNorm_le_graphNorm (a - z))
  have hbz : n ≤ graphNorm (b - z) := by
    have hsplit : c - z = (c - b) + (b - z) := by abel
    have hadd : supNorm (c - z) ≤ supNorm (c - b) + supNorm (b - z) := by
      rw [hsplit]; exact supNorm_add_le' _ _
    have : n ≤ supNorm (b - z) := by omega
    exact le_trans this (supNorm_le_graphNorm (b - z))
  rw [green_eq_zero_of_le haz, green_eq_zero_of_le hbz]
  ring

/-! ### Two-term triangle inequalities for finitely-supported fields -/

theorem l2Norm_add_le_of_support {S : Finset (Site d)} {f g : Site d → ℝ}
    (hf : ∀ z ∉ S, f z = 0) (hg : ∀ z ∉ S, g z = 0) :
    l2Norm (fun z => f z + g z) ≤ l2Norm f + l2Norm g := by
  have h1 : (∑' z : Site d, (f z + g z) ^ 2) = ∑ z ∈ S, (f z + g z) ^ 2 := by
    refine tsum_eq_sum (fun z hz => ?_)
    rw [hf z hz, hg z hz]; ring
  have h2 : (∑' z : Site d, f z ^ 2) = ∑ z ∈ S, f z ^ 2 :=
    tsum_eq_sum (fun z hz => by rw [hf z hz]; ring)
  have h3 : (∑' z : Site d, g z ^ 2) = ∑ z ∈ S, g z ^ 2 :=
    tsum_eq_sum (fun z hz => by rw [hg z hz]; ring)
  have hSf : 0 ≤ ∑ z ∈ S, f z ^ 2 := Finset.sum_nonneg fun z _ => sq_nonneg _
  have hSg : 0 ≤ ∑ z ∈ S, g z ^ 2 := Finset.sum_nonneg fun z _ => sq_nonneg _
  have hCS : (∑ z ∈ S, f z * g z) ^ 2 ≤ (∑ z ∈ S, f z ^ 2) * (∑ z ∈ S, g z ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq S f g
  have hCSle : ∑ z ∈ S, f z * g z ≤ Real.sqrt (∑ z ∈ S, f z ^ 2) * Real.sqrt (∑ z ∈ S, g z ^ 2) := by
    have hsq : (Real.sqrt (∑ z ∈ S, f z ^ 2) * Real.sqrt (∑ z ∈ S, g z ^ 2)) ^ 2
        = (∑ z ∈ S, f z ^ 2) * (∑ z ∈ S, g z ^ 2) := by
      rw [mul_pow, Real.sq_sqrt hSf, Real.sq_sqrt hSg]
    nlinarith [hCS, hsq, sq_nonneg (∑ z ∈ S, f z * g z
        - Real.sqrt (∑ z ∈ S, f z ^ 2) * Real.sqrt (∑ z ∈ S, g z ^ 2)),
      mul_nonneg (Real.sqrt_nonneg (∑ z ∈ S, f z ^ 2)) (Real.sqrt_nonneg (∑ z ∈ S, g z ^ 2))]
  have hexpand : ∑ z ∈ S, (f z + g z) ^ 2
      = (∑ z ∈ S, f z ^ 2) + 2 * (∑ z ∈ S, f z * g z) + (∑ z ∈ S, g z ^ 2) := by
    have hterm : ∀ z ∈ S, (f z + g z) ^ 2 = f z ^ 2 + 2 * (f z * g z) + g z ^ 2 := fun z _ => by ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  have hbound : ∑ z ∈ S, (f z + g z) ^ 2
      ≤ (Real.sqrt (∑ z ∈ S, f z ^ 2) + Real.sqrt (∑ z ∈ S, g z ^ 2)) ^ 2 := by
    have hA : Real.sqrt (∑ z ∈ S, f z ^ 2) ^ 2 = ∑ z ∈ S, f z ^ 2 := Real.sq_sqrt hSf
    have hB : Real.sqrt (∑ z ∈ S, g z ^ 2) ^ 2 = ∑ z ∈ S, g z ^ 2 := Real.sq_sqrt hSg
    nlinarith [hCSle, hA, hB, hexpand]
  show Real.sqrt (∑' z : Site d, (f z + g z) ^ 2) ≤ l2Norm f + l2Norm g
  rw [h1]
  have hrhs : Real.sqrt (∑ z ∈ S, f z ^ 2) + Real.sqrt (∑ z ∈ S, g z ^ 2) = l2Norm f + l2Norm g := by
    unfold l2Norm; rw [h2, h3]
  calc Real.sqrt (∑ z ∈ S, (f z + g z) ^ 2)
      ≤ Real.sqrt ((Real.sqrt (∑ z ∈ S, f z ^ 2) + Real.sqrt (∑ z ∈ S, g z ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt hbound
    _ = Real.sqrt (∑ z ∈ S, f z ^ 2) + Real.sqrt (∑ z ∈ S, g z ^ 2) :=
        Real.sqrt_sq (by positivity)
    _ = l2Norm f + l2Norm g := hrhs

theorem bddAbove_abs_of_support {S : Finset (Site d)} {f : Site d → ℝ}
    (hf : ∀ z ∉ S, f z = 0) :
    BddAbove (Set.range fun z : Site d => |f z|) := by
  refine ⟨∑ z ∈ S, |f z|, ?_⟩
  rintro r ⟨z, rfl⟩
  by_cases hz : z ∈ S
  · exact Finset.single_le_sum (fun i _ => abs_nonneg (f i)) hz
  · show |f z| ≤ ∑ z ∈ S, |f z|
    rw [hf z hz]; simp; positivity

theorem le_supAbs {f : Site d → ℝ} (hbdd : BddAbove (Set.range fun z : Site d => |f z|)) (z : Site d) :
    |f z| ≤ supAbs f := le_ciSup hbdd z

theorem supAbs_add_le_of_support {S : Finset (Site d)} {f g : Site d → ℝ}
    (hf : ∀ z ∉ S, f z = 0) (hg : ∀ z ∉ S, g z = 0) :
    supAbs (fun z => f z + g z) ≤ supAbs f + supAbs g := by
  have hfbdd := bddAbove_abs_of_support hf
  have hgbdd := bddAbove_abs_of_support hg
  unfold supAbs
  refine ciSup_le fun z => ?_
  exact le_trans (abs_add_le (f z) (g z)) (add_le_add (le_supAbs hfbdd z) (le_supAbs hgbdd z))

/-! ### One neighbour step reduces the graph distance to the target by one -/

theorem graphNorm_sub_unit_of_pos {w : Site d} {i : Fin d} (hi : 0 < w i) :
    graphNorm (w - unit i) + 1 = graphNorm w := by
  have hsplit : ∀ v : Site d, graphNorm v = (v i).natAbs + ∑ j ∈ Finset.univ.erase i, (v j).natAbs := by
    intro v
    show (∑ j, (v j).natAbs) = _
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  have hrest : ∀ j ∈ Finset.univ.erase i, ((w - unit i) j).natAbs = (w j).natAbs := by
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [unit, Pi.single_eq_of_ne hji, sub_eq_add_neg]
  have hval : ((w - unit i) i).natAbs + 1 = (w i).natAbs := by
    simp only [Pi.sub_apply, unit, Pi.single_eq_same]
    omega
  rw [hsplit w, hsplit (w - unit i), Finset.sum_congr rfl hrest]
  omega

theorem graphNorm_add_unit_of_neg {w : Site d} {i : Fin d} (hi : w i < 0) :
    graphNorm (w + unit i) + 1 = graphNorm w := by
  have hsplit : ∀ v : Site d, graphNorm v = (v i).natAbs + ∑ j ∈ Finset.univ.erase i, (v j).natAbs := by
    intro v
    show (∑ j, (v j).natAbs) = _
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  have hrest : ∀ j ∈ Finset.univ.erase i, ((w + unit i) j).natAbs = (w j).natAbs := by
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [unit, Pi.single_eq_of_ne hji]
  have hval : ((w + unit i) i).natAbs + 1 = (w i).natAbs := by
    simp only [Pi.add_apply, unit, Pi.single_eq_same]
    omega
  rw [hsplit w, hsplit (w + unit i), Finset.sum_congr rfl hrest]
  omega

theorem exists_nbr_graphNorm_pred {x y : Site d} (hxy : x ≠ y) :
    ∃ x' : Site d, x' ∈ nbrFinset x ∧ graphNorm (x' - y) + 1 = graphNorm (x - y) := by
  have hne : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hex : ∃ i : Fin d, (x - y) i ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hne (funext fun i => h i)
  obtain ⟨i, hi⟩ := hex
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · refine ⟨x + unit i, mem_nbrFinset_iff.mpr ⟨i, Or.inl rfl⟩, ?_⟩
    have hval : (x + unit i) - y = (x - y) + unit i := by abel
    rw [hval]
    exact graphNorm_add_unit_of_neg hneg
  · refine ⟨x - unit i, mem_nbrFinset_iff.mpr ⟨i, Or.inr rfl⟩, ?_⟩
    have hval : (x - unit i) - y = (x - y) - unit i := by abel
    rw [hval]
    exact graphNorm_sub_unit_of_pos hpos

theorem supNorm_sub_le_one_of_nbr {x x' : Site d} (h : x' ∈ nbrFinset x) :
    supNorm (x - x') ≤ 1 := by
  rw [supNorm_le_iff]
  intro i
  have h1 : |x' i - x i| ≤ (1:ℤ) := abs_sub_le_one_of_mem_nbrFinset h i
  rw [abs_sub_comm] at h1
  simpa using h1

theorem nbrFinset_sub_mem {x x' z : Site d} (h : x' ∈ nbrFinset x) :
    x' - z ∈ nbrFinset (x - z) := by
  obtain ⟨i, hi | hi⟩ := mem_nbrFinset_iff.mp h
  · exact mem_nbrFinset_iff.mpr ⟨i, Or.inl (by rw [hi]; abel)⟩
  · exact mem_nbrFinset_iff.mpr ⟨i, Or.inr (by rw [hi]; abel)⟩

theorem abs_green_nbr_diff_le {C : ℝ} (hgrad : ∀ m : ℕ, 1 ≤ m → ∀ y z : Site d,
      z ∈ nbrFinset y → |green d m y - green d m z| ≤ C * (1 + (graphNorm y : ℝ)) ^ (1 - (d:ℝ)))
    {n : ℕ} (hn : 1 ≤ n) {x x' : Site d} (hx' : x' ∈ nbrFinset x) (z : Site d) :
    |green d n (x - z) - green d n (x' - z)| ≤ C * (1 + (graphNorm (x - z) : ℝ)) ^ (1 - (d:ℝ)) :=
  hgrad n hn (x - z) (x' - z) (nbrFinset_sub_mem hx')

/-! ### The shell sum `Σ (1+k)^(2(1-d))`, dimension three and above -/

theorem sum_sq_rpow_le (hd3 : 3 ≤ d) (n : ℕ) :
    ∑ y ∈ boxFinset (0 : Site d) n, ((1 + (supNorm y : ℝ)) ^ ((1:ℝ) - (d:ℝ))) ^ 2
      ≤ 1 + 2 * (d:ℝ) * 2 ^ (d - 1) := by
  have hd1 : 1 ≤ d := by omega
  set f : ℕ → ℝ := fun k => ((1 + (k:ℝ)) ^ ((1:ℝ) - (d:ℝ))) ^ 2 with hfdef
  have hradial : ∑ y ∈ boxFinset (0 : Site d) n, f (supNorm y)
      = f 0 + ∑ k ∈ Finset.Icc 1 n, (shellCard d k : ℝ) * f k := sum_box_radial f n
  have hf0 : f 0 = 1 := by rw [hfdef]; norm_num
  set K : ℝ := 2 * (d:ℝ) * 2 ^ (d - 1) with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  have hterm : ∀ k ∈ Finset.Icc 1 n, (shellCard d k : ℝ) * f k ≤ K * (1 + (k:ℝ)) ^ (1 - (d:ℝ)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have h1 : (shellCard d k : ℝ) * f k ≤ (2 * (d:ℝ) * (2 * (k:ℝ) + 1) ^ (d - 1)) * f k :=
      mul_le_mul_of_nonneg_right (shellCard_le d hk.1) (by rw [hfdef]; positivity)
    have h2 : (2 * (k:ℝ) + 1) ^ (d - 1) ≤ 2 ^ (d - 1) * (1 + (k:ℝ)) ^ (d - 1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have hfk : 0 ≤ f k := by rw [hfdef]; positivity
    have h3 : (2 * (d:ℝ) * (2 * (k:ℝ) + 1) ^ (d - 1)) * f k
        ≤ (2 * (d:ℝ) * (2 ^ (d - 1) * (1 + (k:ℝ)) ^ (d - 1))) * f k := by
      refine mul_le_mul_of_nonneg_right ?_ hfk
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : (2 * (d:ℝ) * (2 ^ (d - 1) * (1 + (k:ℝ)) ^ (d - 1))) * f k
        = K * (1 + (k:ℝ)) ^ (1 - (d:ℝ)) := by
      rw [hfdef, hKdef, ← rpow_shell_combine hd1 k]
      ring
    linarith
  have hsum_shell : ∑ k ∈ Finset.Icc 1 n, (shellCard d k : ℝ) * f k
      ≤ ∑ k ∈ Finset.Icc 1 n, K * (1 + (k:ℝ)) ^ (1 - (d:ℝ)) :=
    Finset.sum_le_sum hterm
  have hpow : ∀ k : ℕ, (1 + (k:ℝ)) ^ (1 - (d:ℝ)) ≤ 1 / ((k:ℝ) + 1) ^ 2 := by
    intro k
    have hknn : (0:ℝ) ≤ (k:ℝ) := by positivity
    have hx : (1:ℝ) ≤ 1 + (k:ℝ) := by linarith
    have hexp : (1:ℝ) - (d:ℝ) ≤ -2 := by
      have : (3:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd3
      linarith
    have hle : (1 + (k:ℝ)) ^ (1 - (d:ℝ)) ≤ (1 + (k:ℝ)) ^ (-2:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx hexp
    have hval : (1 + (k:ℝ)) ^ (-2:ℝ) = 1 / ((k:ℝ) + 1) ^ 2 := by
      rw [show (-2:ℝ) = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_natCast,
        one_div]
      congr 2
      ring
    rw [hval] at hle
    exact hle
  have hone : ∑ k ∈ Finset.Icc 1 n, K * (1 + (k:ℝ)) ^ (1 - (d:ℝ)) ≤ K := by
    rw [← Finset.mul_sum]
    calc K * ∑ k ∈ Finset.Icc 1 n, (1 + (k:ℝ)) ^ (1 - (d:ℝ))
        ≤ K * ∑ k ∈ Finset.Icc 1 n, 1 / ((k:ℝ) + 1) ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hpow k) hKnn
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left (sum_inv_sq_succ_le_one n) hKnn
      _ = K := by ring
  rw [hradial, hf0]
  linarith

/-! ### The one-step spatial comparison, dimension three and above -/

theorem exists_green_space_step_l2_bound (hd3 : 3 ≤ d) {C : ℝ} (hC : 0 < C)
    (hgrad : ∀ m : ℕ, 1 ≤ m → ∀ y z : Site d,
      z ∈ nbrFinset y → |green d m y - green d m z| ≤ C * (1 + (graphNorm y : ℝ)) ^ (1 - (d:ℝ)))
    {n : ℕ} (hn : 1 ≤ n) {x x' : Site d} (hx' : x' ∈ nbrFinset x) :
    l2Norm (fun z => green d n (x - z) - green d n (x' - z))
      ≤ C * Real.sqrt (1 + 2 * (d:ℝ) * 2 ^ (d - 1)) := by
  have hd1 : 1 ≤ d := by omega
  set f : Site d → ℝ := fun z => green d n (x - z) - green d n (x' - z) with hfdef
  have hzero : ∀ z ∉ boxFinset x (n + 1), f z = 0 := by
    intro z hz
    exact green_diff_eq_zero_of_notMem_box (by rw [sub_self, supNorm_zero']; omega) (by
      have := supNorm_sub_le_one_of_nbr hx'; omega) hz
  have hsq : ∀ z : Site d, f z ^ 2 ≤ C ^ 2 * ((1 + (supNorm (x - z) : ℝ)) ^ (1 - (d:ℝ))) ^ 2 := by
    intro z
    have h1 : |f z| ≤ C * (1 + (graphNorm (x - z) : ℝ)) ^ (1 - (d:ℝ)) :=
      abs_green_nbr_diff_le hgrad hn hx' z
    have hanti : (1 + (graphNorm (x - z) : ℝ)) ^ (1 - (d:ℝ))
        ≤ (1 + (supNorm (x - z) : ℝ)) ^ (1 - (d:ℝ)) :=
      rpow_radial_antitone hd1 (supNorm_le_graphNorm (x - z))
    have h2 : |f z| ≤ C * (1 + (supNorm (x - z) : ℝ)) ^ (1 - (d:ℝ)) :=
      le_trans h1 (mul_le_mul_of_nonneg_left hanti hC.le)
    have hsqle : f z ^ 2 ≤ (C * (1 + (supNorm (x - z) : ℝ)) ^ (1 - (d:ℝ))) ^ 2 := by
      have := sq_abs (f z)
      nlinarith [abs_nonneg (f z), h2, hC.le,
        Real.rpow_pos_of_pos (show (0:ℝ) < 1 + (supNorm (x - z) : ℝ) by positivity) (1 - (d:ℝ))]
    calc f z ^ 2 ≤ (C * (1 + (supNorm (x - z) : ℝ)) ^ (1 - (d:ℝ))) ^ 2 := hsqle
      _ = C ^ 2 * ((1 + (supNorm (x - z) : ℝ)) ^ (1 - (d:ℝ))) ^ 2 := by ring
  have hstep : (∑' z : Site d, f z ^ 2) ≤ C ^ 2 * (1 + 2 * (d:ℝ) * 2 ^ (d - 1)) := by
    have heq : (∑' z : Site d, f z ^ 2) = ∑ z ∈ boxFinset x (n + 1), f z ^ 2 :=
      tsum_eq_sum (fun z hz => by rw [hzero z hz]; ring)
    rw [heq]
    calc ∑ z ∈ boxFinset x (n + 1), f z ^ 2
        ≤ ∑ z ∈ boxFinset x (n + 1),
            C ^ 2 * ((1 + (supNorm (x - z) : ℝ)) ^ (1 - (d:ℝ))) ^ 2 :=
          Finset.sum_le_sum fun z _ => hsq z
      _ = C ^ 2 * ∑ z ∈ boxFinset x (n + 1), ((1 + (supNorm (x - z) : ℝ)) ^ (1 - (d:ℝ))) ^ 2 := by
          rw [Finset.mul_sum]
      _ = C ^ 2 * ∑ w ∈ boxFinset (0 : Site d) (n + 1), ((1 + (supNorm w : ℝ)) ^ (1 - (d:ℝ))) ^ 2 := by
          rw [sum_boxFinset_shift x (n + 1) (fun k => ((1 + (k : ℝ)) ^ (1 - (d:ℝ))) ^ 2)]
      _ ≤ C ^ 2 * (1 + 2 * (d:ℝ) * 2 ^ (d - 1)) :=
          mul_le_mul_of_nonneg_left (sum_sq_rpow_le hd3 (n + 1)) (sq_nonneg C)
  unfold l2Norm
  rw [hfdef] at hstep ⊢
  calc Real.sqrt (∑' z : Site d, f z ^ 2) ≤ Real.sqrt (C ^ 2 * (1 + 2 * (d:ℝ) * 2 ^ (d - 1))) := by
        rw [hfdef]; exact Real.sqrt_le_sqrt hstep
    _ = C * Real.sqrt (1 + 2 * (d:ℝ) * 2 ^ (d - 1)) := by
        rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC.le]

theorem exists_green_space_step_sup_bound {C : ℝ} (hC : 0 < C) (hd1 : 1 ≤ d)
    (hgrad : ∀ m : ℕ, 1 ≤ m → ∀ y z : Site d,
      z ∈ nbrFinset y → |green d m y - green d m z| ≤ C * (1 + (graphNorm y : ℝ)) ^ (1 - (d:ℝ)))
    {n : ℕ} (hn : 1 ≤ n) {x x' : Site d} (hx' : x' ∈ nbrFinset x) :
    supAbs (fun z => green d n (x - z) - green d n (x' - z)) ≤ C := by
  have hpt : ∀ z : Site d, |green d n (x - z) - green d n (x' - z)| ≤ C := by
    intro z
    refine le_trans (abs_green_nbr_diff_le hgrad hn hx' z) ?_
    have hbase : (1:ℝ) ≤ 1 + (graphNorm (x - z) : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) (graphNorm (x - z)); linarith
    have hexp : (1:ℝ) - (d:ℝ) ≤ 0 := by
      have : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd1
      linarith
    have hrp : (1 + (graphNorm (x - z) : ℝ)) ^ (1 - (d:ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hbase hexp
    nlinarith
  unfold supAbs
  exact ciSup_le hpt

/-! ### The `L`-step space comparison, dimension three and above -/

theorem exists_green_space_l2_bound (hd3 : 3 ≤ d) {C : ℝ} (hC : 0 < C)
    (hgrad : ∀ m : ℕ, 1 ≤ m → ∀ y z : Site d,
      z ∈ nbrFinset y → |green d m y - green d m z| ≤ C * (1 + (graphNorm y : ℝ)) ^ (1 - (d:ℝ)))
    {n : ℕ} (hn : 1 ≤ n) :
    ∀ L : ℕ, ∀ x y : Site d, graphNorm (x - y) = L →
      l2Norm (fun z => green d n (x - z) - green d n (y - z))
        ≤ (L : ℝ) * (C * Real.sqrt (1 + 2 * (d:ℝ) * 2 ^ (d - 1))) := by
  intro L
  induction L with
  | zero =>
      intro x y hL
      have hxy : x = y := sub_eq_zero.mp (graphNorm_eq_zero_iff.mp hL)
      subst hxy
      have hz0 : (fun z => green d n (x - z) - green d n (x - z)) = fun _ : Site d => (0:ℝ) := by
        funext z; ring
      rw [hz0]
      have h0 : l2Norm (fun _ : Site d => (0:ℝ)) = 0 := by unfold l2Norm; simp
      rw [h0]; positivity
  | succ L ih =>
      intro x y hL
      have hxy : x ≠ y := by
        intro hcontra
        have hz0 : graphNorm (0 : Site d) = 0 := graphNorm_eq_zero_iff.mpr rfl
        rw [hcontra, sub_self, hz0] at hL
        omega
      obtain ⟨x', hx', hpred⟩ := exists_nbr_graphNorm_pred hxy
      have hLx' : graphNorm (x' - y) = L := by omega
      have hIH := ih x' y hLx'
      have hone := exists_green_space_step_l2_bound hd3 hC hgrad hn hx'
      set R : ℕ := n + L + 2 with hRdef
      have hS1 : ∀ z ∉ boxFinset x R, green d n (x - z) - green d n (x' - z) = 0 := by
        intro z hz
        refine green_diff_eq_zero_of_notMem_box ?_ ?_ hz
        · rw [sub_self, supNorm_zero']; omega
        · have := supNorm_sub_le_one_of_nbr hx'; omega
      have hS2 : ∀ z ∉ boxFinset x R, green d n (x' - z) - green d n (y - z) = 0 := by
        intro z hz
        refine green_diff_eq_zero_of_notMem_box ?_ ?_ hz
        · have hxx' := supNorm_sub_le_one_of_nbr hx'; omega
        · have hxy' : supNorm (x - y) ≤ L + 1 := by
            have := supNorm_le_graphNorm (x - y)
            omega
          omega
      have hcomb : l2Norm (fun z => green d n (x - z) - green d n (y - z))
          ≤ l2Norm (fun z => green d n (x - z) - green d n (x' - z))
            + l2Norm (fun z => green d n (x' - z) - green d n (y - z)) := by
        have heq : (fun z => (green d n (x - z) - green d n (x' - z))
              + (green d n (x' - z) - green d n (y - z)))
            = fun z => green d n (x - z) - green d n (y - z) := by
          funext z; ring
        calc l2Norm (fun z => green d n (x - z) - green d n (y - z))
            = l2Norm (fun z => (green d n (x - z) - green d n (x' - z))
                + (green d n (x' - z) - green d n (y - z))) := by rw [heq]
          _ ≤ l2Norm (fun z => green d n (x - z) - green d n (x' - z))
                + l2Norm (fun z => green d n (x' - z) - green d n (y - z)) :=
              l2Norm_add_le_of_support hS1 hS2
      calc l2Norm (fun z => green d n (x - z) - green d n (y - z))
          ≤ l2Norm (fun z => green d n (x - z) - green d n (x' - z))
              + l2Norm (fun z => green d n (x' - z) - green d n (y - z)) := hcomb
        _ ≤ C * Real.sqrt (1 + 2 * (d:ℝ) * 2 ^ (d - 1))
              + (L : ℝ) * (C * Real.sqrt (1 + 2 * (d:ℝ) * 2 ^ (d - 1))) :=
            add_le_add hone hIH
        _ = ((L : ℝ) + 1) * (C * Real.sqrt (1 + 2 * (d:ℝ) * 2 ^ (d - 1))) := by ring
        _ = ((L + 1 : ℕ) : ℝ) * (C * Real.sqrt (1 + 2 * (d:ℝ) * 2 ^ (d - 1))) := by push_cast; ring

theorem exists_green_space_sup_bound {C : ℝ} (hC : 0 < C) (hd1 : 1 ≤ d)
    (hgrad : ∀ m : ℕ, 1 ≤ m → ∀ y z : Site d,
      z ∈ nbrFinset y → |green d m y - green d m z| ≤ C * (1 + (graphNorm y : ℝ)) ^ (1 - (d:ℝ)))
    {n : ℕ} (hn : 1 ≤ n) :
    ∀ L : ℕ, ∀ x y : Site d, graphNorm (x - y) = L →
      supAbs (fun z => green d n (x - z) - green d n (y - z)) ≤ (L : ℝ) * C := by
  intro L
  induction L with
  | zero =>
      intro x y hL
      have hxy : x = y := sub_eq_zero.mp (graphNorm_eq_zero_iff.mp hL)
      subst hxy
      have hz0 : (fun z => green d n (x - z) - green d n (x - z)) = fun _ : Site d => (0:ℝ) := by
        funext z; ring
      rw [hz0]
      have h0 : supAbs (fun _ : Site d => (0:ℝ)) = 0 := by unfold supAbs; simp
      rw [h0]; positivity
  | succ L ih =>
      intro x y hL
      have hxy : x ≠ y := by
        intro hcontra
        have hz0 : graphNorm (0 : Site d) = 0 := graphNorm_eq_zero_iff.mpr rfl
        rw [hcontra, sub_self, hz0] at hL
        omega
      obtain ⟨x', hx', hpred⟩ := exists_nbr_graphNorm_pred hxy
      have hLx' : graphNorm (x' - y) = L := by omega
      have hIH := ih x' y hLx'
      have hone := exists_green_space_step_sup_bound hC hd1 hgrad hn hx'
      set R : ℕ := n + L + 2 with hRdef
      have hS1 : ∀ z ∉ boxFinset x R, green d n (x - z) - green d n (x' - z) = 0 := by
        intro z hz
        refine green_diff_eq_zero_of_notMem_box ?_ ?_ hz
        · rw [sub_self, supNorm_zero']; omega
        · have := supNorm_sub_le_one_of_nbr hx'; omega
      have hS2 : ∀ z ∉ boxFinset x R, green d n (x' - z) - green d n (y - z) = 0 := by
        intro z hz
        refine green_diff_eq_zero_of_notMem_box ?_ ?_ hz
        · have hxx' := supNorm_sub_le_one_of_nbr hx'; omega
        · have hxy' : supNorm (x - y) ≤ L + 1 := by
            have := supNorm_le_graphNorm (x - y)
            omega
          omega
      have hcomb : supAbs (fun z => green d n (x - z) - green d n (y - z))
          ≤ supAbs (fun z => green d n (x - z) - green d n (x' - z))
            + supAbs (fun z => green d n (x' - z) - green d n (y - z)) := by
        have heq : (fun z => (green d n (x - z) - green d n (x' - z))
              + (green d n (x' - z) - green d n (y - z)))
            = fun z => green d n (x - z) - green d n (y - z) := by
          funext z; ring
        calc supAbs (fun z => green d n (x - z) - green d n (y - z))
            = supAbs (fun z => (green d n (x - z) - green d n (x' - z))
                + (green d n (x' - z) - green d n (y - z))) := by rw [heq]
          _ ≤ supAbs (fun z => green d n (x - z) - green d n (x' - z))
                + supAbs (fun z => green d n (x' - z) - green d n (y - z)) :=
              supAbs_add_le_of_support hS1 hS2
      calc supAbs (fun z => green d n (x - z) - green d n (y - z))
          ≤ supAbs (fun z => green d n (x - z) - green d n (x' - z))
              + supAbs (fun z => green d n (x' - z) - green d n (y - z)) := hcomb
        _ ≤ C + (L : ℝ) * C := add_le_add hone hIH
        _ = ((L : ℝ) + 1) * C := by ring
        _ = ((L + 1 : ℕ) : ℝ) * C := by push_cast; ring

/-! ### The External-facing wrappers -/

/-- **The space-direction translated-kernel-difference comparison for the cited External
`Parking.External.GreenGradient`, `l2Norm` form, dimension three and above.** -/
theorem exists_green_space_shift_l2_bound (hd3 : 3 ≤ d) (hgrad : Parking.External.GreenGradient d) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n → ∀ x y : Site d,
      l2Norm (fun z => green d n (x - z) - green d n (y - z)) ≤ K * (graphNorm (x - y) : ℝ) := by
  obtain ⟨C, hC, hgradraw⟩ := hgrad
  refine ⟨C * Real.sqrt (1 + 2 * (d:ℝ) * 2 ^ (d - 1)), by positivity, fun n hn x y => ?_⟩
  have hb := exists_green_space_l2_bound hd3 hC hgradraw hn (graphNorm (x - y)) x y rfl
  linarith [hb]

/-- **The space-direction translated-kernel-difference comparison for the cited External
`Parking.External.GreenGradient`, `supAbs` form, dimension two and above.** -/
theorem exists_green_space_shift_sup_bound (hd1 : 1 ≤ d) (hgrad : Parking.External.GreenGradient d) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n → ∀ x y : Site d,
      supAbs (fun z => green d n (x - z) - green d n (y - z)) ≤ K * (graphNorm (x - y) : ℝ) := by
  obtain ⟨C, hC, hgradraw⟩ := hgrad
  refine ⟨C, hC, fun n hn x y => ?_⟩
  have hb := exists_green_space_sup_bound hC hd1 hgradraw hn (graphNorm (x - y)) x y rfl
  linarith [hb]

end Parking

end
