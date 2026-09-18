/-
**The discrete maximal inequality for the linear membrane field over a growing box.**

The discrete cutoff-to-true bound `Parking.abs_stoppingSup_sub_cutoffStoppingSup_le'`
(`Parking/Support/SpatialStoppingCutoff.lean`) needs a GLOBAL deterministic bound on the reward
`-linPotential η (n0-k) y`, which is only a.s. locally finite; turning its pathwise bound (with a
random, uncontrolled constant `M(η)`) into a probability-`0` statement needs an independent
maximal inequality for `sup_{y : graphNorm y ≤ A} |linPotential η n y|`.  This module supplies
it, via a union bound over the FINITE box `Parking.boxFinset 0 A` and the Bernstein-type
two-point tail `Parking.exists_linPotential_increment_concentration` (`Parking/Support/
LinIncrementConcentration.lean`), applied per lattice point against the base point at time `0`
(where `linPotential` is identically zero, `Parking.linPotential_zero`, so no separate base-point
estimate is needed).

The per-point tail (`Parking.exists_linPotential_point_tail`) needs the kernel-norm quantities
`l2Norm`/`supAbs (fun z => green d n (y - z))`, uniform in the SITE `y`: bounded here (`Parking.
l2Norm_green_le`/`Parking.supAbs_green_le`), for every `y` and every `n ≥ 1`, by a constant
(depending only on `d`) times `n`, via the SAME triangle-inequality route
`Parking/Support/LinGridGap.lean` already uses (`Parking.l2Norm_add_le_of_support`/
`supAbs_add_le_of_support`, `Parking/Support/SpatGreenShift.lean`), splitting `green d n (y-·)`
into its own two-time difference from the trivial base horizon `1` (`Parking.
exists_green_time_shift_l2_bound`/`_sup_bound`, `Parking/Support/LinTimeShift.lean`, GENERAL `d`,
no `1 ≤ d ≤ 3` restriction needed here) plus the exactly-computed single-spike norm at horizon `1`
(`green d 1 x = if x = 0 then 1 else 0`, `Parking.green_one_apply`).  Both bounds are strict
lower bounds too (`Parking.l2Norm_green_pos`/`supAbs_green_pos`, from the diagonal term
`green d n 0 ≥ 1`), needed to invert the ratio direction in the union-bound step: an upper bound
`L ≤ B` on a POSITIVE `L` gives `r²/B² ≤ r²/L²`, which would be false at the Lean junk value
`L = 0`.

The union bound (`Parking.exists_linPotential_maximal_tail`) folds the two `d`-dependent kernel-
norm constants into a single rate via `Parking.Generic.MinProduct.min_mul_min_le` (an arithmetic
fact with no repository-specific object in its statement, so it lives under `Parking/Generic/`),
producing the clean schematic form
`C · (2A+1)^d · exp(-c · min(M²/n², M/n))` for the box `boxFinset 0 A` (`A : ℕ`, cardinality
`Parking.card_boxFinset`), `n ≥ 1`, `M > 0`.  The raw exceedance threshold this licenses is
`M = Θ(n·√(d log A))`: for `n = ⌊sR²⌋₊ ~ R²` and `A = A(R)` any polynomial in `R`, taking
`M(R) := n·√((d+1)·log(A(R))/c)` makes `C·(2A+1)^d·exp(-c·M²/n²) = O(A^{-1}) → 0`, which is
consistent with the cutoff-error rate `n0·d²/A²`: a polynomial-degree choice of `A(R)` beats it
once `A(R)` grows fast enough relative to `n0 ~ R²`.
-/
import Parking.Support.LinIncrementConcentration
import Parking.Support.LinMeanMoment
import Parking.Support.LinTimeShift
import Parking.Support.SpatGreenShift
import Parking.Support.GreenIncrement
import Parking.Support.MatchedUniform
import Parking.Generic.MinProduct

noncomputable section

namespace Parking

open MeasureTheory LatticeProb Finset Parking.Generic.MinProduct

variable {d : ℕ}

/-! ### The truncated Green function at horizon `0` is identically zero -/

theorem green_zero_eq (w : Site d) : green d 0 w = 0 := by unfold green; simp

/-! ### The diagonal term `green d n 0 ≥ 1`, for `n ≥ 1` -/

theorem one_le_green_zero (n : ℕ) (hn : 1 ≤ n) : (1 : ℝ) ≤ green d n (0 : Site d) := by
  unfold green
  have h0 : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr hn
  have hnn : ∀ j ∈ Finset.range n, (0 : ℝ) ≤ heat d j (0 : Site d) := fun j _ => by
    rw [heat_eq_srwHeat]; exact srwHeat_nonneg j 0
  have hterm : heat d 0 (0 : Site d) = 1 := by unfold heat; simp
  calc (1 : ℝ) = heat d 0 (0 : Site d) := hterm.symm
    _ ≤ ∑ j ∈ Finset.range n, heat d j (0 : Site d) := Finset.single_le_sum hnn h0

/-! ### Positivity of the `l2Norm`/`supAbs` of the truncated Green function, `n ≥ 1` -/

/-- **Positivity of the `l2Norm`**, from the diagonal term `z = x` alone. -/
theorem l2Norm_green_pos (n : ℕ) (hn : 1 ≤ n) (x : Site d) :
    0 < l2Norm (fun z => green d n (x - z)) := by
  have hle : (fun z : Site d => (green d n (x - z)) ^ 2) x
      ≤ ∑' z : Site d, (green d n (x - z)) ^ 2 := by
    have hS : ∀ z ∉ boxFinset x n, (green d n (x - z)) ^ 2 = 0 := fun z hz => by
      rw [green_eq_zero_of_not_mem_boxFinset hz]; ring
    rw [tsum_eq_sum hS]
    refine Finset.single_le_sum (f := fun z => (green d n (x - z)) ^ 2)
      (fun i _ => sq_nonneg _) ?_
    rw [mem_boxFinset_iff]; intro i; simp
  have hbase : (1 : ℝ) ≤ green d n (x - x) := by rw [sub_self]; exact one_le_green_zero n hn
  have h1 : (1 : ℝ) ≤ green d n (x - x) ^ 2 := by nlinarith [hbase]
  have h2 : (1 : ℝ) ≤ ∑' z : Site d, (green d n (x - z)) ^ 2 := le_trans h1 hle
  unfold l2Norm
  exact Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one h2)

/-- **Positivity of `supAbs`**, from the diagonal term `z = x` alone. -/
theorem supAbs_green_pos (n : ℕ) (hn : 1 ≤ n) (x : Site d) :
    0 < supAbs (fun z => green d n (x - z)) := by
  have hbdd : BddAbove (Set.range fun z : Site d => |green d n (x - z)|) :=
    bddAbove_abs_of_support (S := boxFinset x n)
      (fun z hz => green_eq_zero_of_not_mem_boxFinset hz)
  have hbase : (1 : ℝ) ≤ green d n (x - x) := by rw [sub_self]; exact one_le_green_zero n hn
  have hx := le_supAbs hbdd x
  have hle : (1 : ℝ) ≤ |green d n (x - x)| := le_trans hbase (le_abs_self _)
  linarith [hx, hle]

/-! ### The exact single-spike norm at horizon `1` -/

theorem l2Norm_green_one_eq (x : Site d) : l2Norm (fun z => green d 1 (x - z)) = 1 := by
  have hpt : ∀ z : Site d, green d 1 (x - z) = if z = x then (1 : ℝ) else 0 := by
    intro z; rw [green_one_apply]
    by_cases h : z = x
    · simp [h]
    · have : x - z ≠ 0 := by intro hc; apply h; exact (sub_eq_zero.mp hc).symm
      simp [this, h]
  unfold l2Norm
  have hsq : (fun z : Site d => green d 1 (x - z) ^ 2) = fun z => if z = x then (1 : ℝ) else 0 := by
    funext z; rw [hpt z]; by_cases h : z = x <;> simp [h]
  rw [hsq, tsum_ite_eq x (fun _ => (1 : ℝ))]
  exact Real.sqrt_one

theorem supAbs_green_one_eq (x : Site d) : supAbs (fun z => green d 1 (x - z)) = 1 := by
  have hpt : ∀ z : Site d, green d 1 (x - z) = if z = x then (1 : ℝ) else 0 := by
    intro z; rw [green_one_apply]
    by_cases h : z = x
    · simp [h]
    · have : x - z ≠ 0 := by intro hc; apply h; exact (sub_eq_zero.mp hc).symm
      simp [this, h]
  have hbdd : ∀ z ∉ ({x} : Finset (Site d)), green d 1 (x - z) = 0 := by
    intro z hz; rw [hpt z]
    simp only [Finset.mem_singleton] at hz; simp [hz]
  have hbddAbove := bddAbove_abs_of_support hbdd
  unfold supAbs
  refine le_antisymm (ciSup_le fun z => ?_) ?_
  · show |green d 1 (x - z)| ≤ 1
    rw [hpt z]; by_cases h : z = x <;> simp [h]
  · have hx := le_ciSup hbddAbove x
    have heq : |green d 1 (x - x)| = 1 := by rw [hpt x]; simp
    rw [heq] at hx; exact hx

theorem notMem_boxFinset_one_of_notMem_boxFinset_n {n : ℕ} (hn : 1 ≤ n) {x z : Site d}
    (hz : z ∉ boxFinset x n) : z ∉ boxFinset x 1 := by
  intro hmem; apply hz
  rw [mem_boxFinset_iff]
  intro i
  exact le_trans (mem_boxFinset_iff.mp hmem i) (by exact_mod_cast hn)

/-! ### The uniform-in-`x`, linear-in-`n` bounds on the truncated Green function -/

/-- **The `l2Norm` of the truncated Green function, uniform in the site `x`, linear in `n`.**
Triangle inequality against the exactly-computed base value at horizon `1`. -/
theorem l2Norm_green_le (hd1 : 1 ≤ d) (n : ℕ) (hn : 1 ≤ n) (x : Site d) :
    l2Norm (fun z => green d n (x - z))
      ≤ (1 + Real.sqrt (LatticeProb.diagConst d / Real.sqrt 2 ^ d)) * n := by
  have hd0 : 0 < d := hd1
  have hf0 : ∀ z ∉ boxFinset x n, (fun z => green d n (x - z) - green d 1 (x - z)) z = 0 := by
    intro z hz; show green d n (x - z) - green d 1 (x - z) = 0
    have h1 : green d n (x - z) = 0 := green_eq_zero_of_not_mem_boxFinset hz
    have h2' : green d 1 (x - z) = 0 :=
      green_eq_zero_of_not_mem_boxFinset (notMem_boxFinset_one_of_notMem_boxFinset_n hn hz)
    rw [h1, h2']; ring
  have hg0 : ∀ z ∉ boxFinset x n, (fun z => green d 1 (x - z)) z = 0 := fun z hz =>
    green_eq_zero_of_not_mem_boxFinset (notMem_boxFinset_one_of_notMem_boxFinset_n hn hz)
  have htri := l2Norm_add_le_of_support hf0 hg0
  have heq : (fun z => (fun z => green d n (x - z) - green d 1 (x - z)) z
      + (fun z => green d 1 (x - z)) z) = fun z => green d n (x - z) := by
    funext z; show green d n (x - z) - green d 1 (x - z) + green d 1 (x - z) = green d n (x - z)
    ring
  rw [heq] at htri
  have hdiffb := exists_green_time_shift_l2_bound hd0 (le_refl 1) hn x
  simp only [Nat.cast_one, mul_one] at hdiffb
  have hbase := l2Norm_green_one_eq x
  have hspos : (0 : ℝ) ≤ Real.sqrt (LatticeProb.diagConst d / Real.sqrt 2 ^ d) := Real.sqrt_nonneg _
  have hcomb : l2Norm (fun z => green d n (x - z))
      ≤ ((n : ℝ) - 1) * Real.sqrt (LatticeProb.diagConst d / Real.sqrt 2 ^ d) + 1 := by
    calc l2Norm (fun z => green d n (x - z))
        ≤ l2Norm (fun z => green d n (x - z) - green d 1 (x - z))
            + l2Norm (fun z => green d 1 (x - z)) := htri
      _ ≤ ((n : ℝ) - 1) * Real.sqrt (LatticeProb.diagConst d / Real.sqrt 2 ^ d) + 1 := by
          rw [hbase]; linarith [hdiffb]
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [hcomb, hspos, hnR]

/-- **The `supAbs` of the truncated Green function, uniform in the site `x`, linear in `n`.** -/
theorem supAbs_green_le (hd1 : 1 ≤ d) (n : ℕ) (hn : 1 ≤ n) (x : Site d) :
    supAbs (fun z => green d n (x - z)) ≤ (1 + LatticeProb.diagConst d) * n := by
  have hd0 : 0 < d := hd1
  have hf0 : ∀ z ∉ boxFinset x n, (fun z => green d n (x - z) - green d 1 (x - z)) z = 0 := by
    intro z hz; show green d n (x - z) - green d 1 (x - z) = 0
    have h1 : green d n (x - z) = 0 := green_eq_zero_of_not_mem_boxFinset hz
    have h2' : green d 1 (x - z) = 0 :=
      green_eq_zero_of_not_mem_boxFinset (notMem_boxFinset_one_of_notMem_boxFinset_n hn hz)
    rw [h1, h2']; ring
  have hg0 : ∀ z ∉ boxFinset x n, (fun z => green d 1 (x - z)) z = 0 := fun z hz =>
    green_eq_zero_of_not_mem_boxFinset (notMem_boxFinset_one_of_notMem_boxFinset_n hn hz)
  have htri := supAbs_add_le_of_support hf0 hg0
  have heq : (fun z => (fun z => green d n (x - z) - green d 1 (x - z)) z
      + (fun z => green d 1 (x - z)) z) = fun z => green d n (x - z) := by
    funext z; show green d n (x - z) - green d 1 (x - z) + green d 1 (x - z) = green d n (x - z)
    ring
  rw [heq] at htri
  have hdiffb := exists_green_time_shift_sup_bound hd0 (le_refl 1) hn x
  simp only [Nat.cast_one, Real.sqrt_one, one_pow] at hdiffb
  have hbase := supAbs_green_one_eq x
  have hcomb : supAbs (fun z => green d n (x - z)) ≤ ((n : ℝ) - 1) * LatticeProb.diagConst d + 1 := by
    calc supAbs (fun z => green d n (x - z))
        ≤ supAbs (fun z => green d n (x - z) - green d 1 (x - z))
            + supAbs (fun z => green d 1 (x - z)) := htri
      _ ≤ ((n : ℝ) - 1) * LatticeProb.diagConst d + 1 := by rw [hbase]; linarith [hdiffb]
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [hcomb, hnR, LatticeProb.diagConst_pos d]

/-! ### The per-point tail bound -/

/-- **The per-point tail bound for `linPotential`.**  `Parking.
exists_linPotential_increment_concentration` at the base point `(m := 0, y := 0)`: `linPotential
η 0 0 = 0` identically (`Parking.linPotential_zero`), and its mean is `0` too (trivially, since
the quantity is identically zero), so the two-point concentration collapses to a genuine
ONE-point tail for `linPotential η n y` itself, with no separate base-point estimate needed. -/
theorem exists_linPotential_point_tail (hd1 : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (y : Site d) (r : ℝ), 0 < r →
      ((iidLaw d (realLaw ν)) {η | r ≤ |linPotential η n y|}).toReal
        ≤ C * Real.exp (-(c * min (r ^ 2 / (l2Norm (fun z => green d n (y - z))) ^ 2)
            (r / supAbs (fun z => green d n (y - z))))) := by
  haveI := hν.prob
  haveI hν0P : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI hμP : IsProbabilityMeasure (iidLaw d (realLaw ν)) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : Site d => realLaw ν))
  obtain ⟨θ, hθ, hexpabs⟩ := realLaw_expMoment ν hν
  obtain ⟨c, C, hc, hC, hmain⟩ :=
    exists_linPotential_increment_concentration hd1 (realLaw ν) θ hθ hexpabs
  refine ⟨c, C, hc, hC, ?_⟩
  intro n hn y r hr
  have hkey := hmain n 0 y (0 : Site d) r hr
  have hmean0 : (∫ η', linPotential η' n y - linPotential η' 0 (0 : Site d)
      ∂(iidLaw d (realLaw ν))) = 0 := by
    have h1 := integral_linPotential_eq_zero_critical ν hν n y
    simp only [linPotential_zero, sub_zero]; exact h1
  rw [hmean0] at hkey
  simp only [sub_zero, linPotential_zero] at hkey
  have hnormEq : (fun z => green d n (y - z) - green d 0 ((0 : Site d) - z))
      = (fun z => green d n (y - z)) := by
    funext z; rw [green_zero_eq]; ring
  rw [hnormEq] at hkey
  rw [← measureReal_def]
  have hstep := ENNReal.toReal_mono ENNReal.ofReal_ne_top hkey
  rwa [ENNReal.toReal_ofReal (by positivity)] at hstep

/-! ### The maximal inequality, assembled by a union bound over `boxFinset 0 A` -/

/-- **The discrete maximal inequality for the linear membrane field over a growing box.**
For `1 ≤ d`, `∃ c C > 0`, for every horizon `n ≥ 1`, every box radius `A : ℕ` and every
threshold `M > 0`, the probability that `linPotential η n ·` exceeds `M` somewhere in
`Parking.boxFinset 0 A` is at most `C · (2A+1)^d · exp(-c · min(M²/n², M/n))` — a union bound
(`Parking.card_boxFinset`) over the per-point tail (`Parking.exists_linPotential_point_tail`),
with the `d`-dependent kernel-norm constants folded into `c` via
`Parking.Generic.MinProduct.min_mul_min_le`.  The sup ranges over the growing but FINITE box, so
the infinite lattice never enters the statement: the maximal inequality is stated directly over
`boxFinset 0 A`. -/
theorem exists_linPotential_maximal_tail (hd1 : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (A : ℕ) (M : ℝ), 0 < M →
      ((iidLaw d (realLaw ν))
          {η | ∃ y ∈ boxFinset (0 : Site d) A, M ≤ |linPotential η n y|}).toReal
        ≤ C * (2 * A + 1) ^ d * Real.exp (-(c * min (M ^ 2 / (n : ℝ) ^ 2) (M / (n : ℝ)))) := by
  haveI := hν.prob
  haveI hν0P : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI hμP : IsProbabilityMeasure (iidLaw d (realLaw ν)) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : Site d => realLaw ν))
  obtain ⟨c0, C0, hc0, hC0, hpt⟩ := exists_linPotential_point_tail hd1 ν hν
  set Cg1 : ℝ := 1 + Real.sqrt (LatticeProb.diagConst d / Real.sqrt 2 ^ d) with hCg1def
  set Cg2 : ℝ := 1 + LatticeProb.diagConst d with hCg2def
  have hCg1pos : 0 < Cg1 := by rw [hCg1def]; positivity
  have hCg2pos : 0 < Cg2 := by
    rw [hCg2def]; have := LatticeProb.diagConst_pos d; linarith
  set κ : ℝ := min (1 / Cg1 ^ 2) (1 / Cg2) with hκdef
  have hκpos : 0 < κ := by
    rw [hκdef]
    exact lt_min (div_pos one_pos (pow_pos hCg1pos 2)) (div_pos one_pos hCg2pos)
  refine ⟨c0 * κ, C0, mul_pos hc0 hκpos, hC0, ?_⟩
  intro n hn A M hM
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hEsub : {η : Site d → ℝ | ∃ y ∈ boxFinset (0 : Site d) A, M ≤ |linPotential η n y|}
      ⊆ ⋃ y ∈ boxFinset (0 : Site d) A, {η : Site d → ℝ | M ≤ |linPotential η n y|} := by
    intro η hη
    obtain ⟨y, hy, hyM⟩ := hη
    exact Set.mem_biUnion hy hyM
  have hstep1 : (iidLaw d (realLaw ν)).real
        {η : Site d → ℝ | ∃ y ∈ boxFinset (0 : Site d) A, M ≤ |linPotential η n y|}
      ≤ (iidLaw d (realLaw ν)).real
        (⋃ y ∈ boxFinset (0 : Site d) A, {η : Site d → ℝ | M ≤ |linPotential η n y|}) :=
    measureReal_mono hEsub (measure_ne_top _ _)
  have hstep2 : (iidLaw d (realLaw ν)).real
        (⋃ y ∈ boxFinset (0 : Site d) A, {η : Site d → ℝ | M ≤ |linPotential η n y|})
      ≤ ∑ y ∈ boxFinset (0 : Site d) A,
          (iidLaw d (realLaw ν)).real {η : Site d → ℝ | M ≤ |linPotential η n y|} :=
    measureReal_biUnion_finset_le _ _
  have hL2b : ∀ y : Site d, l2Norm (fun z => green d n (y - z)) ≤ Cg1 * n :=
    fun y => l2Norm_green_le hd1 n hn y
  have hL2pos : ∀ y : Site d, 0 < l2Norm (fun z => green d n (y - z)) :=
    fun y => l2Norm_green_pos n hn y
  have hSupb : ∀ y : Site d, supAbs (fun z => green d n (y - z)) ≤ Cg2 * n :=
    fun y => supAbs_green_le hd1 n hn y
  have hSuppos : ∀ y : Site d, 0 < supAbs (fun z => green d n (y - z)) :=
    fun y => supAbs_green_pos n hn y
  have hminkey : κ * min (M ^ 2 / (n : ℝ) ^ 2) (M / (n : ℝ))
      ≤ min (M ^ 2 / (Cg1 * n) ^ 2) (M / (Cg2 * n)) := by
    have heq1 : M ^ 2 / (Cg1 * n) ^ 2 = (1 / Cg1 ^ 2) * (M ^ 2 / (n : ℝ) ^ 2) := by
      rw [mul_pow]; field_simp
    have heq2 : M / (Cg2 * n) = (1 / Cg2) * (M / (n : ℝ)) := by field_simp
    rw [heq1, heq2, hκdef]
    exact min_mul_min_le (1 / Cg1 ^ 2) (1 / Cg2) (M ^ 2 / (n : ℝ) ^ 2) (M / (n : ℝ))
      (by positivity) (by positivity) (by positivity) (by positivity)
  have hpoint : ∀ y ∈ boxFinset (0 : Site d) A,
      (iidLaw d (realLaw ν)).real {η : Site d → ℝ | M ≤ |linPotential η n y|}
        ≤ C0 * Real.exp (-(c0 * κ * min (M ^ 2 / (n : ℝ) ^ 2) (M / (n : ℝ)))) := by
    intro y _
    have hb := hpt n hn y M hM
    have hL2ratio : M ^ 2 / (Cg1 * n) ^ 2 ≤ M ^ 2 / (l2Norm (fun z => green d n (y - z))) ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg M) (pow_pos (hL2pos y) 2)
        (pow_le_pow_left₀ (hL2pos y).le (hL2b y) 2)
    have hSupratio : M / (Cg2 * n) ≤ M / supAbs (fun z => green d n (y - z)) :=
      div_le_div_of_nonneg_left hM.le (hSuppos y) (hSupb y)
    have hminratio : min (M ^ 2 / (Cg1 * n) ^ 2) (M / (Cg2 * n))
        ≤ min (M ^ 2 / (l2Norm (fun z => green d n (y - z))) ^ 2)
            (M / supAbs (fun z => green d n (y - z))) :=
      min_le_min hL2ratio hSupratio
    have hchain : κ * min (M ^ 2 / (n : ℝ) ^ 2) (M / (n : ℝ))
        ≤ min (M ^ 2 / (l2Norm (fun z => green d n (y - z))) ^ 2)
            (M / supAbs (fun z => green d n (y - z))) :=
      hminkey.trans hminratio
    have hmulle : c0 * (κ * min (M ^ 2 / (n : ℝ) ^ 2) (M / (n : ℝ)))
        ≤ c0 * min (M ^ 2 / (l2Norm (fun z => green d n (y - z))) ^ 2)
            (M / supAbs (fun z => green d n (y - z))) :=
      mul_le_mul_of_nonneg_left hchain hc0.le
    have hexple : Real.exp (-(c0 * min (M ^ 2 / (l2Norm (fun z => green d n (y - z))) ^ 2)
            (M / supAbs (fun z => green d n (y - z)))))
        ≤ Real.exp (-(c0 * κ * min (M ^ 2 / (n : ℝ) ^ 2) (M / (n : ℝ)))) := by
      rw [Real.exp_le_exp]
      have hre : c0 * κ * min (M ^ 2 / (n : ℝ) ^ 2) (M / (n : ℝ))
          = c0 * (κ * min (M ^ 2 / (n : ℝ) ^ 2) (M / (n : ℝ))) := by ring
      rw [hre]
      exact neg_le_neg hmulle
    have hCmulle : C0 * Real.exp (-(c0 * min (M ^ 2 / (l2Norm (fun z => green d n (y - z))) ^ 2)
            (M / supAbs (fun z => green d n (y - z)))))
        ≤ C0 * Real.exp (-(c0 * κ * min (M ^ 2 / (n : ℝ) ^ 2) (M / (n : ℝ)))) :=
      mul_le_mul_of_nonneg_left hexple hC0.le
    exact hb.trans hCmulle
  have hstep3 : ∑ y ∈ boxFinset (0 : Site d) A,
        (iidLaw d (realLaw ν)).real {η : Site d → ℝ | M ≤ |linPotential η n y|}
      ≤ ∑ _y ∈ boxFinset (0 : Site d) A,
          C0 * Real.exp (-(c0 * κ * min (M ^ 2 / (n : ℝ) ^ 2) (M / (n : ℝ)))) :=
    Finset.sum_le_sum hpoint
  have hcard : (boxFinset (0 : Site d) A).card = (2 * A + 1) ^ d := card_boxFinset 0 A
  rw [Finset.sum_const, hcard] at hstep3
  have hfinal : (iidLaw d (realLaw ν)).real
        {η : Site d → ℝ | ∃ y ∈ boxFinset (0 : Site d) A, M ≤ |linPotential η n y|}
      ≤ (2 * A + 1) ^ d • (C0 * Real.exp (-(c0 * κ * min (M ^ 2 / (n : ℝ) ^ 2) (M / (n : ℝ))))) :=
    hstep1.trans (hstep2.trans hstep3)
  rw [nsmul_eq_mul] at hfinal
  push_cast at hfinal
  rw [← measureReal_def]
  calc (iidLaw d (realLaw ν)).real
        {η : Site d → ℝ | ∃ y ∈ boxFinset (0 : Site d) A, M ≤ |linPotential η n y|}
      ≤ (2 * A + 1) ^ d * (C0 * Real.exp (-(c0 * κ * min (M ^ 2 / (n : ℝ) ^ 2) (M / (n : ℝ))))) :=
        hfinal
    _ = C0 * (2 * A + 1) ^ d * Real.exp (-(c0 * κ * min (M ^ 2 / (n : ℝ) ^ 2) (M / (n : ℝ)))) := by
        ring

end Parking

end
