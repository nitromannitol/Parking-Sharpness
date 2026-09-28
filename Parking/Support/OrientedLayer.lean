import Parking.Support.OrientedKernel

/-!
# Probability mass and disjoint support of the oriented layers

Probability mass, disjoint support and square sums of the oriented layers.
-/

noncomputable section
namespace Parking
open LatticeProb Finset
variable {d : ℕ}

/-- The signed layer coordinate of a lattice site. -/
def layerHeight (x : Site d) : ℤ := ∑ i, x i

/-- `layerHeight` is additive: the layer height of `x + y` is the sum of the layer
heights of `x` and `y`, since it is itself a coordinate sum. -/
theorem layerHeight_add (x y : Site d) : layerHeight (x + y) = layerHeight x + layerHeight y := by
  simp [layerHeight, sum_add_distrib]

/-- Every standard basis site `unit i` has layer height `1`. -/
theorem layerHeight_unit (i : Fin d) : layerHeight (unit i) = 1 := by
  simp [layerHeight, unit]

/-- `orientedLayer d n x` is nonnegative for every `n` and `x`, by induction on `n` using
that `orientedLayer d (n + 1)` is an average of nonnegative earlier values
(`orientedLayer_succ`). -/
theorem orientedLayer_nonneg (n : ℕ) (x : Site d) : 0 ≤ orientedLayer d n x := by
  induction n generalizing x with
  | zero => simp only [orientedLayer]; split_ifs <;> norm_num
  | succ n ih =>
    rw [orientedLayer_succ]
    exact div_nonneg (sum_nonneg fun i _ => ih _) (Nat.cast_nonneg _)

/-- If `orientedLayer d (n + 1) x` is nonzero then some successor `x + unit i` already
carries nonzero mass at layer `n`, since the recursion `orientedLayer_succ` expresses the
former as an average of the latter over `i`. -/
theorem orientedLayer_predecessor {n : ℕ} {x : Site d}
    (h : orientedLayer d (n + 1) x ≠ 0) :
    ∃ i : Fin d, orientedLayer d n (x + unit i) ≠ 0 := by
  rw [orientedLayer_succ] at h
  have hs : (∑ i : Fin d, orientedLayer d n (x + unit i)) ≠ 0 := by
    intro hs
    exact h (by rw [hs, zero_div])
  obtain ⟨i, _, hi⟩ := exists_ne_zero_of_sum_ne_zero hs
  exact ⟨i, hi⟩

/-- Every site of nonzero `orientedLayer d n` mass has layer height exactly `-n`, by
induction on `n` using `orientedLayer_predecessor` to walk back to a successor at layer
`n - 1` and `layerHeight_add`/`layerHeight_unit` to track the height. -/
theorem orientedLayer_height {n : ℕ} {x : Site d} (h : orientedLayer d n x ≠ 0) :
    layerHeight x = -(n : ℤ) := by
  induction n generalizing x with
  | zero =>
    have hx : x = 0 := by by_contra hx; exact h (if_neg hx)
    simp [hx, layerHeight]
  | succ n ih =>
    obtain ⟨i, hi⟩ := orientedLayer_predecessor h
    have he := ih hi
    rw [layerHeight_add, layerHeight_unit] at he
    push_cast
    omega

/-- Every site of nonzero `orientedLayer d n` mass lies in the box `boxFinset 0 n`, by
induction on `n` using `orientedLayer_predecessor` and the fact that each step from a
successor changes each coordinate by at most `1`. -/
theorem orientedLayer_mem_box {n : ℕ} {x : Site d} (h : orientedLayer d n x ≠ 0) :
    x ∈ boxFinset 0 n := by
  induction n generalizing x with
  | zero =>
    have hx : x = 0 := by by_contra hx; exact h (if_neg hx)
    simp [hx, mem_boxFinset_iff]
  | succ n ih =>
    obtain ⟨i, hi⟩ := orientedLayer_predecessor h
    have hm := mem_boxFinset_one_of_nbr (mem_nbrFinset_sub (x + unit i) i)
    simp only [add_sub_cancel_right] at hm
    exact mem_boxFinset_add (ih hi) hm

/-- The contrapositive of `orientedLayer_mem_box`: outside the box `boxFinset 0 n`, the
`n`-th layer vanishes. -/
theorem orientedLayer_eq_zero_of_notMem {n : ℕ} {x : Site d}
    (h : x ∉ boxFinset 0 n) : orientedLayer d n x = 0 :=
  not_not.mp (fun hn => h (orientedLayer_mem_box hn))

/-- For any `f`, the weighted layer function `x ↦ f x * orientedLayer d n x` is summable,
since it vanishes outside the finite set `boxFinset 0 n` by
`orientedLayer_eq_zero_of_notMem`. -/
theorem summable_orientedLayer_weight (n : ℕ) (f : Site d → ℝ) :
    Summable fun x => f x * orientedLayer d n x := by
  refine summable_of_ne_finset_zero (s := boxFinset 0 n) fun x hx => ?_
  rw [orientedLayer_eq_zero_of_notMem hx, mul_zero]

/-- `orientedLayer d n` is summable, the case `f = 1` of `summable_orientedLayer_weight`. -/
theorem summable_orientedLayer (n : ℕ) : Summable (orientedLayer d n) := by
  simpa using summable_orientedLayer_weight n (fun _ : Site d => 1)

/-- The squared layer function `x ↦ orientedLayer d n x ^ 2` is summable, the case
`f = orientedLayer d n` of `summable_orientedLayer_weight`. -/
theorem summable_orientedLayer_sq (n : ℕ) : Summable fun x : Site d => orientedLayer d n x ^ 2 := by
  simpa only [pow_two] using summable_orientedLayer_weight n (orientedLayer d n)

/-- Each layer `orientedLayer d n` has total mass `1`, by induction on `n` using the
recursion `orientedLayer_succ`, which averages `d` terms each already summing to `1`
by the inductive hypothesis and reindexing by `Equiv.addRight`. -/
theorem tsum_orientedLayer (hd : 1 ≤ d) (n : ℕ) : ∑' x, orientedLayer d n x = 1 := by
  induction n with
  | zero => simp [orientedLayer]
  | succ n ih =>
    have hs : ∀ i : Fin d, Summable fun x => orientedLayer d n (x + unit i) := by
      intro i
      exact (Equiv.addRight (unit i)).summable_iff.mpr (summable_orientedLayer n)
    rw [tsum_congr (orientedLayer_succ n), tsum_div_const, Summable.tsum_finsetSum
      (fun i _ => hs i)]
    have he : ∀ i : Fin d, (∑' x, orientedLayer d n (x + unit i)) = 1 := by
      intro i
      exact ((Equiv.addRight (unit i)).tsum_eq (orientedLayer d n)).trans ih
    simp only [he, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact div_self (ne_of_gt (show (0 : ℝ) < d by exact_mod_cast hd))

/-- Each value `orientedLayer d n x` is at most `1`, since the nonnegative layer sums to
`1` by `tsum_orientedLayer` and one nonnegative term of a sum with total `1` cannot
exceed it. -/
theorem orientedLayer_le_one (hd : 1 ≤ d) (n : ℕ) (x : Site d) : orientedLayer d n x ≤ 1 := by
  rw [← tsum_orientedLayer hd n]
  exact (summable_orientedLayer n).le_tsum x (fun y _ => orientedLayer_nonneg n y)

/-- Distinct layers `orientedLayer d n` and `orientedLayer d m` never overlap at the same
site: if both were nonzero at `x` then `orientedLayer_height` would force `n = m` from
`layerHeight x = -n = -m`. -/
theorem orientedLayer_mul_eq_zero {n m : ℕ} (hnm : n ≠ m) (x : Site d) :
    orientedLayer d n x * orientedLayer d m x = 0 := by
  by_cases hn : orientedLayer d n x = 0
  · simp [hn]
  · have hm : orientedLayer d m x = 0 := by
      by_contra hm
      have he := orientedLayer_height hn
      have he' := orientedLayer_height hm
      exact hnm (by omega)
    simp [hm]

/-- `orientedGreen d n x` is nonnegative, being a sum of nonnegative layer values. -/
theorem orientedGreen_nonneg (n : ℕ) (x : Site d) : 0 ≤ orientedGreen d n x :=
  sum_nonneg fun l _ => orientedLayer_nonneg l x

/-- Each value `orientedGreen d n x` is at most `1`: by `orientedLayer_mul_eq_zero`, at
most one layer `l < n` is nonzero at `x`, so the sum defining the Green function reduces
to that one term, which is at most `1` by `orientedLayer_le_one`. -/
theorem orientedGreen_le_one (hd : 1 ≤ d) (n : ℕ) (x : Site d) : orientedGreen d n x ≤ 1 := by
  classical
  by_cases h : ∃ l ∈ range n, orientedLayer d l x ≠ 0
  · obtain ⟨l, hl, hpos⟩ := h
    rw [orientedGreen, sum_eq_single l]
    · exact orientedLayer_le_one hd l x
    · intro m hm hml
      have he := orientedLayer_mul_eq_zero hml x
      exact (mul_eq_zero.mp he).resolve_right hpos
    · exact fun h => (h hl).elim
  · have he : ∀ l ∈ range n, orientedLayer d l x = 0 := by
      intro l hl
      by_contra hn
      exact h ⟨l, hl, hn⟩
    simp only [orientedGreen, sum_eq_zero he, zero_le_one]

/-- `orientedGreen d n x ^ 2` equals the sum of squared layer values `orientedLayer d l x
^ 2` over `l < n`, since distinct layers do not overlap at `x`
(`orientedLayer_mul_eq_zero`) and so the cross terms in `(∑ orientedLayer)² ` vanish. -/
theorem orientedGreen_sq (n : ℕ) (x : Site d) :
    orientedGreen d n x ^ 2 = ∑ l ∈ range n, orientedLayer d l x ^ 2 := by
  induction n with
  | zero => simp [orientedGreen]
  | succ n ih =>
    have hz : orientedGreen d n x * orientedLayer d n x = 0 := by
      unfold orientedGreen
      rw [sum_mul]
      apply sum_eq_zero
      intro l hl
      exact orientedLayer_mul_eq_zero (ne_of_lt (mem_range.mp hl)) x
    have hr : orientedGreen d (n + 1) x = orientedGreen d n x + orientedLayer d n x :=
      sum_range_succ _ n
    rw [hr, sum_range_succ, ← ih]
    nlinarith

/-- Summing `orientedGreen_sq` over all sites and exchanging the finite sum over `l < n`
with the `tsum` over `x` gives the total squared Green norm as a sum of the total
squared layer norms. -/
theorem tsum_orientedGreen_sq (n : ℕ) :
    (∑' x : Site d, orientedGreen d n x ^ 2) =
      ∑ l ∈ range n, ∑' x : Site d, orientedLayer d l x ^ 2 := by
  rw [tsum_congr (orientedGreen_sq n), Summable.tsum_finsetSum
    (fun l _ => summable_orientedLayer_sq l)]

end Parking
