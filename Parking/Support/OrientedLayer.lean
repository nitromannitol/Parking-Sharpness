/- Probability mass, disjoint support and square sums of the oriented layers. -/
import Parking.Support.OrientedKernel

noncomputable section
namespace Parking
open LatticeProb Finset
variable {d : ℕ}

/-- The signed layer coordinate of a lattice site. -/
def layerHeight (x : Site d) : ℤ := ∑ i, x i

theorem layerHeight_add (x y : Site d) : layerHeight (x + y) = layerHeight x + layerHeight y := by
  simp [layerHeight, sum_add_distrib]

theorem layerHeight_unit (i : Fin d) : layerHeight (unit i) = 1 := by
  simp [layerHeight, unit]

theorem orientedLayer_nonneg (n : ℕ) (x : Site d) : 0 ≤ orientedLayer d n x := by
  induction n generalizing x with
  | zero => simp only [orientedLayer]; split_ifs <;> norm_num
  | succ n ih =>
    rw [orientedLayer_succ]
    exact div_nonneg (sum_nonneg fun i _ => ih _) (Nat.cast_nonneg _)

theorem orientedLayer_predecessor {n : ℕ} {x : Site d}
    (h : orientedLayer d (n + 1) x ≠ 0) :
    ∃ i : Fin d, orientedLayer d n (x + unit i) ≠ 0 := by
  rw [orientedLayer_succ] at h
  have hs : (∑ i : Fin d, orientedLayer d n (x + unit i)) ≠ 0 := by
    intro hs
    exact h (by rw [hs, zero_div])
  obtain ⟨i, _, hi⟩ := exists_ne_zero_of_sum_ne_zero hs
  exact ⟨i, hi⟩

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

theorem orientedLayer_eq_zero_of_notMem {n : ℕ} {x : Site d}
    (h : x ∉ boxFinset 0 n) : orientedLayer d n x = 0 :=
  not_not.mp (fun hn => h (orientedLayer_mem_box hn))

theorem summable_orientedLayer_weight (n : ℕ) (f : Site d → ℝ) :
    Summable fun x => f x * orientedLayer d n x := by
  refine summable_of_ne_finset_zero (s := boxFinset 0 n) fun x hx => ?_
  rw [orientedLayer_eq_zero_of_notMem hx, mul_zero]

theorem summable_orientedLayer (n : ℕ) : Summable (orientedLayer d n) := by
  simpa using summable_orientedLayer_weight n (fun _ : Site d => 1)

theorem summable_orientedLayer_sq (n : ℕ) : Summable fun x : Site d => orientedLayer d n x ^ 2 := by
  simpa only [pow_two] using summable_orientedLayer_weight n (orientedLayer d n)

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

theorem orientedLayer_le_one (hd : 1 ≤ d) (n : ℕ) (x : Site d) : orientedLayer d n x ≤ 1 := by
  rw [← tsum_orientedLayer hd n]
  exact (summable_orientedLayer n).le_tsum x (fun y _ => orientedLayer_nonneg n y)

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

theorem orientedGreen_nonneg (n : ℕ) (x : Site d) : 0 ≤ orientedGreen d n x :=
  sum_nonneg fun l _ => orientedLayer_nonneg l x

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

theorem tsum_orientedGreen_sq (n : ℕ) :
    (∑' x : Site d, orientedGreen d n x ^ 2) =
      ∑ l ∈ range n, ∑' x : Site d, orientedLayer d l x ^ 2 := by
  rw [tsum_congr (orientedGreen_sq n), Summable.tsum_finsetSum
    (fun l _ => summable_orientedLayer_sq l)]

end Parking
