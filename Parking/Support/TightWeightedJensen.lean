/-
The weighted-Jensen geometric-tail lemma: a bound on the `p`-th power of a finite sum of
nonnegative reals, in terms of the SAME power of its individual terms weighted by a geometric
factor that grows with the index.  This is the tool that sums the per-level moment bounds of
`Parking/Support/TightBoxSupMoment.lean`'s `levelInc` into a geometric-tail bound of the
box-clamped reward field's supremum, WITHOUT Minkowski's inequality or any `ENNReal`/`eLpNorm`
bookkeeping.

The proof: for weights `w_k := (1 - r) * r ^ k / (1 - r ^ (N + 1))` on `Finset.range (N + 1)`
(which sum to `1` by the finite geometric series identity), `Real.rpow_arith_mean_le_arith_mean_
rpow` applied to `z_k := x_k / w_k` gives `(∑ x_k) ^ p ≤ ∑ w_k ^ (1 - p) * x_k ^ p`.  Since
`w_k ≥ (1 - r) * r ^ k` (dividing a positive quantity by `1 - r ^ (N + 1) ∈ (0, 1]` only
increases it) and `1 - p ≤ 0`, `Real.rpow_le_rpow_of_nonpos` reverses this to `w_k ^ (1 - p) ≤
((1 - r) * r ^ k) ^ (1 - p) = (1 - r) ^ (1 - p) * r ^ (k * (1 - p))`, giving the stated bound.
The bound is UNIFORM IN `N`: no summability of `x` is assumed or needed, and the right side's
own summability (as `N → ∞`) is controlled entirely by the choice of `r` against the decay rate
of `x_k ^ p` itself, at the point of use.
-/
import Mathlib

noncomputable section

namespace Parking

open Finset

/-- **The weighted-Jensen geometric bound.**  For any nonnegative sequence `x`, any `p ≥ 1`,
and any geometric ratio `r ∈ (0, 1)`, the `p`-th power of the sum of the first `N + 1` terms of
`x` is bounded by a GEOMETRICALLY WEIGHTED sum of the `p`-th powers of the individual terms,
uniformly in `N`. -/
theorem rpow_sum_range_le_geometric_weighted_sum (N : ℕ) (x : ℕ → ℝ) (hx : ∀ k, 0 ≤ x k)
    (p : ℝ) (hp : 1 ≤ p) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (∑ k ∈ Finset.range (N + 1), x k) ^ p ≤
      (1 - r) ^ (1 - p) * ∑ k ∈ Finset.range (N + 1), r ^ ((k : ℝ) * (1 - p)) * (x k) ^ p := by
  have hr1' : r ≠ 1 := hr1.ne
  have hrpow_lt : r ^ (N + 1) < 1 := pow_lt_one₀ hr0.le hr1 (Nat.succ_ne_zero N)
  have hrpow_nonneg : (0 : ℝ) ≤ r ^ (N + 1) := by positivity
  have hden_pos : (0 : ℝ) < 1 - r ^ (N + 1) := by linarith
  set D : ℝ := 1 - r ^ (N + 1) with hDdef
  set w : ℕ → ℝ := fun k => (1 - r) * r ^ k / D with hwdef
  have h1r_pos : (0 : ℝ) < 1 - r := by linarith
  have hw_pos : ∀ k, 0 < w k := by
    intro k
    rw [hwdef]
    positivity
  have h1rp1_pos : (0 : ℝ) < 1 - r ^ (N + 1) := by linarith
  have hw_sum : ∑ k ∈ Finset.range (N + 1), w k = 1 := by
    have hgeom : ∑ k ∈ Finset.range (N + 1), r ^ k = (1 - r ^ (N + 1)) / (1 - r) := by
      rw [geom_sum_eq hr1']
      rw [div_eq_div_iff (sub_ne_zero.mpr hr1') h1r_pos.ne']
      ring
    calc ∑ k ∈ Finset.range (N + 1), w k
        = ∑ k ∈ Finset.range (N + 1), (1 - r) / D * r ^ k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hwdef]; ring
      _ = (1 - r) / D * ∑ k ∈ Finset.range (N + 1), r ^ k := by rw [Finset.mul_sum]
      _ = (1 - r) / D * ((1 - r ^ (N + 1)) / (1 - r)) := by rw [hgeom]
      _ = 1 := by
          rw [hDdef]
          field_simp [h1r_pos.ne', h1rp1_pos.ne']
  set z : ℕ → ℝ := fun k => x k / w k with hzdef
  have hz_nonneg : ∀ k ∈ Finset.range (N + 1), 0 ≤ z k := by
    intro k _
    exact div_nonneg (hx k) (hw_pos k).le
  have hw_nonneg : ∀ k ∈ Finset.range (N + 1), 0 ≤ w k := fun k _ => (hw_pos k).le
  have hmain := Real.rpow_arith_mean_le_arith_mean_rpow (Finset.range (N + 1)) w z
    hw_nonneg hw_sum hz_nonneg hp
  have hwz : ∀ k ∈ Finset.range (N + 1), w k * z k = x k := by
    intro k _
    rw [hzdef]
    exact mul_div_cancel₀ (x k) (hw_pos k).ne'
  have hsum_eq : ∑ k ∈ Finset.range (N + 1), w k * z k = ∑ k ∈ Finset.range (N + 1), x k :=
    Finset.sum_congr rfl hwz
  rw [hsum_eq] at hmain
  have hstep : ∀ k ∈ Finset.range (N + 1), w k * z k ^ p = (w k) ^ (1 - p) * (x k) ^ p := by
    intro k _
    rw [hzdef, Real.div_rpow (hx k) (hw_pos k).le]
    rw [show (w k) ^ (1 - p) = (w k) / (w k) ^ p by
      rw [Real.rpow_sub (hw_pos k), Real.rpow_one]]
    field_simp
  rw [Finset.sum_congr rfl hstep] at hmain
  refine hmain.trans ?_
  have hbound : ∀ k ∈ Finset.range (N + 1),
      (w k) ^ (1 - p) * (x k) ^ p ≤
        (1 - r) ^ (1 - p) * r ^ ((k : ℝ) * (1 - p)) * (x k) ^ p := by
    intro k _
    have hle : (1 - r) * r ^ k ≤ w k := by
      rw [hwdef]
      rw [le_div_iff₀ hden_pos]
      have hDle1 : D ≤ 1 := by rw [hDdef]; linarith
      have hpos : (0 : ℝ) ≤ (1 - r) * r ^ k := by positivity
      nlinarith [hpos, hDle1]
    have hpos1 : (0 : ℝ) < (1 - r) * r ^ k := by positivity
    have hp1 : 1 - p ≤ 0 := by linarith
    have hrw : (w k) ^ (1 - p) ≤ ((1 - r) * r ^ k) ^ (1 - p) :=
      Real.rpow_le_rpow_of_nonpos hpos1 hle hp1
    have hexpand : ((1 - r) * r ^ k) ^ (1 - p) =
        (1 - r) ^ (1 - p) * r ^ ((k : ℝ) * (1 - p)) := by
      rw [Real.mul_rpow h1r_pos.le (by positivity : (0:ℝ) ≤ r ^ k)]
      congr 1
      rw [← Real.rpow_natCast r k, ← Real.rpow_mul hr0.le]
    rw [hexpand] at hrw
    exact mul_le_mul_of_nonneg_right hrw (Real.rpow_nonneg (hx k) p)
  calc ∑ k ∈ Finset.range (N + 1), (w k) ^ (1 - p) * (x k) ^ p
      ≤ ∑ k ∈ Finset.range (N + 1), (1 - r) ^ (1 - p) * r ^ ((k : ℝ) * (1 - p)) * (x k) ^ p :=
        Finset.sum_le_sum hbound
    _ = (1 - r) ^ (1 - p) * ∑ k ∈ Finset.range (N + 1), r ^ ((k : ℝ) * (1 - p)) * (x k) ^ p := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring

end Parking

end
