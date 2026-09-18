/-
**The two-time (fixed space) comparison of the truncated Green function, general `d`.**

This is the TIME half of the translated-kernel-difference bound `parking.tex:1745-1747`
asks for, in the form that the `l2Norm`/`supAbs` of `Parking.Support.LinIncrementMoment`
need: a bound on

    l2Norm (fun z => green d n (x - z) - green d m (x - z))
    supAbs (fun z => green d n (x - z) - green d m (x - z))

for the SAME site `x` and two horizons `1 ≤ m ≤ n`, decaying as `n - m` stays small
relative to `m`.  Unlike the SPACE-only comparison (see the docstring of
`exists_green_time_shift_l2_bound`), this one is a short computation from tools already
proved in the shared library: `LatticeProb.tsum_sum_srwHeat_mul` (Chapman-Kolmogorov,
`LatticeProb/Walk/GreenSq.lean`) turns the l2Norm-squared into the double sum
`∑_{a,b ∈ Ico m n} srwHeat d (a+b) 0`, and the on-diagonal decay bounds
`LatticeProb.srwHeat_diag_le`/`srwHeat_sup_le` (`LatticeProb/Walk/VarianceScale.lean`,
already general in `d`) bound every term of that sum, since `a + b ≥ 2m` throughout.

No External is registered or consumed: this is a theorem of the repository.
-/
import Parking.Support.GreenBridge
import Parking.Support.Kernel
import LatticeProb.Walk.GreenSq
import LatticeProb.Walk.VarianceScale

noncomputable section

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-! ### Reindexing a `tsum` by `z ↦ x - z` -/

/-- Subtraction from a fixed `x` is an involution of `Site d`, hence a self-inverse
`Equiv`; reindexing a `tsum` along it changes nothing. -/
def subLeftEquiv (x : Site d) : Site d ≃ Site d where
  toFun z := x - z
  invFun z := x - z
  left_inv z := by simp
  right_inv z := by simp

theorem tsum_comp_subLeft (x : Site d) (f : Site d → ℝ) :
    ∑' z : Site d, f (x - z) = ∑' z : Site d, f z :=
  (subLeftEquiv x).tsum_eq f

/-! ### The truncated Green function as a sum of one interval of layers -/

/-- `g_n(w) - g_m(w) = ∑_{j = m}^{n-1} P^j(0,w)`, for `m ≤ n`. -/
theorem green_sub_eq_sum_Ico {m n : ℕ} (hmn : m ≤ n) (w : Site d) :
    green d n w - green d m w = ∑ j ∈ Finset.Ico m n, heat d j w := by
  have hcons : (∑ j ∈ Finset.Ico 0 m, heat d j w) + (∑ j ∈ Finset.Ico m n, heat d j w)
      = ∑ j ∈ Finset.Ico 0 n, heat d j w :=
    Finset.sum_Ico_consecutive (fun j => heat d j w) (Nat.zero_le m) hmn
  have h0m : (∑ j ∈ Finset.Ico 0 m, heat d j w) = green d m w := by
    rw [← Finset.range_eq_Ico]; rfl
  have h0n : (∑ j ∈ Finset.Ico 0 n, heat d j w) = green d n w := by
    rw [← Finset.range_eq_Ico]; rfl
  rw [h0m, h0n] at hcons
  linarith

/-! ### The Chapman-Kolmogorov identity for the squared time-difference -/

/-- `∑'_z (g_n(x-z) - g_m(x-z))^2 = ∑_{a,b ∈ Ico m n} P^{a+b}(0,0)`, for `m ≤ n`. -/
theorem tsum_green_sub_sq_eq {m n : ℕ} (hmn : m ≤ n) (x : Site d) :
    ∑' z : Site d, (green d n (x - z) - green d m (x - z)) ^ 2
      = ∑ a ∈ Finset.Ico m n, ∑ b ∈ Finset.Ico m n, LatticeProb.srwHeat d (a + b) 0 := by
  have hpt : ∀ z : Site d, (green d n (x - z) - green d m (x - z)) ^ 2
      = (∑ a ∈ Finset.Ico m n, LatticeProb.srwHeat d a (x - z))
          * (∑ b ∈ Finset.Ico m n, LatticeProb.srwHeat d b (x - z)) := by
    intro z
    have hsum : (∑ j ∈ Finset.Ico m n, heat d j (x - z))
        = ∑ j ∈ Finset.Ico m n, LatticeProb.srwHeat d j (x - z) :=
      Finset.sum_congr rfl fun j _ => heat_eq_srwHeat d j (x - z)
    rw [green_sub_eq_sum_Ico hmn (x - z), hsum, sq]
  rw [tsum_congr hpt,
    tsum_comp_subLeft x (fun y => (∑ a ∈ Finset.Ico m n, LatticeProb.srwHeat d a y)
      * (∑ b ∈ Finset.Ico m n, LatticeProb.srwHeat d b y))]
  exact LatticeProb.tsum_sum_srwHeat_mul (Finset.Ico m n) (Finset.Ico m n)

/-! ### The double sum is bounded by the on-diagonal decay at the earliest time -/

theorem sum_sum_srwHeat_le {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) (hd : 0 < d) :
    ∑ a ∈ Finset.Ico m n, ∑ b ∈ Finset.Ico m n, LatticeProb.srwHeat d (a + b) 0
      ≤ ((n : ℝ) - m) ^ 2 * (LatticeProb.diagConst d / Real.sqrt (2 * m) ^ d) := by
  have hcard : (Finset.Ico m n).card = n - m := Nat.card_Ico m n
  have hcardR : ((Finset.Ico m n).card : ℝ) = (n : ℝ) - m := by
    rw [hcard, Nat.cast_sub hmn]
  have hpow_pos : (0 : ℝ) < Real.sqrt (2 * (m : ℝ)) ^ d := by
    have : (0 : ℝ) < 2 * (m : ℝ) := by
      have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      linarith
    exact pow_pos (Real.sqrt_pos.mpr this) d
  have hterm : ∀ a ∈ Finset.Ico m n, ∀ b ∈ Finset.Ico m n,
      LatticeProb.srwHeat d (a + b) 0 ≤ LatticeProb.diagConst d / Real.sqrt (2 * m) ^ d := by
    intro a ha b hb
    rw [Finset.mem_Ico] at ha hb
    have hab1 : 1 ≤ a + b := by omega
    have hab2m : (2 : ℝ) * m ≤ (a : ℝ) + b := by
      have : 2 * m ≤ a + b := by omega
      exact_mod_cast this
    have hle : Real.sqrt (2 * (m : ℝ)) ^ d ≤ Real.sqrt ((a : ℝ) + b) ^ d := by
      have h1 : (2 * (m : ℝ)) ≤ (a : ℝ) + b := hab2m
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt h1) d
    have hcastab : ((a + b : ℕ) : ℝ) = (a : ℝ) + b := by push_cast; ring
    calc LatticeProb.srwHeat d (a + b) 0
        ≤ LatticeProb.diagConst d / Real.sqrt (a + b : ℕ) ^ d := srwHeat_diag_le hd hab1
      _ = LatticeProb.diagConst d / Real.sqrt ((a : ℝ) + b) ^ d := by rw [hcastab]
      _ ≤ LatticeProb.diagConst d / Real.sqrt (2 * m) ^ d :=
          div_le_div_of_nonneg_left (diagConst_pos d).le hpow_pos hle
  calc ∑ a ∈ Finset.Ico m n, ∑ b ∈ Finset.Ico m n, LatticeProb.srwHeat d (a + b) 0
      ≤ ∑ a ∈ Finset.Ico m n, ∑ b ∈ Finset.Ico m n,
          LatticeProb.diagConst d / Real.sqrt (2 * m) ^ d :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hterm a ha b hb
    _ = ((n : ℝ) - m) ^ 2 * (LatticeProb.diagConst d / Real.sqrt (2 * m) ^ d) := by
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hcardR]
        ring

/-- **The two-time comparison of the truncated Green function, fixed space, general
`d`.**  For `1 ≤ m ≤ n`, `l2Norm (fun z => green d n (x - z) - green d m (x - z)) ≤
(n - m) · sqrt (diagConst d / sqrt (2m) ^ d)`: every term of the double sum
`∑_{a,b ∈ Ico m n} P^{a+b}(0,0)` (`tsum_green_sub_sq_eq`) is bounded by the
on-diagonal decay `srwHeat_diag_le`, since `a + b ≥ 2m` throughout the range.  This is
the TIME half of the joint space-time translated-kernel-difference bound
`parking.tex:1745-1747` needs for the Kolmogorov chaining of the equicontinuity clause
of `prop:spatial-scaling`.  The SPACE half (fixed time, `x ≠ y`) is a different computation:
it needs chaining `Parking.External.GreenGradient` along a lattice path from `x` to `y` and a
shell-sum bound comparable to `Parking.Support.GammaSum`'s
`sum_gamma_le`/`gamma_le_of_gradient`, and, unlike this TIME computation, has no exact
Chapman-Kolmogorov shortcut (the analogous cross term
`∑_z g_n(x-z) g_n(y-z)` does reduce to `∑_{a,b<n} P^{a+b}(x-y)`, but bounding its
DEFICIT below `∑_z g_n(z)^2` needs the pointwise heat-kernel gradient at a single
offset `x-y`, not merely its `ℓ¹`-in-`y` form already in the library
(`LatticeProb.Walk.GenGrad`'s `exists_tsum_abs_srwHeat_two_point_le`), and in
dimensions one and two the naive per-term bound diverges without a scale-`n` cutoff,
exactly as the shell-sum machinery of `GammaSum.lean` is needed for `gamma`). -/
theorem exists_green_time_shift_l2_bound (hd : 0 < d) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (x : Site d) :
    l2Norm (fun z => green d n (x - z) - green d m (x - z))
      ≤ ((n : ℝ) - m) * Real.sqrt (LatticeProb.diagConst d / Real.sqrt (2 * m) ^ d) := by
  have hnm : (0 : ℝ) ≤ (n : ℝ) - m := by
    have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    linarith
  have hbound : ∑' z : Site d, (green d n (x - z) - green d m (x - z)) ^ 2
      ≤ ((n : ℝ) - m) ^ 2 * (LatticeProb.diagConst d / Real.sqrt (2 * m) ^ d) := by
    rw [tsum_green_sub_sq_eq hmn x]
    exact sum_sum_srwHeat_le hm hmn hd
  unfold l2Norm
  calc Real.sqrt (∑' z : Site d, (green d n (x - z) - green d m (x - z)) ^ 2)
      ≤ Real.sqrt (((n : ℝ) - m) ^ 2 * (LatticeProb.diagConst d / Real.sqrt (2 * m) ^ d)) :=
        Real.sqrt_le_sqrt hbound
    _ = ((n : ℝ) - m) * Real.sqrt (LatticeProb.diagConst d / Real.sqrt (2 * m) ^ d) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hnm]

/-- **The sup-norm form of the same time comparison.**  `heat d j w ≥ 0`
for every `j, w`, so `|g_n(x-z) - g_m(x-z)| = ∑_{j ∈ Ico m n} P^j(0, x - z)`, and each
summand is at most `diagConst d / √m ^ d` since `j ≥ m`. -/
theorem exists_green_time_shift_sup_bound (hd : 0 < d) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (x : Site d) :
    supAbs (fun z => green d n (x - z) - green d m (x - z))
      ≤ ((n : ℝ) - m) * (LatticeProb.diagConst d / Real.sqrt m ^ d) := by
  have hnm : (0 : ℝ) ≤ (n : ℝ) - m := by
    have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    linarith
  have hcard : (Finset.Ico m n).card = n - m := Nat.card_Ico m n
  have hcardR : ((Finset.Ico m n).card : ℝ) = (n : ℝ) - m := by
    rw [hcard, Nat.cast_sub hmn]
  have hpt : ∀ z : Site d, |green d n (x - z) - green d m (x - z)|
      ≤ ((n : ℝ) - m) * (LatticeProb.diagConst d / Real.sqrt m ^ d) := by
    intro z
    rw [green_sub_eq_sum_Ico hmn (x - z)]
    have hnonneg : 0 ≤ ∑ j ∈ Finset.Ico m n, heat d j (x - z) := by
      refine Finset.sum_nonneg fun j _ => ?_
      rw [heat_eq_srwHeat]
      exact LatticeProb.srwHeat_nonneg j (x - z)
    rw [abs_of_nonneg hnonneg]
    have hterm : ∀ j ∈ Finset.Ico m n,
        heat d j (x - z) ≤ LatticeProb.diagConst d / Real.sqrt m ^ d := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      rw [heat_eq_srwHeat]
      refine le_trans (srwHeat_sup_le hd (by omega) (x - z)) ?_
      have hjm : (m : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
      have hpowm : (0 : ℝ) < Real.sqrt (m : ℝ) ^ d :=
        pow_pos (Real.sqrt_pos.mpr (by exact_mod_cast hm)) d
      have hpow_le : Real.sqrt (m : ℝ) ^ d ≤ Real.sqrt (j : ℝ) ^ d :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hjm) d
      exact div_le_div_of_nonneg_left (diagConst_pos d).le hpowm hpow_le
    calc ∑ j ∈ Finset.Ico m n, heat d j (x - z)
        ≤ ∑ j ∈ Finset.Ico m n, LatticeProb.diagConst d / Real.sqrt m ^ d :=
          Finset.sum_le_sum hterm
      _ = ((n : ℝ) - m) * (LatticeProb.diagConst d / Real.sqrt m ^ d) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcardR]
  unfold supAbs
  exact ciSup_le hpt

end Parking

end
