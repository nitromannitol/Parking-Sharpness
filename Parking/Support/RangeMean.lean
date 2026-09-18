/-
The expected range of the walk from below, Step 1 of `prop:resolvent`.

`parking.tex:2660-2670` bounds `E_0|R_t|` from below by `(t+1)^2 / E_0 ∑_x L_t(x)^2`,
which the library's `div_le_integral_rangeCard` states in the equivalent form
`E_0|R_t| ≥ (t+1) / G_t(0,0)` for the truncated Green function
`G_t(0,0) = ∑_{j ≤ t} p_j(0,0)`.  The Green function grows like the paper's
scale: `√(t+1)` in dimension one, `log(t+2)` in dimension two, and boundedly
above.  That is what this file proves, from the on-diagonal heat kernel bound
`p_{2n}(0,0) ≤ C n^{-d/2}` and the parity of the walk.
-/
import Parking.Support.Near
import LatticeProb.Walk.SRWDiag
import LatticeProb.Walk.RangeSecond

noncomputable section

open MeasureTheory

namespace Parking

open Finset

variable {d : ℕ}

/-! ### Three elementary sums -/

theorem sum_inv_sqrt_le (t : ℕ) :
    ∑ k ∈ Finset.range (t + 1), (1 : ℝ) / Real.sqrt ((k : ℝ) + 1)
      ≤ 2 * Real.sqrt ((t : ℝ) + 1) := by
  induction t with
  | zero => norm_num
  | succ t ih =>
      rw [Finset.sum_range_succ]
      have h1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
      have h2 : (0 : ℝ) < (t : ℝ) + 1 + 1 := by positivity
      have hs1 : Real.sqrt ((t : ℝ) + 1) ^ 2 = (t : ℝ) + 1 := Real.sq_sqrt h1.le
      have hs2 : Real.sqrt ((t : ℝ) + 1 + 1) ^ 2 = (t : ℝ) + 1 + 1 := Real.sq_sqrt h2.le
      have hp1 : 0 < Real.sqrt ((t : ℝ) + 1) := Real.sqrt_pos.mpr h1
      have hp2 : 0 < Real.sqrt ((t : ℝ) + 1 + 1) := Real.sqrt_pos.mpr h2
      have hmono : Real.sqrt ((t : ℝ) + 1) ≤ Real.sqrt ((t : ℝ) + 1 + 1) :=
        Real.sqrt_le_sqrt (by linarith)
      have key : (1 : ℝ) / Real.sqrt ((t : ℝ) + 1 + 1)
          ≤ 2 * Real.sqrt ((t : ℝ) + 1 + 1) - 2 * Real.sqrt ((t : ℝ) + 1) := by
        rw [div_le_iff₀ hp2]
        nlinarith [hs1, hs2, hp1, hp2, hmono]
      push_cast
      linarith [ih, key]

theorem sum_inv_le_log (t : ℕ) :
    ∑ k ∈ Finset.range (t + 1), (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 + Real.log ((t : ℝ) + 1) := by
  induction t with
  | zero => norm_num
  | succ t ih =>
      rw [Finset.sum_range_succ]
      have h1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
      have h2 : (0 : ℝ) < (t : ℝ) + 1 + 1 := by positivity
      have hlog : Real.log (((t : ℝ) + 1) / ((t : ℝ) + 1 + 1))
          ≤ ((t : ℝ) + 1) / ((t : ℝ) + 1 + 1) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have hsplit : Real.log (((t : ℝ) + 1) / ((t : ℝ) + 1 + 1))
          = Real.log ((t : ℝ) + 1) - Real.log ((t : ℝ) + 1 + 1) :=
        Real.log_div (by positivity) (by positivity)
      have hval : ((t : ℝ) + 1) / ((t : ℝ) + 1 + 1) - 1 = -(1 / ((t : ℝ) + 1 + 1)) := by
        field_simp
        ring
      have hstep : (1 : ℝ) / ((t : ℝ) + 1 + 1)
          ≤ Real.log ((t : ℝ) + 1 + 1) - Real.log ((t : ℝ) + 1) := by
        rw [hsplit, hval] at hlog
        linarith
      push_cast
      linarith [ih, hstep]

theorem exists_sum_rpow_le {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ,
      ∑ k ∈ Finset.range (t + 1), ((k : ℝ) + 1) ^ (-p) ≤ C := by
  have h0 : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ p :=
    Real.summable_one_div_nat_rpow.mpr hp
  have h1 : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ p := by
    have := (summable_nat_add_iff 1).2 h0
    simpa [Nat.cast_add, Nat.cast_one] using this
  have hsum : Summable fun k : ℕ => ((k : ℝ) + 1) ^ (-p) := by
    refine h1.congr fun k => ?_
    rw [Real.rpow_neg (by positivity), one_div]
  have hnn : ∀ k : ℕ, (0 : ℝ) ≤ ((k : ℝ) + 1) ^ (-p) :=
    fun k => Real.rpow_nonneg (by positivity) _
  refine ⟨(∑' k : ℕ, ((k : ℝ) + 1) ^ (-p)) + 1, by positivity, fun t => ?_⟩
  have hle := hsum.sum_le_tsum (Finset.range (t + 1)) fun k _ => hnn k
  linarith

/-! ### The Green function on the diagonal -/

theorem srwHeat_odd_zero (n : ℕ) : LatticeProb.srwHeat d (2 * n + 1) 0 = 0 := by
  refine LatticeProb.srwHeat_eq_zero_of_parity ?_
  have h1 : ((2 * n + 1 : ℕ) : ZMod 2) = 1 := by
    have hcast : ((2 * n + 1 : ℕ) : ZMod 2) = 2 * (n : ZMod 2) + 1 := by push_cast; ring
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [hcast, h2, zero_mul, zero_add]
  rw [LatticeProb.graphNorm_zero, h1, Nat.cast_zero]
  decide

theorem srwGreen_even_eq (t : ℕ) :
    LatticeProb.srwGreen d (2 * t + 2) 0
      = ∑ n ∈ Finset.range (t + 1), LatticeProb.srwHeat d (2 * n) 0 := by
  induction t with
  | zero =>
      have h := srwHeat_odd_zero (d := d) 0
      norm_num at h
      simp [LatticeProb.srwGreen, Finset.sum_range_succ, h]
  | succ t ih =>
      have hrw : 2 * (t + 1) + 2 = (2 * t + 2) + 1 + 1 := by ring
      have hg1 : LatticeProb.srwGreen d ((2 * t + 2) + 1 + 1) 0
          = LatticeProb.srwGreen d (2 * t + 2) 0 + LatticeProb.srwHeat d (2 * t + 2) 0
            + LatticeProb.srwHeat d (2 * t + 2 + 1) 0 := by
        simp [LatticeProb.srwGreen, Finset.sum_range_succ]
      have hodd : LatticeProb.srwHeat d (2 * t + 2 + 1) 0 = 0 := by
        have h := srwHeat_odd_zero (d := d) (t + 1)
        have he : 2 * (t + 1) + 1 = 2 * t + 2 + 1 := by ring
        rwa [he] at h
      have heven : 2 * t + 2 = 2 * (t + 1) := by ring
      rw [hrw, hg1, hodd, ih, add_zero, heven, Finset.sum_range_succ (n := t + 1)]


/-! ### The Green function on the diagonal grows like the paper's scale -/

/-- The growth of the truncated Green function on the diagonal: `√(t+1)` in
dimension one, `log(t+2)` in dimension two, and bounded above. -/
def greenScale (d : ℕ) (t : ℕ) : ℝ :=
  if d = 1 then Real.sqrt ((t : ℝ) + 1) else if d = 2 then Real.log ((t : ℝ) + 2) else 1

theorem rpow_three_halves_eq (k : ℕ) :
    ((k : ℝ) + 1) ^ (-(3 : ℝ) / 2) = 1 / Real.sqrt ((k : ℝ) + 1) ^ 3 := by
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (((k : ℝ) + 1) ^ ((1 : ℝ) / 2)) 3,
    ← Real.rpow_mul hpos.le, one_div, ← Real.rpow_neg hpos.le]
  norm_num

theorem srwGreen_le_head_tail (hd : 1 ≤ d) (t : ℕ) :
    LatticeProb.srwGreen d (t + 1) 0
      ≤ 1 + ∑ n ∈ Finset.range t,
          (3 ^ d * LatticeProb.greenConst d + 1) / Real.sqrt ((n : ℝ) + 1) ^ d := by
  have hd0 : 0 < d := hd
  have hsubset : Finset.range (t + 1) ⊆ Finset.range (2 * t + 2) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hsub : LatticeProb.srwGreen d (t + 1) 0 ≤ LatticeProb.srwGreen d (2 * t + 2) 0 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset fun j _ _ => LatticeProb.srwHeat_nonneg j 0
  rw [srwGreen_even_eq] at hsub
  refine hsub.trans ?_
  rw [Finset.sum_range_succ']
  have hzero : LatticeProb.srwHeat d (2 * 0) 0 = 1 := by simp
  rw [hzero]
  have hterm : ∀ n ∈ Finset.range t, LatticeProb.srwHeat d (2 * (n + 1)) 0
      ≤ (3 ^ d * LatticeProb.greenConst d + 1) / Real.sqrt ((n : ℝ) + 1) ^ d := by
    intro n _
    have h := LatticeProb.srwHeat_diag_upper hd0 (n + 1) (by omega)
    have hc : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rwa [hc] at h
  linarith [Finset.sum_le_sum hterm]

theorem greenConst_pos (d : ℕ) : 0 < 3 ^ d * LatticeProb.greenConst d + 1 := by
  have h := LatticeProb.greenConst_nonneg d
  have h3 : (0 : ℝ) ≤ 3 ^ d := by positivity
  nlinarith

/-- **The truncated Green function on the diagonal is of the order of the
paper's scale.**  This is the denominator of the lower bound on `E_0|R_t|` at
`parking.tex:2660-2670`. -/
theorem exists_srwGreen_diag_le (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, LatticeProb.srwGreen d (t + 1) 0 ≤ C * greenScale d t := by
  obtain ⟨C₀, hC₀, hhead⟩ : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ t : ℕ,
      LatticeProb.srwGreen d (t + 1) 0
        ≤ 1 + ∑ n ∈ Finset.range t, C₀ / Real.sqrt ((n : ℝ) + 1) ^ d :=
    ⟨_, greenConst_pos d, srwGreen_le_head_tail hd⟩
  have hsubrange : ∀ t : ℕ, Finset.range t ⊆ Finset.range (t + 1) := by
    intro t x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hsqrt_one : ∀ n : ℕ, (1 : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) := by
    intro n
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_le_sqrt h1
  by_cases h1 : d = 1
  · subst h1
    refine ⟨1 + 2 * C₀, by positivity, fun t => ?_⟩
    have hg : greenScale 1 t = Real.sqrt ((t : ℝ) + 1) := by simp [greenScale]
    have hle : ∑ n ∈ Finset.range t, (1 : ℝ) / Real.sqrt ((n : ℝ) + 1)
        ≤ ∑ n ∈ Finset.range (t + 1), (1 : ℝ) / Real.sqrt ((n : ℝ) + 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg (hsubrange t) fun n _ _ => by positivity
    have hrw : ∑ n ∈ Finset.range t, C₀ / Real.sqrt ((n : ℝ) + 1) ^ 1
        = C₀ * ∑ n ∈ Finset.range t, (1 : ℝ) / Real.sqrt ((n : ℝ) + 1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by rw [pow_one]; ring
    have hsum : ∑ n ∈ Finset.range t, C₀ / Real.sqrt ((n : ℝ) + 1) ^ 1
        ≤ C₀ * (2 * Real.sqrt ((t : ℝ) + 1)) := by
      rw [hrw]
      exact mul_le_mul_of_nonneg_left (hle.trans (sum_inv_sqrt_le t)) hC₀.le
    rw [hg]
    nlinarith [hhead t, hsum, hsqrt_one t]
  · by_cases h2 : d = 2
    · subst h2
      have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      refine ⟨(1 + C₀) / Real.log 2 + C₀, by positivity, fun t => ?_⟩
      have hg : greenScale 2 t = Real.log ((t : ℝ) + 2) := by norm_num [greenScale]
      have hterm : ∀ n ∈ Finset.range t, C₀ / Real.sqrt ((n : ℝ) + 1) ^ 2
          = C₀ * ((1 : ℝ) / ((n : ℝ) + 1)) := by
        intro n _
        rw [Real.sq_sqrt (by positivity)]
        ring
      have hle : ∑ n ∈ Finset.range t, (1 : ℝ) / ((n : ℝ) + 1)
          ≤ ∑ n ∈ Finset.range (t + 1), (1 : ℝ) / ((n : ℝ) + 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg (hsubrange t) fun n _ _ => by positivity
      have hsum : ∑ n ∈ Finset.range t, C₀ / Real.sqrt ((n : ℝ) + 1) ^ 2
          ≤ C₀ * (1 + Real.log ((t : ℝ) + 1)) := by
        rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hle.trans (sum_inv_le_log t)) hC₀.le
      have hmono : Real.log ((t : ℝ) + 1) ≤ Real.log ((t : ℝ) + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      have hlow : Real.log 2 ≤ Real.log ((t : ℝ) + 2) := by
        refine Real.log_le_log (by norm_num) ?_
        have : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
        linarith
      have hh := hhead t
      rw [hg]
      have hkey : (1 + C₀) ≤ ((1 + C₀) / Real.log 2) * Real.log ((t : ℝ) + 2) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
        nlinarith
      nlinarith
    · have hd3 : 3 ≤ d := by omega
      obtain ⟨C₁, hC₁, hC₁le⟩ := exists_sum_rpow_le (p := (3 : ℝ) / 2) (by norm_num)
      refine ⟨1 + C₀ * C₁, by positivity, fun t => ?_⟩
      have hg : greenScale d t = 1 := by simp only [greenScale, if_neg h1, if_neg h2]
      have hterm : ∀ n ∈ Finset.range t, C₀ / Real.sqrt ((n : ℝ) + 1) ^ d
          ≤ C₀ * ((n : ℝ) + 1) ^ (-(3 : ℝ) / 2) := by
        intro n _
        have hcube : Real.sqrt ((n : ℝ) + 1) ^ 3 ≤ Real.sqrt ((n : ℝ) + 1) ^ d :=
          pow_le_pow_right₀ (hsqrt_one n) hd3
        have hpos3 : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) ^ 3 :=
          pow_pos (lt_of_lt_of_le zero_lt_one (hsqrt_one n)) 3
        rw [rpow_three_halves_eq n, mul_one_div]
        exact div_le_div_of_nonneg_left hC₀.le hpos3 hcube
      have hle : ∑ n ∈ Finset.range t, ((n : ℝ) + 1) ^ (-(3 : ℝ) / 2)
          ≤ ∑ n ∈ Finset.range (t + 1), ((n : ℝ) + 1) ^ (-(3 : ℝ) / 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg (hsubrange t)
          fun n _ _ => Real.rpow_nonneg (by positivity) _
      have hC1t : ∑ n ∈ Finset.range (t + 1), ((n : ℝ) + 1) ^ (-(3 : ℝ) / 2) ≤ C₁ := by
        have := hC₁le t
        simpa [neg_div] using this
      have hsum : ∑ n ∈ Finset.range t, C₀ / Real.sqrt ((n : ℝ) + 1) ^ d ≤ C₀ * C₁ := by
        refine (Finset.sum_le_sum hterm).trans ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hle.trans hC1t) hC₀.le
      rw [hg]
      linarith [hhead t, hsum]


theorem greenScale_pos (d : ℕ) (t : ℕ) : 0 < greenScale d t := by
  unfold greenScale
  split_ifs with h1 h2
  · have : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    exact Real.sqrt_pos.mpr this
  · refine Real.log_pos ?_
    have : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    linarith
  · exact zero_lt_one

/-- **The expected range from below**, in the paper's scale:
`E_x|R_t| ≥ c (t+1)/φ_d(t)` with `φ_1(t) = √(t+1)`, `φ_2(t) = log(t+2)` and
`φ_d(t) = 1` for `d ≥ 3`.  This is the first display of Step 1 of the proof of
`prop:resolvent` at `parking.tex:2660-2670`. -/
theorem exists_meanRange_lower (hd : 1 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (x : Site d) (t : ℕ),
      c * (((t : ℝ) + 1) / greenScale d t)
        ≤ ∫ X, (LatticeProb.rangeCard X t : ℝ) ∂(LatticeProb.siteWalkLaw d x) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hCle⟩ := exists_srwGreen_diag_le hd
  refine ⟨C⁻¹, by positivity, fun x t => ?_⟩
  have hgpos : 0 < greenScale d t := greenScale_pos d t
  have hGpos : (0 : ℝ) < LatticeProb.srwGreen d (t + 1) 0 :=
    lt_of_lt_of_le zero_lt_one (LatticeProb.one_le_srwGreen_origin t)
  have hstep : C⁻¹ * (((t : ℝ) + 1) / greenScale d t)
      ≤ ((t : ℝ) + 1) / LatticeProb.srwGreen d (t + 1) 0 := by
    have hrw : C⁻¹ * (((t : ℝ) + 1) / greenScale d t)
        = ((t : ℝ) + 1) / (C * greenScale d t) := by
      field_simp
    rw [hrw]
    refine div_le_div_of_nonneg_left ?_ hGpos (hCle t)
    have : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    linarith
  exact hstep.trans (LatticeProb.div_le_integral_rangeCard hd x t)

end Parking

end
