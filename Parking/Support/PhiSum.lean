/-
The dyadic block sum of Step 2 of `lem:mean-horizon` (`parking.tex:2802-2826`).

Step 2 splits the horizon into the blocks `[0, N)` and `[2^{k-1}N, 2^k N)` and
bounds the reward collected in the `k`-th block by `φ_d(2^{k-1}N)` times the
chance `2^{1-k}` that the stopping time reaches it; Hölder's inequality turns
the two into the series

    ∑_{j ≥ 0} 2^{-jθ} φ_d(2^j N) ,   θ = 1 - 1/q ,

which the paper says converges by the choice of `q`.  This file proves that it
converges and is at most `C φ_d(N)`, uniformly in `N ≥ 1`: the scale `φ_d`
grows by at most `2^{jα}` with `α = (4-d)/4` across `j` dyadic doublings when
`d ≤ 3`, and by at most the factor `j log 2 + 1` when `d ≥ 4`, so the series is
geometric in the first case and geometric with a linear weight in the second.
-/
import Parking.Support.RangeResolvent

open MeasureTheory

noncomputable section

namespace Parking

variable {d : ℕ}

theorem phi_two_pow_le_pow {d : ℕ} (hd3 : d ≤ 3) (k : ℕ) {N : ℝ} (hN : 1 ≤ N) :
    phi d (2 ^ k * N) ≤ 2 ^ ((k : ℝ) * (((4 : ℝ) - (d : ℝ)) / 4)) * phi d N := by
  simp only [phi, if_pos hd3]
  have hk : (1 : ℝ) ≤ (2:ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hNpos : (0 : ℝ) < N := by linarith
  have hstep : (2:ℝ) ^ k * N + 1 ≤ (2:ℝ) ^ k * (N + 1) := by nlinarith [hk]
  have hexp : (0 : ℝ) ≤ ((4 : ℝ) - (d : ℝ)) / 4 := by
    have hd : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
    linarith
  calc ((2:ℝ) ^ k * N + 1) ^ (((4 : ℝ) - (d : ℝ)) / 4)
      ≤ ((2:ℝ) ^ k * (N + 1)) ^ (((4 : ℝ) - (d : ℝ)) / 4) :=
        Real.rpow_le_rpow (by positivity) hstep hexp
    _ = ((2:ℝ) ^ k) ^ (((4 : ℝ) - (d : ℝ)) / 4) * (N + 1) ^ (((4 : ℝ) - (d : ℝ)) / 4) :=
        Real.mul_rpow (by positivity) (by positivity)
    _ = 2 ^ ((k : ℝ) * (((4 : ℝ) - (d : ℝ)) / 4)) * (N + 1) ^ (((4 : ℝ) - (d : ℝ)) / 4) := by
        rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]

theorem phi_two_pow_le_log {d : ℕ} (hd4 : 4 ≤ d) (k : ℕ) {N : ℝ} (hN : 1 ≤ N) :
    phi d (2 ^ k * N) ≤ ((k : ℝ) * Real.log 2 + 1) * phi d N := by
  have hd3 : ¬ (d ≤ 3) := by omega
  simp only [phi, if_neg hd3]
  have hk : (1 : ℝ) ≤ (2:ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hstep : (2:ℝ) ^ k * N + 2 ≤ (2:ℝ) ^ k * (N + 2) := by nlinarith [hk]
  have h1 : Real.log ((2:ℝ) ^ k * N + 2) ≤ Real.log ((2:ℝ) ^ k * (N + 2)) :=
    Real.log_le_log (by nlinarith [hk]) hstep
  have h2 : Real.log ((2:ℝ) ^ k * (N + 2)) = (k : ℝ) * Real.log 2 + Real.log (N + 2) := by
    rw [Real.log_mul (by positivity) (by linarith), Real.log_pow]
  have h3 : (1 : ℝ) ≤ Real.log (N + 2) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    nlinarith [Real.exp_one_lt_d9]
  have h4 : (0 : ℝ) ≤ (k : ℝ) * Real.log 2 := by
    have h5 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  nlinarith [h1, h2, h3, h4]


theorem phi_nonneg (d : ℕ) {N : ℝ} (hN : 1 ≤ N) : 0 ≤ phi d N := by
  unfold phi
  split_ifs with h
  · exact Real.rpow_nonneg (by linarith) _
  · exact Real.log_nonneg (by linarith)

theorem two_rpow_mul (x : ℝ) (j : ℕ) : (2:ℝ) ^ ((j : ℝ) * x) = ((2:ℝ) ^ x) ^ j := by
  rw [mul_comm, Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]

theorem exists_phi_block_sum (d : ℕ) {θ : ℝ} (hθ : 0 < θ)
    (hθd : d ≤ 3 → ((4:ℝ) - (d:ℝ)) / 4 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 ≤ N →
      Summable (fun j : ℕ => (2:ℝ) ^ (-(j : ℝ) * θ) * phi d (2 ^ j * N)) ∧
      ∑' j : ℕ, (2:ℝ) ^ (-(j : ℝ) * θ) * phi d (2 ^ j * N) ≤ C * phi d N := by
  by_cases hd3 : d ≤ 3
  · have hα : ((4:ℝ) - (d:ℝ)) / 4 < θ := hθd hd3
    set r : ℝ := (2:ℝ) ^ (((4:ℝ) - (d:ℝ)) / 4 - θ) with hrdef
    have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
    have hr1 : r < 1 := by
      rw [hrdef, show (1:ℝ) = (2:ℝ) ^ (0:ℝ) from (Real.rpow_zero 2).symm]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    refine ⟨(1 - r)⁻¹, inv_pos.mpr (by linarith), fun N hN => ?_⟩
    have hphi : 0 ≤ phi d N := phi_nonneg d hN
    have hmaj : ∀ j : ℕ, (2:ℝ) ^ (-(j : ℝ) * θ) * phi d (2 ^ j * N) ≤ r ^ j * phi d N := by
      intro j
      have h1 := phi_two_pow_le_pow hd3 j hN
      have h2 : (0:ℝ) < (2:ℝ) ^ (-(j : ℝ) * θ) := Real.rpow_pos_of_pos (by norm_num) _
      have hpow : (2:ℝ) ^ (-(j : ℝ) * θ) * (2:ℝ) ^ ((j : ℝ) * (((4:ℝ) - (d:ℝ)) / 4))
          = r ^ j := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2), hrdef, ← two_rpow_mul]
        congr 1
        ring
      have h3 : (2:ℝ) ^ (-(j : ℝ) * θ) * ((2:ℝ) ^ ((j : ℝ) * (((4:ℝ) - (d:ℝ)) / 4)) * phi d N)
          = r ^ j * phi d N := by
        rw [← mul_assoc, hpow]
      calc (2:ℝ) ^ (-(j : ℝ) * θ) * phi d (2 ^ j * N)
          ≤ (2:ℝ) ^ (-(j : ℝ) * θ)
              * ((2:ℝ) ^ ((j : ℝ) * (((4:ℝ) - (d:ℝ)) / 4)) * phi d N) :=
            mul_le_mul_of_nonneg_left h1 h2.le
        _ = r ^ j * phi d N := h3
    have hnn : ∀ j : ℕ, (0:ℝ) ≤ (2:ℝ) ^ (-(j : ℝ) * θ) * phi d (2 ^ j * N) := by
      intro j
      have h2 : (0:ℝ) < (2:ℝ) ^ (-(j : ℝ) * θ) := Real.rpow_pos_of_pos (by norm_num) _
      have h4 : (0:ℝ) ≤ phi d (2 ^ j * N) := by
        refine phi_nonneg d ?_
        have hk : (1:ℝ) ≤ (2:ℝ) ^ j := one_le_pow₀ (by norm_num)
        nlinarith
      positivity
    have hsumr : Summable (fun j : ℕ => r ^ j * phi d N) :=
      (summable_geometric_of_lt_one hr0.le hr1).mul_right _
    have hsummable := hsumr.of_nonneg_of_le hnn hmaj
    refine ⟨hsummable, ?_⟩
    calc ∑' j : ℕ, (2:ℝ) ^ (-(j : ℝ) * θ) * phi d (2 ^ j * N)
        ≤ ∑' j : ℕ, r ^ j * phi d N := hsummable.tsum_le_tsum hmaj hsumr
      _ = (∑' j : ℕ, r ^ j) * phi d N := tsum_mul_right
      _ = (1 - r)⁻¹ * phi d N := by rw [tsum_geometric_of_lt_one hr0.le hr1]
  · have hd4 : 4 ≤ d := by omega
    set r : ℝ := (2:ℝ) ^ (-θ) with hrdef
    have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
    have hr1 : r < 1 := by
      rw [hrdef, show (1:ℝ) = (2:ℝ) ^ (0:ℝ) from (Real.rpow_zero 2).symm]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    have hrnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hr0]
    have h1 : Summable (fun j : ℕ => ((j : ℝ) ^ 1) * r ^ j) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 hrnorm
    have h2 : Summable (fun j : ℕ => r ^ j) := summable_geometric_of_lt_one hr0.le hr1
    have hsumj : Summable (fun j : ℕ => ((j : ℝ) * Real.log 2 + 1) * r ^ j) := by
      refine ((h1.mul_left (Real.log 2)).add h2).congr fun j => ?_
      ring
    set C : ℝ := ∑' j : ℕ, ((j : ℝ) * Real.log 2 + 1) * r ^ j with hCdef
    have hterm : ∀ j : ℕ, (0:ℝ) ≤ ((j : ℝ) * Real.log 2 + 1) * r ^ j := by
      intro j
      have hl : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have : (0:ℝ) ≤ (j : ℝ) * Real.log 2 + 1 := by positivity
      positivity
    have hCpos : 0 < C := by
      have h0 := hsumj.le_tsum 0 (fun j _ => hterm j)
      simp only [Nat.cast_zero, zero_mul, zero_add, pow_zero, one_mul] at h0
      rw [hCdef]
      linarith
    refine ⟨C, hCpos, fun N hN => ?_⟩
    have hphi : 0 ≤ phi d N := phi_nonneg d hN
    have hrj : ∀ j : ℕ, (2:ℝ) ^ (-(j : ℝ) * θ) = r ^ j := by
      intro j
      rw [hrdef, ← two_rpow_mul]
      congr 1
      ring
    have hmaj : ∀ j : ℕ, (2:ℝ) ^ (-(j : ℝ) * θ) * phi d (2 ^ j * N)
        ≤ ((j : ℝ) * Real.log 2 + 1) * r ^ j * phi d N := by
      intro j
      have hb := phi_two_pow_le_log hd4 j hN
      have h2' : (0:ℝ) < (2:ℝ) ^ (-(j : ℝ) * θ) := Real.rpow_pos_of_pos (by norm_num) _
      calc (2:ℝ) ^ (-(j : ℝ) * θ) * phi d (2 ^ j * N)
          ≤ (2:ℝ) ^ (-(j : ℝ) * θ) * (((j : ℝ) * Real.log 2 + 1) * phi d N) :=
            mul_le_mul_of_nonneg_left hb h2'.le
        _ = ((j : ℝ) * Real.log 2 + 1) * r ^ j * phi d N := by rw [hrj j]; ring
    have hnn : ∀ j : ℕ, (0:ℝ) ≤ (2:ℝ) ^ (-(j : ℝ) * θ) * phi d (2 ^ j * N) := by
      intro j
      have h2' : (0:ℝ) < (2:ℝ) ^ (-(j : ℝ) * θ) := Real.rpow_pos_of_pos (by norm_num) _
      have h4 : (0:ℝ) ≤ phi d (2 ^ j * N) := by
        refine phi_nonneg d ?_
        have hk : (1:ℝ) ≤ (2:ℝ) ^ j := one_le_pow₀ (by norm_num)
        nlinarith
      positivity
    have hsumr : Summable (fun j : ℕ => ((j : ℝ) * Real.log 2 + 1) * r ^ j * phi d N) :=
      hsumj.mul_right _
    have hsummable := hsumr.of_nonneg_of_le hnn hmaj
    refine ⟨hsummable, ?_⟩
    calc ∑' j : ℕ, (2:ℝ) ^ (-(j : ℝ) * θ) * phi d (2 ^ j * N)
        ≤ ∑' j : ℕ, ((j : ℝ) * Real.log 2 + 1) * r ^ j * phi d N :=
          hsummable.tsum_le_tsum hmaj hsumr
      _ = (∑' j : ℕ, ((j : ℝ) * Real.log 2 + 1) * r ^ j) * phi d N := tsum_mul_right
      _ = C * phi d N := by rw [hCdef]

end Parking

end
