/-
The optimization over the mean horizon in Step 1 of `prop:near-divisible`
(`parking.tex:2848-2859`).

Step 1 of that proposition combines `lem:mean-horizon` with `η_δ = ξ_δ - δ` to
get `E u_n^δ(0) ≤ C φ_d(M_n) - δ M_n`, and then says "taking the supremum over
`M ≥ 0` gives the upper bound", with order `δ^{-(4-d)/d}` below dimension four
and `C log(e/δ)` from dimension four.  This file is that supremum.

Both cases are one inequality of elementary calculus applied at the optimizing
parameter.  Below dimension four it is Young's inequality
`x^α ≤ α εx + (1-α) ε^{-α/(1-α)}` with `ε` chosen so that `C₀ α ε = δ`, which
leaves `δ(M+1) - δM = δ` plus a multiple of `δ^{-α/(1-α)}`; the exponent
`α = (4-d)/4` makes `α/(1-α) = (4-d)/d`, the paper's rate.  From dimension four
it is `log x ≤ x/a + log a - 1` with `a = C₀/δ`, which leaves `2δ` plus
`C₀ log(C₀/δ)`, and `log(C₀/δ) ≤ (1 + |log C₀|) log(e/δ)`.
-/
import Parking.Support.PhiSum
import Parking.Support.Near

noncomputable section

namespace Parking

theorem rpow_le_young {α ε x : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hε : 0 < ε) (hx : 0 ≤ x) :
    x ^ α ≤ α * (ε * x) + (1 - α) * ε ^ (-α / (1 - α)) := by
  have hone : (1:ℝ) - α ≠ 0 := by linarith
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := α) (w₂ := 1 - α)
    (p₁ := ε * x) (p₂ := ε ^ (-α / (1 - α)))
    hα0.le (by linarith) (by positivity) (by positivity) (by ring)
  have hprod : (ε * x) ^ α * (ε ^ (-α / (1 - α))) ^ (1 - α) = x ^ α := by
    rw [Real.mul_rpow hε.le hx, ← Real.rpow_mul hε.le]
    rw [div_mul_cancel₀ (-α) hone]
    rw [Real.rpow_neg hε.le]
    field_simp
  rw [hprod] at h
  exact h

theorem log_le_div_add (x a : ℝ) (hx : 0 < x) (ha : 0 < a) :
    Real.log x ≤ x / a + Real.log a - 1 := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < x / a by positivity)
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt ha)] at h
  linarith

/-- **The optimization of Step 1 of `prop:near-divisible`, below dimension four.**  The
supremum over the mean horizon of `C φ_d(M) - δ M` has order `δ^{-(4-d)/d}`. -/
theorem exists_pow_sub_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {C0 : ℝ} (hC0 : 0 < C0) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ Mv : ℝ, 0 ≤ Mv →
      C0 * (Mv + 1) ^ α - δ * Mv ≤ C * δ ^ (-α / (1 - α)) := by
  have hone : (0:ℝ) < 1 - α := by linarith
  set β : ℝ := -α / (1 - α) with hβ
  have hβ0 : β ≤ 0 := by
    rw [hβ]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hone.le
  refine ⟨1 + C0 * (1 - α) * (C0 * α) ^ (-β), by positivity, fun δ hδ hδ1 Mv hMv => ?_⟩
  set ε : ℝ := δ / (C0 * α) with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hyoung := rpow_le_young (α := α) (ε := ε) (x := Mv + 1) hα0 hα1 hε0 (by linarith)
  have hCαε : C0 * (α * (ε * (Mv + 1))) = δ * (Mv + 1) := by
    rw [hε]; field_simp
  have hεβ : ε ^ β = δ ^ β * (C0 * α) ^ (-β) := by
    rw [hε, Real.div_rpow hδ.le (by positivity), Real.rpow_neg (by positivity : (0:ℝ) ≤ C0 * α)]
    field_simp
  have hδβ : (1:ℝ) ≤ δ ^ β := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 hβ0
  have hmain : C0 * (Mv + 1) ^ α ≤ δ * (Mv + 1) + C0 * (1 - α) * (δ ^ β * (C0 * α) ^ (-β)) := by
    have h1 : C0 * (Mv + 1) ^ α
        ≤ C0 * (α * (ε * (Mv + 1)) + (1 - α) * ε ^ β) :=
      mul_le_mul_of_nonneg_left hyoung hC0.le
    rw [mul_add, hCαε] at h1
    rw [hεβ] at h1
    linarith [h1]
  have hpos : (0:ℝ) ≤ C0 * (1 - α) * (C0 * α) ^ (-β) := by positivity
  nlinarith [hmain, hδβ, hpos, hδ.le]

/-- **The optimization of Step 1 of `prop:near-divisible`, from dimension four.**  The
supremum over the mean horizon of `C log(M+2) - δ M` has order `log(e/δ)`. -/
theorem exists_log_sub_le {C0 : ℝ} (hC0 : 0 < C0) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ Mv : ℝ, 0 ≤ Mv →
      C0 * Real.log (Mv + 2) - δ * Mv ≤ C * Real.log (Real.exp 1 / δ) := by
  refine ⟨2 + C0 * (1 + |Real.log C0|), by positivity, fun δ hδ hδ1 Mv hMv => ?_⟩
  have hlogδ : 0 ≤ -Real.log δ := by
    have : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
    linarith
  have hE : Real.log (Real.exp 1 / δ) = 1 - Real.log δ := by
    rw [Real.log_div (by positivity) (ne_of_gt hδ), Real.log_exp]
  have hE1 : (1:ℝ) ≤ Real.log (Real.exp 1 / δ) := by rw [hE]; linarith
  have hstep := log_le_div_add (Mv + 2) (C0 / δ) (by linarith) (by positivity)
  have hdiv : (Mv + 2) / (C0 / δ) = δ * (Mv + 2) / C0 := by field_simp
  rw [hdiv] at hstep
  have hlogC : Real.log (C0 / δ) = Real.log C0 - Real.log δ := by
    rw [Real.log_div (ne_of_gt hC0) (ne_of_gt hδ)]
  rw [hlogC] at hstep
  have h1 : C0 * Real.log (Mv + 2) - δ * Mv
      ≤ 2 * δ + C0 * (Real.log C0 - Real.log δ) - C0 := by
    have := mul_le_mul_of_nonneg_left hstep hC0.le
    have hcancel : C0 * (δ * (Mv + 2) / C0) = δ * (Mv + 2) := by field_simp
    nlinarith [this, hcancel]
  have h2 : Real.log C0 - Real.log δ ≤ (1 + |Real.log C0|) * Real.log (Real.exp 1 / δ) := by
    have hb : Real.log C0 ≤ |Real.log C0| := le_abs_self _
    have habs : 0 ≤ |Real.log C0| := abs_nonneg _
    nlinarith [hE1, hlogδ, hb, habs, hE]
  nlinarith [h1, h2, hE1, hC0.le, hδ.le, hδ1]

/-- **Step 1 of `prop:near-divisible`, the optimization over the mean horizon**
(`parking.tex:2851-2858`).  Taking the supremum over `M ≥ 0` of `C φ_d(M) - δ M` gives
the four rates of `eq:near-divisible-upper`. -/
theorem exists_phi_sub_le_nearRate (d : ℕ) (hd : 1 ≤ d) {C0 : ℝ} (hC0 : 0 < C0) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ Mv : ℝ, 0 ≤ Mv →
      C0 * phi d Mv - δ * Mv ≤ C * Parking.nearRate d δ := by
  by_cases h1 : d = 1
  · subst h1
    obtain ⟨C, hC, hle⟩ := exists_pow_sub_le (α := (3:ℝ)/4) (by norm_num) (by norm_num) hC0
    refine ⟨C, hC, fun δ hδ hδ1 Mv hMv => ?_⟩
    have hphi : phi 1 Mv = (Mv + 1) ^ ((3:ℝ)/4) := by
      rw [phi, if_pos (by norm_num : (1:ℕ) ≤ 3)]
      norm_num
    have hrate : Parking.nearRate 1 δ = δ ^ (-((3:ℝ)/4) / (1 - (3:ℝ)/4)) := by
      rw [Parking.nearRate, if_pos rfl]
      norm_num
    rw [hphi, hrate]
    exact hle δ hδ hδ1 Mv hMv
  by_cases h2 : d = 2
  · subst h2
    obtain ⟨C, hC, hle⟩ := exists_pow_sub_le (α := (1:ℝ)/2) (by norm_num) (by norm_num) hC0
    refine ⟨C, hC, fun δ hδ hδ1 Mv hMv => ?_⟩
    have hphi : phi 2 Mv = (Mv + 1) ^ ((1:ℝ)/2) := by
      rw [phi, if_pos (by norm_num : (2:ℕ) ≤ 3)]
      norm_num
    have hrate : Parking.nearRate 2 δ = δ ^ (-((1:ℝ)/2) / (1 - (1:ℝ)/2)) := by
      rw [Parking.nearRate, if_neg (by norm_num : ¬(2:ℕ) = 1), if_pos rfl]
      norm_num
      rw [Real.rpow_neg_one]
    rw [hphi, hrate]
    exact hle δ hδ hδ1 Mv hMv
  by_cases h3 : d = 3
  · subst h3
    obtain ⟨C, hC, hle⟩ := exists_pow_sub_le (α := (1:ℝ)/4) (by norm_num) (by norm_num) hC0
    refine ⟨C, hC, fun δ hδ hδ1 Mv hMv => ?_⟩
    have hphi : phi 3 Mv = (Mv + 1) ^ ((1:ℝ)/4) := by
      rw [phi, if_pos (by norm_num : (3:ℕ) ≤ 3)]
      norm_num
    have hrate : Parking.nearRate 3 δ = δ ^ (-((1:ℝ)/4) / (1 - (1:ℝ)/4)) := by
      rw [Parking.nearRate, if_neg (by norm_num : ¬(3:ℕ) = 1),
        if_neg (by norm_num : ¬(3:ℕ) = 2), if_pos rfl]
      norm_num
    rw [hphi, hrate]
    exact hle δ hδ hδ1 Mv hMv
  · have hd4 : 4 ≤ d := by omega
    obtain ⟨C, hC, hle⟩ := exists_log_sub_le hC0
    refine ⟨C, hC, fun δ hδ hδ1 Mv hMv => ?_⟩
    have hphi : phi d Mv = Real.log (Mv + 2) := by
      rw [phi, if_neg (by omega : ¬ d ≤ 3)]
    have hrate : Parking.nearRate d δ = Real.log (Real.exp 1 / δ) := by
      rw [Parking.nearRate, if_neg (by omega : ¬ d = 1), if_neg (by omega : ¬ d = 2),
        if_neg (by omega : ¬ d = 3)]
    rw [hphi, hrate]
    exact hle δ hδ hδ1 Mv hMv

end Parking

end
