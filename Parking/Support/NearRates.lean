/-
The elementary rate comparisons behind the choice of the cutoff `eq:near-cutoff`
and of the exponent `r ≍ log(e/δ)` of Step 3 of the upper bounds of `thm:near`
(`parking.tex:2952-2978`).

A power of `log(e/δ)` is bounded by a constant times any negative power of `δ`:
writing `x = δ^{-p/k}`, so that `log(e/δ) = 1 + (k/p) log x` and `log x ≤ x - 1 ≤ x`
with `x ≥ 1`, gives `log(e/δ) ≤ (1 + k/p)x` and hence
`log(e/δ)^k δ^p ≤ (1 + k/p)^k`.  This is what turns each error term of Step 3, which
carries powers of `δ` and of `log(e/δ)`, into a constant multiple of the rate of
`eq:near`, whose power of `δ` is strictly larger.
-/
import Mathlib

noncomputable section
namespace Parking

/-- A power of `log(e/δ)` against a negative power of `δ`. -/
theorem exists_log_pow_mul_rpow_le (k : ℕ) {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      Real.log (Real.exp 1 / δ) ^ k * δ ^ p ≤ C :=
by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    refine ⟨1, one_pos, ?_⟩
    intro δ hδ hδ1
    simp only [pow_zero, one_mul]
    have h := Real.rpow_le_rpow (le_of_lt hδ) hδ1 (le_of_lt hp)
    rwa [Real.one_rpow] at h
  · have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
    have hkne : (k:ℝ) ≠ 0 := ne_of_gt hkR
    refine ⟨(1 + (k:ℝ)/p)^k, ?_, ?_⟩
    · have hkp : (0:ℝ) < (k:ℝ)/p := div_pos hkR hp
      exact pow_pos (by linarith) k
    · intro δ hδ hδ1
      set t : ℝ := p / (k:ℝ) with ht_def
      have ht : 0 < t := by rw [ht_def]; exact div_pos hp hkR
      have htne : t ≠ 0 := ne_of_gt ht
      set x : ℝ := δ ^ (-t) with hx_def
      have hx1 : 1 ≤ x := by
        rw [hx_def]
        exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
      have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
      have hlogx : Real.log x = -t * Real.log δ := by
        rw [hx_def]; exact Real.log_rpow hδ (-t)
      have hLx : Real.log x / t = -Real.log δ := by
        rw [hlogx, div_eq_iff htne]; ring
      have hL : Real.log (Real.exp 1 / δ) = 1 + Real.log x / t := by
        have h1 : Real.log (Real.exp 1 / δ) = 1 - Real.log δ := by
          rw [Real.log_div (Real.exp_ne_zero 1) (ne_of_gt hδ), Real.log_exp]
        rw [h1, hLx]; ring
      have hL_nonneg : 0 ≤ Real.log (Real.exp 1 / δ) := by
        rw [hL]
        have hlx : 0 ≤ Real.log x := Real.log_nonneg hx1
        have : 0 ≤ Real.log x / t := div_nonneg hlx (le_of_lt ht)
        linarith
      have hL_le : Real.log (Real.exp 1 / δ) ≤ (1 + 1/t) * x := by
        rw [hL]
        have hlogx_le : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hxpos
        have h2 : 1 + Real.log x / t ≤ 1 + x / t := by
          have : Real.log x / t ≤ x / t :=
            div_le_div_of_nonneg_right (by linarith) (le_of_lt ht)
          linarith
        have h3 : 1 + x / t ≤ (1 + 1/t) * x := by
          have : (1 + 1/t) * x = x + x/t := by ring
          rw [this]; linarith
        linarith
      have hpow : Real.log (Real.exp 1 / δ) ^ k ≤ ((1 + 1/t) * x)^k :=
        pow_le_pow_left₀ hL_nonneg hL_le k
      have htk : t * (k:ℝ) = p := by
        rw [ht_def]; exact div_mul_cancel₀ p hkne
      have hxk : x ^ k = δ ^ (-p) := by
        rw [hx_def, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
        congr 1
        nlinarith [htk]
      have h2 : δ ^ (-p) * δ ^ p = 1 := by
        rw [← Real.rpow_add hδ, neg_add_cancel, Real.rpow_zero]
      have h1 : Real.log (Real.exp 1 / δ) ^ k * δ ^ p ≤ (1 + 1/t)^k * δ^(-p) * δ^p := by
        have := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hδ.le p)
        rwa [mul_pow, hxk] at this
      have ht_inv : 1/t = (k:ℝ)/p := by
        rw [ht_def, one_div, inv_div]
      calc Real.log (Real.exp 1 / δ) ^ k * δ ^ p
          ≤ (1 + 1/t)^k * δ^(-p) * δ^p := h1
        _ = (1 + 1/t)^k * (δ^(-p) * δ^p) := by ring
        _ = (1 + 1/t)^k := by rw [h2, mul_one]
        _ = (1 + (k:ℝ)/p)^k := by rw [ht_inv]

end Parking

end
