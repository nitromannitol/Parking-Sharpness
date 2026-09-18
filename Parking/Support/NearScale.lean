/-
Two comparisons in the scale `env`, used to read the quantities of Step 3 of the upper
bounds of `thm:near` at the cutoff (`parking.tex:2944-2978`).

Every quantity read at the cutoff is either a power `n^β` with `0 ≤ β ≤ 1` (the rates
`κ_1`, `κ_3`, `φ_d` below dimension four and the two Green rates below dimension four)
or a logarithm `log(n + c)` (the rates `κ_2`, `φ_d` from dimension four on, and the
Green rates from dimension two on).  A power of a bound in the scale is a bound in the
scale with the exponent of `1/δ` multiplied by `β`, and a logarithm of a bound in the
scale is a constant multiple of `log(e/δ)`, because `log(δ^{-α}L^k) = α(L-1) + k log L`
and `log L ≤ L`.
-/
import Parking.Support.NearEnv

noncomputable section
namespace Parking

theorem rpow_le_env {α β : ℝ} {k : ℕ} {C₀ x δ : ℝ} (hC₀ : 0 < C₀) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hx : 0 ≤ x)
    (hxle : x ≤ C₀ * env α k δ) : x ^ β ≤ max 1 C₀ * env (α * β) k δ := by
  have henv : 0 < env α k δ := env_pos hδ0 hδ1
  have h1 : x ^ β ≤ (C₀ * env α k δ) ^ β := Real.rpow_le_rpow hx hxle hβ0
  have h2 : (C₀ * env α k δ) ^ β = C₀ ^ β * (env α k δ) ^ β :=
    Real.mul_rpow hC₀.le henv.le
  have h3 : (env α k δ) ^ β ≤ env (α * β) k δ := rpow_env_le hδ0 hδ1 hβ1
  have h4 : C₀ ^ β ≤ max 1 C₀ := by
    rcases le_total C₀ 1 with hle | hle
    · exact le_trans (Real.rpow_le_one hC₀.le hle hβ0) (le_max_left _ _)
    · refine le_trans ?_ (le_max_right 1 C₀)
      have h := Real.rpow_le_rpow_of_exponent_le hle hβ1
      rwa [Real.rpow_one] at h
  have h5 : (0 : ℝ) ≤ C₀ ^ β := Real.rpow_nonneg hC₀.le β
  have h6 : (0 : ℝ) ≤ env (α * β) k δ := (env_pos hδ0 hδ1).le
  calc x ^ β ≤ C₀ ^ β * (env α k δ) ^ β := by rw [← h2]; exact h1
    _ ≤ C₀ ^ β * env (α * β) k δ := mul_le_mul_of_nonneg_left h3 h5
    _ ≤ max 1 C₀ * env (α * β) k δ := mul_le_mul_of_nonneg_right h4 h6

theorem exists_log_le_env {α : ℝ} {k : ℕ} {C₀ : ℝ} (hC₀ : 0 < C₀) (hα : 0 ≤ α)
    {c : ℝ} (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ x δ : ℝ, 0 < δ → δ ≤ 1 → 0 ≤ x → x ≤ C₀ * env α k δ →
      Real.log (x + c) ≤ C * env 0 1 δ := by
  refine ⟨|Real.log (C₀ + c + 1)| + α + (k : ℝ) + 1, by positivity,
    fun x δ hδ0 hδ1 hx hxle => ?_⟩
  have hL : 1 ≤ Real.log (Real.exp 1 / δ) := one_le_bigL hδ0 hδ1
  have hE1 : 1 ≤ env α k δ := one_le_env hδ0 hδ1 hα
  have hEpos : 0 < env α k δ := env_pos hδ0 hδ1
  have hLdef : Real.log (Real.exp 1 / δ) = 1 - Real.log δ := by
    rw [Real.log_div (Real.exp_ne_zero 1) (ne_of_gt hδ0), Real.log_exp]
  have hlogE : Real.log (env α k δ) ≤ (α + (k : ℝ)) * Real.log (Real.exp 1 / δ) := by
    rw [env, Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hδ0 _))
      (by positivity), Real.log_rpow hδ0, Real.log_pow]
    have hlogL : Real.log (Real.log (Real.exp 1 / δ)) ≤ Real.log (Real.exp 1 / δ) - 1 :=
      Real.log_le_sub_one_of_pos (by linarith)
    nlinarith [hL, hLdef, Nat.cast_nonneg (α := ℝ) k]
  have hstep : x + c ≤ (C₀ + c + 1) * env α k δ := by nlinarith
  have hpos : 0 < (C₀ + c + 1) * env α k δ := by positivity
  have hlog : Real.log (x + c) ≤ Real.log ((C₀ + c + 1) * env α k δ) := by
    rcases le_or_gt (x + c) 0 with h | h
    · have heq : x + c = 0 := le_antisymm h (by linarith)
      rw [heq, Real.log_zero]
      exact Real.log_nonneg (by nlinarith)
    · exact Real.log_le_log h hstep
  rw [Real.log_mul (by positivity) (ne_of_gt hEpos)] at hlog
  have habs : Real.log (C₀ + c + 1) ≤ |Real.log (C₀ + c + 1)| := le_abs_self _
  rw [env_log δ]
  nlinarith [hlog, hlogE, habs, hL, abs_nonneg (Real.log (C₀ + c + 1))]

end Parking
end
