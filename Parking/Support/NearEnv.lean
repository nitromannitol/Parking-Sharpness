/-
The scale in which Step 3 of the upper bounds of `thm:near` is read
(`parking.tex:2944-2978`).

Every quantity there is a product of a power of `1/δ` and a power of
`L = log(e/δ)`: the cutoff `N` of `eq:near-cutoff`, the exponent `r ≍ L`, the
Green quantities of `eq:green-norms` read at `N`, and the rates
`κ_d(N)` and `φ_d(N)`.  The rate of `eq:near` itself is `δ^{-(4-d)/d}` below
dimension four and `L` from dimension four on.  Writing all of them in the single
scale `δ^{-α}L^k` turns Step 3's comparisons into two facts: the scale is
multiplicative, and a power of `L` is absorbed by any strictly larger power of
`1/δ`.
-/
import Parking.Support.NearRates
import Parking.Support.Near
import Parking.Support.Pathwise

noncomputable section
namespace Parking
variable {d : ℕ}

/-- The scale `δ^{-α} log(e/δ)^k` in which every term of Step 3 of the upper bounds is
read. -/
def env (α : ℝ) (k : ℕ) (δ : ℝ) : ℝ := δ ^ (-α) * Real.log (Real.exp 1 / δ) ^ k

theorem one_le_bigL {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ Real.log (Real.exp 1 / δ) := by
  rw [Real.log_div (Real.exp_ne_zero 1) (ne_of_gt hδ0), Real.log_exp]
  have h := Real.log_nonpos hδ0.le hδ1
  linarith

theorem env_pos {α : ℝ} {k : ℕ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) : 0 < env α k δ := by
  have hL := one_le_bigL hδ0 hδ1
  exact mul_pos (Real.rpow_pos_of_pos hδ0 _) (pow_pos (by linarith) k)

theorem env_mul (α β : ℝ) (k l : ℕ) {δ : ℝ} (hδ0 : 0 < δ) :
    env α k δ * env β l δ = env (α + β) (k + l) δ := by
  simp only [env, neg_add, Real.rpow_add hδ0, pow_add]
  ring

theorem env_mono {α α' : ℝ} {k k' : ℕ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hα : α ≤ α') (hk : k ≤ k') : env α k δ ≤ env α' k' δ := by
  have hL := one_le_bigL hδ0 hδ1
  have h1 : δ ^ (-α) ≤ δ ^ (-α') :=
    Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
  have h2 : Real.log (Real.exp 1 / δ) ^ k ≤ Real.log (Real.exp 1 / δ) ^ k' :=
    pow_le_pow_right₀ hL hk
  exact mul_le_mul h1 h2 (pow_nonneg (by linarith) k) (Real.rpow_nonneg hδ0.le _)

/-- A power of the logarithm is absorbed by any strictly larger power of `1/δ`. -/
theorem exists_env_le (k : ℕ) {α α' : ℝ} (h : α < α') :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → env α k δ ≤ C * env α' 0 δ := by
  obtain ⟨C, hC, hCle⟩ := exists_log_pow_mul_rpow_le k (by linarith : (0 : ℝ) < α' - α)
  refine ⟨C, hC, fun δ hδ0 hδ1 => ?_⟩
  have h1 : env α k δ
      = δ ^ (-α') * (Real.log (Real.exp 1 / δ) ^ k * δ ^ (α' - α)) := by
    rw [env, show (-α) = -α' + (α' - α) by ring, Real.rpow_add hδ0]
    ring
  have h2 := hCle δ hδ0 hδ1
  have h3 : (0 : ℝ) ≤ δ ^ (-α') := Real.rpow_nonneg hδ0.le _
  rw [h1, env, pow_zero, mul_one]
  nlinarith

theorem env_zero (α : ℝ) (δ : ℝ) : env α 0 δ = δ ^ (-α) := by
  rw [env, pow_zero, mul_one]

theorem env_log (δ : ℝ) : env 0 1 δ = Real.log (Real.exp 1 / δ) := by
  rw [env, neg_zero, Real.rpow_zero, one_mul, pow_one]

/-- The rate of `eq:near` in the scale `env`. -/
theorem nearRate_eq_env (d : ℕ) (δ : ℝ) :
    Parking.nearRate d δ
      = if d = 1 then env 3 0 δ else if d = 2 then env 1 0 δ
        else if d = 3 then env (1 / 3) 0 δ else env 0 1 δ := by
  rw [Parking.nearRate]
  split_ifs with h1 h2 h3
  · rw [env_zero]
  · rw [env_zero, Real.rpow_neg_one]
  · rw [env_zero]; norm_num
  · rw [env_log δ]

/-- The sandpile odometer is monotone in the scenery. -/
theorem u_mono_field (hd : 1 ≤ d) {f g : Site d → ℝ} (h : ∀ y, f y ≤ g y) (n : ℕ)
    (x : Site d) : u f n x ≤ u g n x := by
  induction n generalizing x with
  | zero => simp [u]
  | succ n ih =>
      rw [u, u]
      exact max_le_max (le_refl 0) (add_le_add (h x) (walkOp_mono hd (fun y => ih y) x))

theorem one_le_env {α : ℝ} {k : ℕ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hα : 0 ≤ α) :
    1 ≤ env α k δ := by
  have hL := one_le_bigL hδ0 hδ1
  have h1 : (1 : ℝ) ≤ δ ^ (-α) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ0 hδ1 (by linarith)
  have h2 : (1 : ℝ) ≤ Real.log (Real.exp 1 / δ) ^ k := one_le_pow₀ hL
  rw [env]
  nlinarith

theorem rpow_env_le {α : ℝ} {k : ℕ} {δ β : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hβ1 : β ≤ 1) : (env α k δ) ^ β ≤ env (α * β) k δ := by
  have hL := one_le_bigL hδ0 hδ1
  have hLk : (1 : ℝ) ≤ Real.log (Real.exp 1 / δ) ^ k := one_le_pow₀ hL
  have hδr : (0 : ℝ) < δ ^ (-α) := Real.rpow_pos_of_pos hδ0 _
  have hfac : (env α k δ) ^ β
      = (δ ^ (-α)) ^ β * (Real.log (Real.exp 1 / δ) ^ k) ^ β := by
    rw [env, Real.mul_rpow hδr.le (by positivity)]
  rw [hfac]
  have h1 : (δ ^ (-α)) ^ β = δ ^ (-(α * β)) := by
    rw [← Real.rpow_mul hδ0.le]
    congr 1
    ring
  have h2 : (Real.log (Real.exp 1 / δ) ^ k) ^ β ≤ Real.log (Real.exp 1 / δ) ^ k := by
    have h := Real.rpow_le_rpow_of_exponent_le hLk hβ1
    rwa [Real.rpow_one] at h
  rw [h1, env]
  exact mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hδ0.le _)

theorem sqrt_env_le {α : ℝ} {k : ℕ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.sqrt (env α k δ) ≤ env (α / 2) k δ := by
  rw [Real.sqrt_eq_rpow]
  have h := rpow_env_le (α := α) (k := k) (δ := δ) (β := 1 / 2) hδ0 hδ1 (by norm_num)
  calc (env α k δ) ^ ((1 : ℝ) / 2) ≤ env (α * (1 / 2)) k δ := h
    _ = env (α / 2) k δ := by ring_nf

/-- The logarithm at the tilted exponent against the logarithm at `δ`. -/
theorem exists_log_scaled_le {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      Real.log (Real.exp 1 / (a * δ ^ 2)) ≤ C * Real.log (Real.exp 1 / δ) := by
  refine ⟨2 + |Real.log a|, by positivity, fun δ hδ0 hδ1 => ?_⟩
  have hL := one_le_bigL hδ0 hδ1
  have hLdef : Real.log (Real.exp 1 / δ) = 1 - Real.log δ := by
    rw [Real.log_div (Real.exp_ne_zero 1) (ne_of_gt hδ0), Real.log_exp]
  have hane : a * δ ^ 2 ≠ 0 := by positivity
  have hexp : Real.log (Real.exp 1 / (a * δ ^ 2))
      = 1 - Real.log a - 2 * Real.log δ := by
    rw [Real.log_div (Real.exp_ne_zero 1) hane, Real.log_exp, Real.log_mul (ne_of_gt ha)
      (by positivity), Real.log_pow]
    push_cast
    ring
  have habs : -Real.log a ≤ |Real.log a| := neg_le_abs _
  have ht : (0 : ℝ) ≤ -Real.log δ := by linarith
  rw [hexp]
  nlinarith [hL, habs, abs_nonneg (Real.log a),
    mul_nonneg (abs_nonneg (Real.log a)) ht]

end Parking

end
