/-
The five products of Step 3 of the near-critical upper bounds
(`parking.tex:2944-2978`), each read at the cutoff `eq:near-cutoff` and compared with
the rate of `eq:near`.

With `R = nearRate d δ`, `r = rHigh N` and `κ = κ_d(N)` the five are

  r ≤ A R,   r κ ≤ A R,   r κ φ_d(N) ≤ A R²,
  r κ (√r ‖g_N‖₂) ≤ A R²,   r κ (r max_x g_N(x)) ≤ A R².

Below dimension four the power of `1/δ` on the right is strictly larger than on the
left and every power of `log(e/δ)` is absorbed.  From dimension four on the rate IS
`log(e/δ)`, so the powers of the logarithm must be counted exactly: there `κ_d(N)` and
`max_x g_N(x)` are equal to one, and `√r ‖g_N‖₂` is of the order of `log(e/δ)` only
because each of its two factors is of the order of the square root of that, so the
product is bounded as a product and never factor by factor.
-/
import Parking.Support.NearRateBounds

noncomputable section
namespace Parking
variable {d : ℕ}

/-! ### The scale of each quantity, as a power of `1/δ` and a power of `log(e/δ)` -/

/-- The power of `1/δ` in the rate of `eq:near`. -/
def rateExp (d : ℕ) : ℝ :=
  if d = 1 then 3 else if d = 2 then 1 else if d = 3 then 1 / 3 else 0

/-- The power of `log(e/δ)` in the rate of `eq:near`. -/
def rateLog (d : ℕ) : ℕ := if d = 1 then 0 else if d = 2 then 0 else if d = 3 then 0 else 1

/-- The power of `1/δ` in the scale of `κ_d` and of `max_x g_N(x)` at the cutoff. -/
def kExp (d : ℕ) : ℝ := if d = 1 then 2 else 0

/-- The power of `log(e/δ)` in that scale.  From dimension three on both quantities are
equal to one, so the power is zero. -/
def kLog (d : ℕ) : ℕ := if d = 1 then 3 else if d = 2 then 1 else 0

/-- The power of `1/δ` in the scale of `φ_d(N)` and of `‖g_N‖₂` at the cutoff. -/
def pExp (d : ℕ) : ℝ :=
  if d = 1 then 3 else if d = 2 then 1 else if d = 3 then 1 / 2 else 0

/-- The power of `log(e/δ)` in that scale. -/
def pLog (d : ℕ) : ℕ := if d = 1 then 3 else if d = 2 then 3 else if d = 3 then 2 else 1

/-- The power of `log(e/δ)` in the scale of the product `√r ‖g_N‖₂` at the cutoff. -/
def qLog (d : ℕ) : ℕ := if d = 1 then 4 else if d = 2 then 4 else if d = 3 then 3 else 1

/-- The scale of `κ_d` and of the maximum of the Green function at the cutoff. -/
def kEnv (d : ℕ) (δ : ℝ) : ℝ := env (kExp d) (kLog d) δ

/-- The scale of the product `√r ‖g_N‖₂` at the cutoff. -/
def qEnv (d : ℕ) (δ : ℝ) : ℝ := env (pExp d) (qLog d) δ

/-! ### The algebra of the scale -/

theorem env_one (δ : ℝ) : env 0 0 δ = 1 := by
  rw [env]; norm_num

theorem env_sq (α : ℝ) (k : ℕ) {δ : ℝ} (hδ0 : 0 < δ) :
    env α k δ ^ 2 = env (2 * α) (2 * k) δ := by
  have h : env α k δ * env α k δ = env (α + α) (k + k) δ := env_mul α α k k hδ0
  rw [sq, h, show α + α = 2 * α from by ring, show k + k = 2 * k from by omega]

/-- A power of the logarithm is absorbed by a strictly larger power of `1/δ`, and the
scale is monotone in both exponents. -/
theorem exists_env_le_env {α α' : ℝ} {k k' : ℕ} (h : α < α' ∨ (α ≤ α' ∧ k ≤ k')) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → env α k δ ≤ C * env α' k' δ := by
  rcases h with h | ⟨h1, h2⟩
  · obtain ⟨C, hC, hCle⟩ := exists_env_le k h
    refine ⟨C, hC, fun δ hδ0 hδ1 => ?_⟩
    refine le_trans (hCle δ hδ0 hδ1) ?_
    exact mul_le_mul_of_nonneg_left (env_mono hδ0 hδ1 le_rfl (Nat.zero_le k')) hC.le
  · refine ⟨1, one_pos, fun δ hδ0 hδ1 => ?_⟩
    rw [one_mul]
    exact env_mono hδ0 hδ1 h1 h2

/-- **The product of two quantities bounded in the scale.**  The exponents add, and the
sum is then compared with the target exponents. -/
theorem env_prod_le {α β α' : ℝ} {k l k' : ℕ} {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hcmp : α + β < α' ∨ (α + β ≤ α' ∧ k + l ≤ k')) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y δ : ℝ, 0 < δ → δ ≤ 1 → 0 ≤ x → 0 ≤ y →
      x ≤ A * env α k δ → y ≤ B * env β l δ → x * y ≤ C * env α' k' δ := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_env_le_env hcmp
  refine ⟨A * B * C₁, by positivity, fun x y δ hδ0 hδ1 hx0 hy0 hx hy => ?_⟩
  have hEa : (0 : ℝ) ≤ env α k δ := (env_pos hδ0 hδ1).le
  have hEb : (0 : ℝ) ≤ env β l δ := (env_pos hδ0 hδ1).le
  have hstep : x * y ≤ (A * env α k δ) * (B * env β l δ) :=
    mul_le_mul hx hy hy0 (by positivity)
  have heq : (A * env α k δ) * (B * env β l δ) = A * B * env (α + β) (k + l) δ := by
    rw [← env_mul α β k l hδ0]; ring
  have hlast : env (α + β) (k + l) δ ≤ C₁ * env α' k' δ := h₁ δ hδ0 hδ1
  rw [heq] at hstep
  have hmul : A * B * env (α + β) (k + l) δ ≤ A * B * (C₁ * env α' k' δ) :=
    mul_le_mul_of_nonneg_left hlast (by positivity)
  linarith [hstep, hmul]

/-! ### The rate and its square in the scale -/

theorem nearRate_eq (d : ℕ) (δ : ℝ) : Parking.nearRate d δ = env (rateExp d) (rateLog d) δ := by
  rw [Parking.nearRate_eq_env d δ, rateExp, rateLog]
  split_ifs <;> rfl

theorem nearRate_sq_eq (d : ℕ) {δ : ℝ} (hδ0 : 0 < δ) :
    Parking.nearRate d δ ^ 2 = env (2 * rateExp d) (2 * rateLog d) δ := by
  rw [nearRate_eq d δ, env_sq _ _ hδ0]

theorem one_le_nearRate (d : ℕ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ Parking.nearRate d δ := by
  rw [nearRate_eq d δ]
  refine one_le_env hδ0 hδ1 ?_
  rw [rateExp]; split_ifs <;> norm_num

theorem nearRate_nonneg (d : ℕ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    0 ≤ Parking.nearRate d δ := le_trans zero_le_one (one_le_nearRate d hδ0 hδ1)

/-! ### Nonnegativity of the five quantities -/

theorem rHigh_nonneg (n : ℕ) : (0 : ℝ) ≤ rHigh n := (rHigh_pos n).le

theorem greenL2Rate_nonneg (d n : ℕ) : 0 ≤ Parking.External.greenL2Rate d n := by
  rw [Parking.External.greenL2Rate]
  split_ifs
  · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  · exact Real.sqrt_nonneg _
  · norm_num

theorem greenMaxRate_nonneg (d n : ℕ) : 0 ≤ Parking.External.greenMaxRate d n := by
  rw [Parking.External.greenMaxRate]
  split_ifs
  · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  · exact Real.log_natCast_nonneg n
  · norm_num

theorem phi_nonneg' (d n : ℕ) : (0 : ℝ) ≤ Parking.phi d (n : ℝ) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [Parking.phi]
  split_ifs
  · exact Real.rpow_nonneg (by linarith) _
  · exact Real.log_nonneg (by linarith)

/-! ### The exponent, the walk factor, the growth rate and the Green quantities -/

/-- `r = rHigh N` is always `j + 2` for a natural `j`, which is the exponent at which
`eq:near-centered-moment` is available. -/
theorem exists_rHigh_eq (N : ℕ) : ∃ j : ℕ, rHigh N = (j : ℝ) + 2 := by
  rcases le_or_gt (Nat.ceil (Real.log ((N : ℝ) + 1))) 2 with h | h
  · refine ⟨0, ?_⟩
    have hcle : ((Nat.ceil (Real.log ((N : ℝ) + 1)) : ℕ) : ℝ) ≤ 2 := by exact_mod_cast h
    rw [rHigh, max_eq_left hcle]
    norm_num
  · refine ⟨Nat.ceil (Real.log ((N : ℝ) + 1)) - 2, ?_⟩
    have hcge : (2 : ℝ) ≤ ((Nat.ceil (Real.log ((N : ℝ) + 1)) : ℕ) : ℝ) := by
      exact_mod_cast h.le
    rw [rHigh, max_eq_right hcge, Nat.cast_sub h.le]
    norm_num

/-- The three cases of the scale of `κ_d` and of the maximum of the Green function. -/
theorem kEnv_cases (d : ℕ) (δ : ℝ) :
    kEnv d δ = if d = 1 then env 2 3 δ else if d = 2 then env 0 1 δ
      else env 0 0 δ := by
  rw [kEnv, kExp, kLog]
  split_ifs <;> rfl

/-- The four cases of the scale of the product `√r ‖g_N‖₂`. -/
theorem qEnv_cases (d : ℕ) (δ : ℝ) :
    qEnv d δ = if d = 1 then env 3 4 δ else if d = 2 then env 1 4 δ
      else if d = 3 then env (1 / 2) 3 δ else env 0 1 δ := by
  rw [qEnv, pExp, qLog]
  split_ifs <;> rfl

/-- `κ_d(N)` at the cutoff, read exactly: from dimension three on it is one. -/
theorem exists_kappa_le_kEnv (d : ℕ) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ((N : ℝ) ≤ C₀ * cutoffEnv d δ) → Parking.kappa d N ≤ C * kEnv d δ := by
  by_cases h1 : d = 1
  · obtain ⟨C, hC, hCle⟩ := exists_kappa_le_env d hC₀
    refine ⟨C, hC, fun N δ hδ0 hδ1 hN => ?_⟩
    rw [kEnv_cases, if_pos h1]
    have h := hCle N δ hδ0 hδ1 hN
    rwa [kappaEnv, if_pos h1] at h
  by_cases h2 : d = 2
  · obtain ⟨C, hC, hCle⟩ := exists_kappa_le_env d hC₀
    refine ⟨C, hC, fun N δ hδ0 hδ1 hN => ?_⟩
    rw [kEnv_cases, if_neg h1, if_pos h2]
    have h := hCle N δ hδ0 hδ1 hN
    rwa [kappaEnv, if_neg h1] at h
  · refine ⟨1, one_pos, fun N δ hδ0 hδ1 hN => ?_⟩
    rw [kEnv_cases, if_neg h1, if_neg h2, env_one, Parking.kappa, if_neg h1, if_neg h2]
    norm_num

/-- `max_x g_N(x)` at the cutoff, read exactly: from dimension three on it is one. -/
theorem exists_greenMaxRate_le_kEnv (d : ℕ) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ((N : ℝ) ≤ C₀ * cutoffEnv d δ) →
      Parking.External.greenMaxRate d N ≤ C * kEnv d δ := by
  by_cases h1 : d = 1
  · obtain ⟨C, hC, hCle⟩ := exists_greenMaxRate_le_env d hC₀
    refine ⟨C, hC, fun N δ hδ0 hδ1 hN => ?_⟩
    rw [kEnv_cases, if_pos h1]
    have h := hCle N δ hδ0 hδ1 hN
    rwa [kappaEnv, if_pos h1] at h
  by_cases h2 : d = 2
  · obtain ⟨C, hC, hCle⟩ := exists_greenMaxRate_le_env d hC₀
    refine ⟨C, hC, fun N δ hδ0 hδ1 hN => ?_⟩
    rw [kEnv_cases, if_neg h1, if_pos h2]
    have h := hCle N δ hδ0 hδ1 hN
    rwa [kappaEnv, if_neg h1] at h
  · refine ⟨1, one_pos, fun N δ hδ0 hδ1 hN => ?_⟩
    rw [kEnv_cases, if_neg h1, if_neg h2, env_one,
      Parking.External.greenMaxRate, if_neg h1, if_neg h2]
    norm_num

/-- `φ_d(N)` at the cutoff. -/
theorem rateEnv_eq (d : ℕ) (δ : ℝ) : rateEnv d δ = env (pExp d) (pLog d) δ := by
  rw [rateEnv, pExp, pLog]
  split_ifs <;> rfl

theorem exists_phi_le_pEnv (d : ℕ) (hd : 1 ≤ d) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ((N : ℝ) ≤ C₀ * cutoffEnv d δ) → Parking.phi d N ≤ C * env (pExp d) (pLog d) δ := by
  obtain ⟨C, hC, hCle⟩ := exists_phi_le_env d hd hC₀
  refine ⟨C, hC, fun N δ hδ0 hδ1 hN => ?_⟩
  rw [← rateEnv_eq]
  exact hCle N δ hδ0 hδ1 hN

/-- **`√r ‖g_N‖₂` at the cutoff, bounded as a product.**  From dimension four on each
factor is of the order of `√log(e/δ)` and only the product is of the order of
`log(e/δ)`; bounding the two factors separately would give a higher power there. -/
theorem exists_sqrtRHigh_greenL2_le (d : ℕ) (hd : 1 ≤ d) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 → 2 ≤ N →
      ((N : ℝ) ≤ C₀ * cutoffEnv d δ) →
      Real.sqrt (rHigh N) * Parking.External.greenL2Rate d N
        ≤ C * qEnv d δ := by
  obtain ⟨Cr, hCr, hr⟩ := exists_rHigh_le_env d hC₀
  by_cases h4 : 4 ≤ d
  · obtain ⟨Cs, hCs, hs⟩ := exists_greenL2Rate_sqrt_le d h4 hC₀
    refine ⟨Real.sqrt Cr * Cs, by positivity, fun N δ hδ0 hδ1 hN2 hN => ?_⟩
    have hE0 : (0 : ℝ) ≤ env 0 1 δ := (env_pos hδ0 hδ1).le
    have h1 : Real.sqrt (rHigh N)
        ≤ Real.sqrt Cr * Real.sqrt (env 0 1 δ) := by
      calc Real.sqrt (rHigh N) ≤ Real.sqrt (Cr * env 0 1 δ) :=
            Real.sqrt_le_sqrt (hr N δ hδ0 hδ1 hN2 hN)
        _ = Real.sqrt Cr * Real.sqrt (env 0 1 δ) := Real.sqrt_mul hCr.le _
    have h2 := hs N δ hδ0 hδ1 hN
    have hq : qEnv d δ = env 0 1 δ := by
      rw [qEnv_cases, if_neg (by omega : ¬ d = 1), if_neg (by omega : ¬ d = 2),
        if_neg (by omega : ¬ d = 3)]
    rw [hq]
    calc Real.sqrt (rHigh N) * Parking.External.greenL2Rate d N
        ≤ (Real.sqrt Cr * Real.sqrt (env 0 1 δ)) *
            (Cs * Real.sqrt (env 0 1 δ)) :=
          mul_le_mul h1 h2 (greenL2Rate_nonneg d N) (by positivity)
      _ = Real.sqrt Cr * Cs *
            (Real.sqrt (env 0 1 δ) * Real.sqrt (env 0 1 δ)) := by ring
      _ = Real.sqrt Cr * Cs * env 0 1 δ := by rw [Real.mul_self_sqrt hE0]
  · obtain ⟨CL, hCL, hL⟩ := exists_greenL2Rate_le_env d hC₀
    have hqp : qLog d = 1 + pLog d := by
      rw [qLog, pLog]
      split_ifs <;> omega
    obtain ⟨A, hA, hAle⟩ := env_prod_le (α := 0) (k := 1) (β := pExp d)
      (l := pLog d) (α' := pExp d) (k' := 1 + pLog d)
      (Real.sqrt_pos.mpr hCr) hCL (Or.inr ⟨by linarith, le_rfl⟩)
    refine ⟨A, hA, fun N δ hδ0 hδ1 hN2 hN => ?_⟩
    rw [qEnv, hqp]
    refine hAle _ _ δ hδ0 hδ1 (Real.sqrt_nonneg _) (greenL2Rate_nonneg d N) ?_ ?_
    · have hzero : (0 : ℝ) / 2 = 0 := by norm_num
      have hs2 := sqrt_env_le (α := 0) (k := 1) (δ := δ) hδ0 hδ1
      rw [hzero] at hs2
      calc Real.sqrt (rHigh N) ≤ Real.sqrt (Cr * env 0 1 δ) :=
            Real.sqrt_le_sqrt (hr N δ hδ0 hδ1 hN2 hN)
        _ = Real.sqrt Cr * Real.sqrt (env 0 1 δ) := Real.sqrt_mul hCr.le _
        _ ≤ Real.sqrt Cr * env 0 1 δ :=
            mul_le_mul_of_nonneg_left hs2 (Real.sqrt_nonneg _)
    · rw [← rateEnv_eq]
      exact hL N δ hδ0 hδ1 hN

/-! ### The comparisons of exponents, dimension by dimension -/

theorem cmp_r (d : ℕ) : (0 : ℝ) < rateExp d ∨ ((0 : ℝ) ≤ rateExp d ∧ 1 ≤ rateLog d) := by
  rw [rateExp, rateLog]
  split_ifs
  · left; norm_num
  · left; norm_num
  · left; norm_num
  · right; norm_num

theorem cmp_rkappa (d : ℕ) :
    kExp d < rateExp d ∨ (kExp d ≤ rateExp d ∧ 1 + kLog d ≤ rateLog d) := by
  rw [kExp, kLog, rateExp, rateLog]
  split_ifs
  · left; norm_num
  · left; norm_num
  · left; norm_num
  · right; norm_num

theorem cmp_phi (d : ℕ) :
    kExp d + pExp d < 2 * rateExp d ∨
      (kExp d + pExp d ≤ 2 * rateExp d ∧ (1 + kLog d) + pLog d ≤ 2 * rateLog d) := by
  rw [kExp, kLog, pExp, pLog, rateExp, rateLog]
  split_ifs
  · left; norm_num
  · left; norm_num
  · left; norm_num
  · right; norm_num

theorem cmp_greenL2 (d : ℕ) :
    kExp d + pExp d < 2 * rateExp d ∨
      (kExp d + pExp d ≤ 2 * rateExp d ∧ (1 + kLog d) + qLog d ≤ 2 * rateLog d) := by
  rw [kExp, kLog, pExp, qLog, rateExp, rateLog]
  split_ifs
  · left; norm_num
  · left; norm_num
  · left; norm_num
  · right; norm_num

theorem cmp_square (d : ℕ) :
    kExp d + kExp d < 2 * rateExp d ∨
      (kExp d + kExp d ≤ 2 * rateExp d ∧ (1 + kLog d) + (1 + kLog d) ≤ 2 * rateLog d) := by
  rw [kExp, kLog, rateExp, rateLog]
  split_ifs
  · left; norm_num
  · left; norm_num
  · left; norm_num
  · right; norm_num

/-! ### The five products -/

/-- `r κ_d(N)` in the scale. -/
theorem exists_rkappa_env (d : ℕ) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 → 2 ≤ N →
      ((N : ℝ) ≤ C₀ * cutoffEnv d δ) →
      rHigh N * Parking.kappa d N ≤ A * env (kExp d) (1 + kLog d) δ := by
  obtain ⟨Cr, hCr, hr⟩ := exists_rHigh_le_env d hC₀
  obtain ⟨Ck, hCk, hk⟩ := exists_kappa_le_kEnv d hC₀
  obtain ⟨A, hA, hAle⟩ := env_prod_le (α := 0) (k := 1) (β := kExp d) (l := kLog d)
    (α' := kExp d) (k' := 1 + kLog d) hCr hCk (Or.inr ⟨by linarith, le_rfl⟩)
  exact ⟨A, hA, fun N δ hδ0 hδ1 hN2 hN => hAle _ _ δ hδ0 hδ1 (rHigh_nonneg N)
    (kappa_nonneg d N) (hr N δ hδ0 hδ1 hN2 hN) (hk N δ hδ0 hδ1 hN)⟩

/-- `r max_x g_N(x)` in the same scale. -/
theorem exists_rgreenMax_env (d : ℕ) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 → 2 ≤ N →
      ((N : ℝ) ≤ C₀ * cutoffEnv d δ) →
      rHigh N * Parking.External.greenMaxRate d N ≤ A * env (kExp d) (1 + kLog d) δ := by
  obtain ⟨Cr, hCr, hr⟩ := exists_rHigh_le_env d hC₀
  obtain ⟨Ck, hCk, hk⟩ := exists_greenMaxRate_le_kEnv d hC₀
  obtain ⟨A, hA, hAle⟩ := env_prod_le (α := 0) (k := 1) (β := kExp d) (l := kLog d)
    (α' := kExp d) (k' := 1 + kLog d) hCr hCk (Or.inr ⟨by linarith, le_rfl⟩)
  exact ⟨A, hA, fun N δ hδ0 hδ1 hN2 hN => hAle _ _ δ hδ0 hδ1 (rHigh_nonneg N)
    (greenMaxRate_nonneg d N) (hr N δ hδ0 hδ1 hN2 hN) (hk N δ hδ0 hδ1 hN)⟩

/-- **The first product: `r ≤ A R`.** -/
theorem exists_prod_r (d : ℕ) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 → 2 ≤ N →
      ((N : ℝ) ≤ C₀ * cutoffEnv d δ) → rHigh N ≤ A * Parking.nearRate d δ := by
  obtain ⟨Cr, hCr, hr⟩ := exists_rHigh_le_env d hC₀
  obtain ⟨C, hC, hCle⟩ := exists_env_le_env (cmp_r d)
  refine ⟨Cr * C, by positivity, fun N δ hδ0 hδ1 hN2 hN => ?_⟩
  rw [nearRate_eq d δ]
  calc rHigh N ≤ Cr * env 0 1 δ := hr N δ hδ0 hδ1 hN2 hN
    _ ≤ Cr * (C * env (rateExp d) (rateLog d) δ) :=
        mul_le_mul_of_nonneg_left (hCle δ hδ0 hδ1) hCr.le
    _ = Cr * C * env (rateExp d) (rateLog d) δ := by ring

/-- **The second product: `r κ_d(N) ≤ A R`.** -/
theorem exists_prod_rkappa (d : ℕ) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 → 2 ≤ N →
      ((N : ℝ) ≤ C₀ * cutoffEnv d δ) →
      rHigh N * Parking.kappa d N ≤ A * Parking.nearRate d δ := by
  obtain ⟨A₁, hA₁, h₁⟩ := exists_rkappa_env d hC₀
  obtain ⟨C, hC, hCle⟩ := exists_env_le_env (cmp_rkappa d)
  refine ⟨A₁ * C, by positivity, fun N δ hδ0 hδ1 hN2 hN => ?_⟩
  rw [nearRate_eq d δ]
  calc rHigh N * Parking.kappa d N ≤ A₁ * env (kExp d) (1 + kLog d) δ :=
        h₁ N δ hδ0 hδ1 hN2 hN
    _ ≤ A₁ * (C * env (rateExp d) (rateLog d) δ) :=
        mul_le_mul_of_nonneg_left (hCle δ hδ0 hδ1) hA₁.le
    _ = A₁ * C * env (rateExp d) (rateLog d) δ := by ring

/-- **The third product: `r κ_d(N) φ_d(N) ≤ A R²`.** -/
theorem exists_prod_phi (d : ℕ) (hd : 1 ≤ d) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 → 2 ≤ N →
      ((N : ℝ) ≤ C₀ * cutoffEnv d δ) →
      rHigh N * Parking.kappa d N * Parking.phi d N ≤ A * Parking.nearRate d δ ^ 2 := by
  obtain ⟨A₁, hA₁, h₁⟩ := exists_rkappa_env d hC₀
  obtain ⟨Cp, hCp, hp⟩ := exists_phi_le_pEnv d hd hC₀
  obtain ⟨A, hA, hAle⟩ := env_prod_le (α := kExp d) (k := 1 + kLog d) (β := pExp d)
    (l := pLog d) (α' := 2 * rateExp d) (k' := 2 * rateLog d) hA₁ hCp (cmp_phi d)
  refine ⟨A, hA, fun N δ hδ0 hδ1 hN2 hN => ?_⟩
  rw [nearRate_sq_eq d hδ0]
  exact hAle _ _ δ hδ0 hδ1
    (mul_nonneg (rHigh_nonneg N) (kappa_nonneg d N)) (phi_nonneg' d N)
    (h₁ N δ hδ0 hδ1 hN2 hN) (hp N δ hδ0 hδ1 hN)

/-- **The fourth product: `r κ_d(N) (√r ‖g_N‖₂) ≤ A R²`.**  The two factors of
`√r ‖g_N‖₂` are bounded together, never separately. -/
theorem exists_prod_greenL2 (d : ℕ) (hd : 1 ≤ d) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 → 2 ≤ N →
      ((N : ℝ) ≤ C₀ * cutoffEnv d δ) →
      rHigh N * Parking.kappa d N *
          (Real.sqrt (rHigh N) * Parking.External.greenL2Rate d N)
        ≤ A * Parking.nearRate d δ ^ 2 := by
  obtain ⟨A₁, hA₁, h₁⟩ := exists_rkappa_env d hC₀
  obtain ⟨Cq, hCq, hq⟩ := exists_sqrtRHigh_greenL2_le d hd hC₀
  obtain ⟨A, hA, hAle⟩ := env_prod_le (α := kExp d) (k := 1 + kLog d) (β := pExp d)
    (l := qLog d) (α' := 2 * rateExp d) (k' := 2 * rateLog d) hA₁ hCq (cmp_greenL2 d)
  refine ⟨A, hA, fun N δ hδ0 hδ1 hN2 hN => ?_⟩
  rw [nearRate_sq_eq d hδ0]
  exact hAle _ _ δ hδ0 hδ1
    (mul_nonneg (rHigh_nonneg N) (kappa_nonneg d N))
    (mul_nonneg (Real.sqrt_nonneg _) (greenL2Rate_nonneg d N))
    (h₁ N δ hδ0 hδ1 hN2 hN) (hq N δ hδ0 hδ1 hN2 hN)

/-- **The fifth product: `r κ_d(N) (r max_x g_N(x)) ≤ A R²`.** -/
theorem exists_prod_greenMax (d : ℕ) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 → 2 ≤ N →
      ((N : ℝ) ≤ C₀ * cutoffEnv d δ) →
      rHigh N * Parking.kappa d N *
          (rHigh N * Parking.External.greenMaxRate d N)
        ≤ A * Parking.nearRate d δ ^ 2 := by
  obtain ⟨A₁, hA₁, h₁⟩ := exists_rkappa_env d hC₀
  obtain ⟨A₂, hA₂, h₂⟩ := exists_rgreenMax_env d hC₀
  obtain ⟨A, hA, hAle⟩ := env_prod_le (α := kExp d) (k := 1 + kLog d) (β := kExp d)
    (l := 1 + kLog d) (α' := 2 * rateExp d) (k' := 2 * rateLog d) hA₁ hA₂ (cmp_square d)
  refine ⟨A, hA, fun N δ hδ0 hδ1 hN2 hN => ?_⟩
  rw [nearRate_sq_eq d hδ0]
  exact hAle _ _ δ hδ0 hδ1
    (mul_nonneg (rHigh_nonneg N) (kappa_nonneg d N))
    (mul_nonneg (rHigh_nonneg N) (greenMaxRate_nonneg d N))
    (h₁ N δ hδ0 hδ1 hN2 hN) (h₂ N δ hδ0 hδ1 hN2 hN)

/-- The square of the second product, `(r κ_d(N))² ≤ A R²`. -/
theorem exists_prod_rkappa_sq (d : ℕ) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 → 2 ≤ N →
      ((N : ℝ) ≤ C₀ * cutoffEnv d δ) →
      (rHigh N * Parking.kappa d N) * (rHigh N * Parking.kappa d N)
        ≤ A * Parking.nearRate d δ ^ 2 := by
  obtain ⟨A₁, hA₁, h₁⟩ := exists_rkappa_env d hC₀
  obtain ⟨A, hA, hAle⟩ := env_prod_le (α := kExp d) (k := 1 + kLog d) (β := kExp d)
    (l := 1 + kLog d) (α' := 2 * rateExp d) (k' := 2 * rateLog d) hA₁ hA₁ (cmp_square d)
  refine ⟨A, hA, fun N δ hδ0 hδ1 hN2 hN => ?_⟩
  rw [nearRate_sq_eq d hδ0]
  exact hAle _ _ δ hδ0 hδ1
    (mul_nonneg (rHigh_nonneg N) (kappa_nonneg d N))
    (mul_nonneg (rHigh_nonneg N) (kappa_nonneg d N))
    (h₁ N δ hδ0 hδ1 hN2 hN) (h₁ N δ hδ0 hδ1 hN2 hN)

end Parking
end
