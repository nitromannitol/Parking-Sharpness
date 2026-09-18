/-
The quantities of Step 3 of the upper bounds of `thm:near`, read at the cutoff in the
scale `env` (`parking.tex:2944-2978`).

"Take `r = 2 ∨ ⌈log(N+1)⌉`.  Then `r ≍ L` and both `(N+1)^{1/r}` and `(N+1)^{2/r}` are
bounded.  Since `κ_1(N) = √N`, `κ_2(N) = log(N+2)` and `κ_d(N) = 1` for `d ≥ 3` …"

Each of the five quantities read at the cutoff is either a power `N^β` with
`0 ≤ β ≤ 1` or a logarithm of `N`, so the two comparisons of
`Parking/Support/NearScale.lean` place each of them in the scale: the exponent of `1/δ`
is multiplied by `β`, and a logarithm becomes a constant multiple of `log(e/δ)`.  The
resulting scales are `env 2 3` or `log(e/δ)` for `κ_d` and for the maximum of the Green
function, and `env 3 3`, `env 1 3`, `env (1/2) 2` or `log(e/δ)` for `φ_d` and for the
`L²` norm of the Green function, in dimensions one, two, three and four upward.
-/
import Parking.Support.NearScale
import Parking.Support.NearCutoff
import Parking.External.GreenNorms
import Parking.Support.UpperTarget

noncomputable section
namespace Parking

/-- The scale in which the Green quantities and the two rates are read at the cutoff. -/
def rateEnv (d : ℕ) (δ : ℝ) : ℝ :=
  if d = 1 then env 3 3 δ else if d = 2 then env 1 3 δ
  else if d = 3 then env (1 / 2) 2 δ else env 0 1 δ

/-- The scale in which `κ_d` and the maximum of the Green function are read. -/
def kappaEnv (d : ℕ) (δ : ℝ) : ℝ := if d = 1 then env 2 3 δ else env 0 1 δ

theorem exists_kappa_le_env (d : ℕ) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ((N : ℝ) ≤ C₀ * cutoffEnv d δ) → Parking.kappa d N ≤ C * kappaEnv d δ := by
  by_cases h1 : d = 1
  · refine ⟨max 1 C₀, lt_of_lt_of_le one_pos (le_max_left _ _), fun N δ hδ0 hδ1 hN => ?_⟩
    rw [Parking.kappa, if_pos h1, kappaEnv, if_pos h1]
    have h := rpow_le_env (α := 4) (β := (1 : ℝ) / 2) (k := 3) (x := (N : ℝ)) (δ := δ)
      hC₀ (by norm_num) (by norm_num) hδ0 hδ1 (Nat.cast_nonneg N)
      (by rw [cutoffEnv, if_pos h1] at hN; exact hN)
    have he : (4 : ℝ) * ((1 : ℝ) / 2) = 2 := by norm_num
    rwa [he] at h
  by_cases h2 : d = 2
  · obtain ⟨C, hC, hCle⟩ := exists_log_le_env (α := 2) (k := 3) (C₀ := C₀) (c := 2) hC₀
      (by norm_num) (by norm_num)
    refine ⟨C, hC, fun N δ hδ0 hδ1 hN => ?_⟩
    rw [Parking.kappa, if_neg h1, if_pos h2, kappaEnv, if_neg h1]
    exact hCle (N : ℝ) δ hδ0 hδ1 (Nat.cast_nonneg N)
      (by rw [cutoffEnv, if_neg h1, if_pos h2] at hN; exact hN)
  · refine ⟨1, one_pos, fun N δ hδ0 hδ1 hN => ?_⟩
    rw [Parking.kappa, if_neg h1, if_neg h2, kappaEnv, if_neg h1, one_mul, env_log δ]
    exact one_le_bigL hδ0 hδ1

theorem exists_greenMaxRate_le_env (d : ℕ) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ((N : ℝ) ≤ C₀ * cutoffEnv d δ) →
      Parking.External.greenMaxRate d N ≤ C * kappaEnv d δ := by
  by_cases h1 : d = 1
  · refine ⟨max 1 C₀, lt_of_lt_of_le one_pos (le_max_left _ _), fun N δ hδ0 hδ1 hN => ?_⟩
    rw [Parking.External.greenMaxRate, if_pos h1, kappaEnv, if_pos h1]
    have h := rpow_le_env (α := 4) (β := (1 : ℝ) / 2) (k := 3) (x := (N : ℝ)) (δ := δ)
      hC₀ (by norm_num) (by norm_num) hδ0 hδ1 (Nat.cast_nonneg N)
      (by rw [cutoffEnv, if_pos h1] at hN; exact hN)
    have he : (4 : ℝ) * ((1 : ℝ) / 2) = 2 := by norm_num
    rwa [he] at h
  by_cases h2 : d = 2
  · obtain ⟨C, hC, hCle⟩ := exists_log_le_env (α := 2) (k := 3) (C₀ := C₀) (c := 0) hC₀
      (by norm_num) (le_refl 0)
    refine ⟨C, hC, fun N δ hδ0 hδ1 hN => ?_⟩
    rw [Parking.External.greenMaxRate, if_neg h1, if_pos h2, kappaEnv, if_neg h1,
      show Real.log (N : ℝ) = Real.log ((N : ℝ) + 0) by rw [add_zero]]
    exact hCle (N : ℝ) δ hδ0 hδ1 (Nat.cast_nonneg N)
      (by rw [cutoffEnv, if_neg h1, if_pos h2] at hN; exact hN)
  · refine ⟨1, one_pos, fun N δ hδ0 hδ1 hN => ?_⟩
    rw [Parking.External.greenMaxRate, if_neg h1, if_neg h2, kappaEnv, if_neg h1, one_mul,
      env_log δ]
    exact one_le_bigL hδ0 hδ1

theorem exists_phi_le_env (d : ℕ) (hd : 1 ≤ d) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ((N : ℝ) ≤ C₀ * cutoffEnv d δ) → Parking.phi d N ≤ C * rateEnv d δ := by
  by_cases h1 : d = 1
  · subst h1
    refine ⟨max 1 (C₀ + 1), lt_of_lt_of_le one_pos (le_max_left _ _),
      fun N δ hδ0 hδ1 hN => ?_⟩
    have hE1 : 1 ≤ cutoffEnv 1 δ := one_le_cutoffEnv 1 hδ0 hδ1
    have hN1 : (N : ℝ) + 1 ≤ (C₀ + 1) * env 4 3 δ := by
      rw [cutoffEnv, if_pos rfl] at hN hE1; nlinarith
    have h := rpow_le_env (α := 4) (β := (3 : ℝ) / 4) (k := 3) (x := (N : ℝ) + 1) (δ := δ)
      (by linarith : (0 : ℝ) < C₀ + 1) (by norm_num) (by norm_num) hδ0 hδ1
      (by positivity) hN1
    rw [Parking.phi, if_pos (by norm_num), rateEnv, if_pos rfl]
    have he : (4 : ℝ) * ((3 : ℝ) / 4) = 3 := by norm_num
    rw [he] at h
    have hexp : (4 - ((1 : ℕ) : ℝ)) / 4 = (3 : ℝ) / 4 := by norm_num
    rwa [hexp]
  by_cases h2 : d = 2
  · subst h2
    refine ⟨max 1 (C₀ + 1), lt_of_lt_of_le one_pos (le_max_left _ _),
      fun N δ hδ0 hδ1 hN => ?_⟩
    have hE1 : 1 ≤ cutoffEnv 2 δ := one_le_cutoffEnv 2 hδ0 hδ1
    have hN1 : (N : ℝ) + 1 ≤ (C₀ + 1) * env 2 3 δ := by
      rw [cutoffEnv, if_neg (by norm_num), if_pos rfl] at hN hE1; nlinarith
    have h := rpow_le_env (α := 2) (β := (1 : ℝ) / 2) (k := 3) (x := (N : ℝ) + 1) (δ := δ)
      (by linarith : (0 : ℝ) < C₀ + 1) (by norm_num) (by norm_num) hδ0 hδ1
      (by positivity) hN1
    rw [Parking.phi, if_pos (by norm_num), rateEnv, if_neg (by norm_num), if_pos rfl]
    have he : (2 : ℝ) * ((1 : ℝ) / 2) = 1 := by norm_num
    rw [he] at h
    have hexp : (4 - ((2 : ℕ) : ℝ)) / 4 = (1 : ℝ) / 2 := by norm_num
    rwa [hexp]
  by_cases h3 : d = 3
  · subst h3
    refine ⟨max 1 (C₀ + 1), lt_of_lt_of_le one_pos (le_max_left _ _),
      fun N δ hδ0 hδ1 hN => ?_⟩
    have hE1 : 1 ≤ cutoffEnv 3 δ := one_le_cutoffEnv 3 hδ0 hδ1
    have hN1 : (N : ℝ) + 1 ≤ (C₀ + 1) * env 2 2 δ := by
      rw [cutoffEnv, if_neg (by norm_num), if_neg (by norm_num)] at hN hE1; nlinarith
    have h := rpow_le_env (α := 2) (β := (1 : ℝ) / 4) (k := 2) (x := (N : ℝ) + 1) (δ := δ)
      (by linarith : (0 : ℝ) < C₀ + 1) (by norm_num) (by norm_num) hδ0 hδ1
      (by positivity) hN1
    rw [Parking.phi, if_pos (by norm_num), rateEnv, if_neg (by norm_num),
      if_neg (by norm_num), if_pos rfl]
    have he : (2 : ℝ) * ((1 : ℝ) / 4) = 1 / 2 := by norm_num
    rw [he] at h
    have hexp : (4 - ((3 : ℕ) : ℝ)) / 4 = (1 : ℝ) / 4 := by norm_num
    rwa [hexp]
  · obtain ⟨C, hC, hCle⟩ := exists_log_le_env (α := 2) (k := 2) (C₀ := C₀) (c := 2) hC₀
      (by norm_num) (by norm_num)
    refine ⟨C, hC, fun N δ hδ0 hδ1 hN => ?_⟩
    rw [Parking.phi, if_neg (by omega : ¬ d ≤ 3), rateEnv, if_neg h1, if_neg h2, if_neg h3]
    exact hCle (N : ℝ) δ hδ0 hδ1 (Nat.cast_nonneg N)
      (by rw [cutoffEnv, if_neg h1, if_neg h2] at hN; exact hN)

theorem exists_greenL2Rate_le_env (d : ℕ) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ((N : ℝ) ≤ C₀ * cutoffEnv d δ) →
      Parking.External.greenL2Rate d N ≤ C * rateEnv d δ := by
  by_cases h1 : d = 1
  · subst h1
    refine ⟨max 1 C₀, lt_of_lt_of_le one_pos (le_max_left _ _), fun N δ hδ0 hδ1 hN => ?_⟩
    rw [Parking.External.greenL2Rate, if_pos rfl, rateEnv, if_pos rfl]
    have h := rpow_le_env (α := 4) (β := (3 : ℝ) / 4) (k := 3) (x := (N : ℝ)) (δ := δ)
      hC₀ (by norm_num) (by norm_num) hδ0 hδ1 (Nat.cast_nonneg N)
      (by rw [cutoffEnv, if_pos rfl] at hN; exact hN)
    have he : (4 : ℝ) * ((3 : ℝ) / 4) = 3 := by norm_num
    rwa [he] at h
  by_cases h2 : d = 2
  · subst h2
    refine ⟨max 1 C₀, lt_of_lt_of_le one_pos (le_max_left _ _), fun N δ hδ0 hδ1 hN => ?_⟩
    rw [Parking.External.greenL2Rate, if_neg (by norm_num), if_pos rfl, rateEnv,
      if_neg (by norm_num), if_pos rfl]
    have h := rpow_le_env (α := 2) (β := (1 : ℝ) / 2) (k := 3) (x := (N : ℝ)) (δ := δ)
      hC₀ (by norm_num) (by norm_num) hδ0 hδ1 (Nat.cast_nonneg N)
      (by rw [cutoffEnv, if_neg (by norm_num), if_pos rfl] at hN; exact hN)
    have he : (2 : ℝ) * ((1 : ℝ) / 2) = 1 := by norm_num
    rwa [he] at h
  by_cases h3 : d = 3
  · subst h3
    refine ⟨max 1 C₀, lt_of_lt_of_le one_pos (le_max_left _ _), fun N δ hδ0 hδ1 hN => ?_⟩
    rw [Parking.External.greenL2Rate, if_neg (by norm_num), if_neg (by norm_num),
      if_pos rfl, rateEnv, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
    have h := rpow_le_env (α := 2) (β := (1 : ℝ) / 4) (k := 2) (x := (N : ℝ)) (δ := δ)
      hC₀ (by norm_num) (by norm_num) hδ0 hδ1 (Nat.cast_nonneg N)
      (by rw [cutoffEnv, if_neg (by norm_num), if_neg (by norm_num)] at hN; exact hN)
    have he : (2 : ℝ) * ((1 : ℝ) / 4) = 1 / 2 := by norm_num
    rwa [he] at h
  by_cases h4 : d = 4
  · obtain ⟨C, hC, hCle⟩ := exists_log_le_env (α := 2) (k := 2) (C₀ := C₀) (c := 0) hC₀
      (by norm_num) (le_refl 0)
    refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, fun N δ hδ0 hδ1 hN => ?_⟩
    have hL := one_le_bigL hδ0 hδ1
    have hlog : Real.log (N : ℝ) ≤ C * Real.log (Real.exp 1 / δ) := by
      have h := hCle (N : ℝ) δ hδ0 hδ1 (Nat.cast_nonneg N)
        (by rw [cutoffEnv, if_neg h1, if_neg h2] at hN; exact hN)
      rwa [add_zero, env_log δ] at h
    rw [Parking.External.greenL2Rate, if_neg h1, if_neg h2, if_neg h3, if_pos h4,
      rateEnv, if_neg h1, if_neg h2, if_neg h3, env_log δ]
    calc Real.sqrt (Real.log (N : ℝ))
        ≤ Real.sqrt (C * Real.log (Real.exp 1 / δ)) := Real.sqrt_le_sqrt hlog
      _ = Real.sqrt C * Real.sqrt (Real.log (Real.exp 1 / δ)) :=
          Real.sqrt_mul hC.le _
      _ ≤ Real.sqrt C * Real.log (Real.exp 1 / δ) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg C)
          have hsq : Real.log (Real.exp 1 / δ) ≤ Real.log (Real.exp 1 / δ) ^ 2 := by
            nlinarith
          calc Real.sqrt (Real.log (Real.exp 1 / δ))
              ≤ Real.sqrt (Real.log (Real.exp 1 / δ) ^ 2) := Real.sqrt_le_sqrt hsq
            _ = Real.log (Real.exp 1 / δ) := Real.sqrt_sq (by linarith)
  · refine ⟨1, one_pos, fun N δ hδ0 hδ1 hN => ?_⟩
    rw [Parking.External.greenL2Rate, if_neg h1, if_neg h2, if_neg h3, if_neg h4,
      rateEnv, if_neg h1, if_neg h2, if_neg h3, one_mul, env_log δ]
    exact one_le_bigL hδ0 hδ1

theorem resolventThreshold_pos (d : ℕ) {CR a : ℝ} (hCR : 0 < CR) (ha : 0 < a)
    (ha1 : a ≤ 1) : 0 < Parking.resolventThreshold d CR a := by
  have hΛ : 1 ≤ Real.log (Real.exp 1 / a) := one_le_bigL ha ha1
  have hr : (0 : ℝ) < a ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos ha _
  have hi : (0 : ℝ) < a⁻¹ := inv_pos.mpr ha
  rw [Parking.resolventThreshold]
  split_ifs
  · exact mul_pos hCR (mul_pos hr (pow_pos (by linarith) 3))
  · exact mul_pos hCR (mul_pos hi (pow_pos (by linarith) 3))
  · exact mul_pos hCR (mul_pos hi (pow_pos (by linarith) 2))

theorem two_le_nearCutoff (d : ℕ) {CR a δ : ℝ}
    (h : 0 < Parking.resolventThreshold d CR (a * δ ^ 2)) : 2 ≤ nearCutoff d CR a δ := by
  have h1 : 0 < ⌈Parking.resolventThreshold d CR (a * δ ^ 2)⌉₊ := Nat.ceil_pos.mpr h
  rw [nearCutoff]
  omega

/-- The exponent `r = 2 ∨ ⌈log(N+1)⌉` of Step 3 is of the order of `log(e/δ)` at the
cutoff. -/
theorem exists_rHigh_le_env (d : ℕ) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 → 2 ≤ N →
      ((N : ℝ) ≤ C₀ * cutoffEnv d δ) → rHigh N ≤ C * env 0 1 δ := by
  have main : ∀ (α : ℝ) (k : ℕ), 0 ≤ α →
      (∀ δ : ℝ, 0 < δ → δ ≤ 1 → cutoffEnv d δ = env α k δ) →
      ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 → 2 ≤ N →
        ((N : ℝ) ≤ C₀ * cutoffEnv d δ) → rHigh N ≤ C * env 0 1 δ := by
    intro α k hα hEq
    obtain ⟨C, hC, hCle⟩ := exists_log_le_env (α := α) (k := k) (C₀ := C₀) (c := 0) hC₀ hα
      (le_refl 0)
    refine ⟨rConst * C, mul_pos rConst_pos hC, fun N δ hδ0 hδ1 hN2 hN => ?_⟩
    have hlog : Real.log (N : ℝ) ≤ C * env 0 1 δ := by
      have h := hCle (N : ℝ) δ hδ0 hδ1 (Nat.cast_nonneg N) (by rw [← hEq δ hδ0 hδ1]; exact hN)
      rwa [add_zero] at h
    have hstep : rHigh N ≤ rConst * Real.log N := rHigh_le_log hN2
    have hE0 : (0 : ℝ) ≤ env 0 1 δ := (env_pos hδ0 hδ1).le
    nlinarith [hstep, hlog, rConst_pos]
  by_cases h1 : d = 1
  · exact main 4 3 (by norm_num) (fun δ _ _ => by rw [cutoffEnv, if_pos h1])
  by_cases h2 : d = 2
  · exact main 2 3 (by norm_num) (fun δ _ _ => by rw [cutoffEnv, if_neg h1, if_pos h2])
  · exact main 2 2 (by norm_num) (fun δ _ _ => by rw [cutoffEnv, if_neg h1, if_neg h2])

/-- **From dimension four on the `L²` Green rate is of the order of the square root of
the logarithm**, which is what makes `√r ‖g_N‖₂` of the order of `log(e/δ)` there rather
than of a higher power of it. -/
theorem exists_greenL2Rate_sqrt_le (d : ℕ) (hd4 : 4 ≤ d) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ((N : ℝ) ≤ C₀ * cutoffEnv d δ) →
      Parking.External.greenL2Rate d N ≤ C * Real.sqrt (env 0 1 δ) := by
  have h1 : ¬ d = 1 := by omega
  have h2 : ¬ d = 2 := by omega
  have h3 : ¬ d = 3 := by omega
  obtain ⟨C, hC, hCle⟩ := exists_log_le_env (α := 2) (k := 2) (C₀ := C₀) (c := 0) hC₀
    (by norm_num) (le_refl 0)
  refine ⟨Real.sqrt C + 1, by positivity, fun N δ hδ0 hδ1 hN => ?_⟩
  have hL := one_le_bigL hδ0 hδ1
  have hEL : env 0 1 δ = Real.log (Real.exp 1 / δ) := env_log δ
  have hsq1 : 1 ≤ Real.sqrt (env 0 1 δ) := by
    rw [hEL]
    have h := Real.sqrt_le_sqrt hL
    rwa [Real.sqrt_one] at h
  have hsq0 : (0 : ℝ) ≤ Real.sqrt (env 0 1 δ) := le_trans zero_le_one hsq1
  by_cases h4 : d = 4
  · have hlog : Real.log (N : ℝ) ≤ C * env 0 1 δ := by
      have h := hCle (N : ℝ) δ hδ0 hδ1 (Nat.cast_nonneg N)
        (by rw [cutoffEnv, if_neg h1, if_neg h2] at hN; exact hN)
      rwa [add_zero] at h
    rw [Parking.External.greenL2Rate, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
    calc Real.sqrt (Real.log (N : ℝ)) ≤ Real.sqrt (C * env 0 1 δ) := Real.sqrt_le_sqrt hlog
      _ = Real.sqrt C * Real.sqrt (env 0 1 δ) := Real.sqrt_mul hC.le _
      _ ≤ (Real.sqrt C + 1) * Real.sqrt (env 0 1 δ) := by nlinarith
  · rw [Parking.External.greenL2Rate, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
    nlinarith [hsq1, Real.sqrt_nonneg C]


end Parking
end
