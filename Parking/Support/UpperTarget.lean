/-
Steps 2 and 3 of the proof of `thm:upper` (`parking.tex:1444-1460`), and the
first display `eq:target`.

Step 1 leaves the moment bound

    (E U_n(0)^r)^{1/r} ≤ C (E u_n(0) + √r ‖g_n‖₂ + r max_x g_n(x)
                              + r (n+1)^{2/r} κ_d(n)).

Below dimension four the paper takes `r = 8`, where `eq:green-norms` makes the
two Green terms and the last term of the order of `‖g_n‖₂`, which `thm:BP`
bounds by `E u_n(0)`.  From dimension four on it takes
`r = 2 ∨ ⌈log(n+1)⌉`, where `(n+1)^{2/r} ≤ e²` and `κ_d(n) = 1`, and every
term is of the order of `log n`.

The elementary comparisons the two steps rest on are collected first:
`x^{2/r} ≤ e²` when `log x ≤ r`, `log(n+1) ≤ 2 log n` and `log(n+2) ≤ 2 log n`
for `n ≥ 2`, `log n ≤ n^ε/ε`, and `(n+1)^t ≤ 2^t n^t`.
-/
import Parking.Support.CriticalLawReal
import Parking.External.GreenNorms

noncomputable section

namespace Parking

open MeasureTheory ProbabilityTheory LatticeProb

variable {d : ℕ}

/-! ### Elementary comparisons -/

theorem rpow_two_div_le_exp_two {x r : ℝ} (hx : 1 ≤ x) (hr : 0 < r)
    (hlog : Real.log x ≤ r) : x ^ (2 / r) ≤ Real.exp 2 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  rw [Real.rpow_def_of_pos hx0 (2 / r)]
  refine Real.exp_le_exp.mpr ?_
  have hnn : 0 ≤ Real.log x := Real.log_nonneg hx
  rw [mul_div_assoc']
  exact (div_le_iff₀ hr).mpr (by linarith)

theorem log_succ_le_two_mul_log {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((n : ℝ) + 1) ≤ 2 * Real.log n := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq : (n : ℝ) + 1 ≤ (n : ℝ) ^ 2 := by nlinarith
  calc Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) ^ 2) :=
      Real.log_le_log (by linarith) hsq
    _ = 2 * Real.log (n : ℝ) := by rw [Real.log_pow]; norm_num

theorem log_add_two_le_two_mul_log {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  calc Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) ^ 2) :=
      Real.log_le_log (by linarith) hsq
    _ = 2 * Real.log (n : ℝ) := by rw [Real.log_pow]; norm_num

theorem log_le_four_rpow_quarter (n : ℕ) : Real.log n ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
  calc Real.log n ≤ (n : ℝ) ^ ((1 : ℝ) / 4) / (1 / 4) :=
        Real.log_le_rpow_div (Nat.cast_nonneg n) (by norm_num)
    _ = 4 * (n : ℝ) ^ ((1 : ℝ) / 4) := by ring

theorem log_le_two_rpow_half (n : ℕ) : Real.log n ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 2) := by
  calc Real.log n ≤ (n : ℝ) ^ ((1 : ℝ) / 2) / (1 / 2) :=
        Real.log_le_rpow_div (Nat.cast_nonneg n) (by norm_num)
    _ = 2 * (n : ℝ) ^ ((1 : ℝ) / 2) := by ring

theorem rpow_succ_le_two_rpow {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    ((n : ℝ) + 1) ^ t ≤ 2 ^ t * (n : ℝ) ^ t := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hle : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
  calc ((n : ℝ) + 1) ^ t ≤ (2 * (n : ℝ)) ^ t :=
        Real.rpow_le_rpow (by linarith) hle ht
    _ = 2 ^ t * (n : ℝ) ^ t := Real.mul_rpow (by norm_num) (by linarith)

theorem log_two_le_log {n : ℕ} (hn : 2 ≤ n) : Real.log 2 ≤ Real.log n := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact Real.log_le_log (by norm_num) hn2

theorem log_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

theorem log_pos_of_two_le {n : ℕ} (hn : 2 ≤ n) : (0 : ℝ) < Real.log n :=
  lt_of_lt_of_le log_two_pos (log_two_le_log hn)

/-! ### Jensen: the mean against the `r`-th moment norm -/

theorem integral_le_rNorm {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) (hfi : Integrable f μ)
    {r : ℝ} (hr : 1 ≤ r) (hgi : Integrable (fun ω => f ω ^ r) μ) :
    ∫ ω, f ω ∂μ ≤ (∫ ω, f ω ^ r ∂μ) ^ (1 / r) := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hI0 : (0 : ℝ) ≤ ∫ ω, f ω ∂μ := integral_nonneg hf
  have hJ := rpow_integral_le hf hfi hr hgi
  have hmono : ((∫ ω, f ω ∂μ) ^ r) ^ (1 / r) ≤ (∫ ω, f ω ^ r ∂μ) ^ (1 / r) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hI0 r) hJ (by positivity)
  rwa [← Real.rpow_mul hI0, mul_one_div_cancel (ne_of_gt hr0), Real.rpow_one] at hmono

/-! ### Step 2: the error terms below dimension four -/

theorem greenL2Rate_eq_low {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) (n : ℕ) :
    Parking.External.greenL2Rate d n = (n : ℝ) ^ ((4 - (d : ℝ)) / 4) := by
  interval_cases d <;> · rw [Parking.External.greenL2Rate]; norm_num

theorem greenMaxRate_le_greenL2Rate {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) {n : ℕ} (hn : 2 ≤ n) :
    Parking.External.greenMaxRate d n ≤ 2 * Parking.External.greenL2Rate d n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  interval_cases d
  · -- d = 1: n^{1/2} ≤ 2 n^{3/4}
    rw [Parking.External.greenMaxRate, Parking.External.greenL2Rate]
    norm_num
    have h : (n : ℝ) ^ ((1 : ℝ) / 2) ≤ (n : ℝ) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    have h0 : (0 : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
    linarith
  · -- d = 2: log n ≤ 2 n^{1/2}
    rw [Parking.External.greenMaxRate, Parking.External.greenL2Rate]
    norm_num
    exact log_le_two_rpow_half n
  · -- d = 3: 1 ≤ 2 n^{1/4}
    rw [Parking.External.greenMaxRate, Parking.External.greenL2Rate]
    norm_num
    have h : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := Real.one_le_rpow hn1 (by norm_num)
    linarith

theorem kappa_term_le_greenL2Rate {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) {n : ℕ} (hn : 2 ≤ n) :
    ((n : ℝ) + 1) ^ ((1 : ℝ) / 4) * kappa d n
      ≤ 32 * Parking.External.greenL2Rate d n := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hE : ((n : ℝ) + 1) ^ ((1 : ℝ) / 4) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
    refine (rpow_succ_le_two_rpow (le_trans one_le_two hn) (by norm_num)).trans ?_
    have h2 : (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
        (show (1 : ℝ) / 4 ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    have h0 : (0 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
    nlinarith
  have hq0 : (0 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
  have hE0 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
  interval_cases d
  · -- d = 1: κ = n^{1/2}, rate = n^{3/4}
    rw [Parking.External.greenL2Rate, kappa]
    norm_num
    have hmul : (n : ℝ) ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 2)
        = (n : ℝ) ^ ((3 : ℝ) / 4) := by
      rw [← Real.rpow_add hn0]; norm_num
    have hk0 : (0 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
    calc ((n : ℝ) + 1) ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 2)
        ≤ (2 * (n : ℝ) ^ ((1 : ℝ) / 4)) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
          exact mul_le_mul_of_nonneg_right hE hk0
      _ = 2 * (n : ℝ) ^ ((3 : ℝ) / 4) := by rw [mul_assoc, hmul]
      _ ≤ 32 * (n : ℝ) ^ ((3 : ℝ) / 4) := by
          have : (0 : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
          linarith
  · -- d = 2: κ = log(n+2), rate = n^{1/2}
    rw [Parking.External.greenL2Rate, kappa]
    norm_num
    have hk : Real.log ((n : ℝ) + 2) ≤ 8 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
      refine (log_add_two_le_two_mul_log hn).trans ?_
      have := log_le_four_rpow_quarter n
      linarith
    have hk0 : (0 : ℝ) ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_nonneg (by linarith)
    have hmul : (n : ℝ) ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4)
        = (n : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hn0]; norm_num
    calc ((n : ℝ) + 1) ^ ((1 : ℝ) / 4) * Real.log ((n : ℝ) + 2)
        ≤ (2 * (n : ℝ) ^ ((1 : ℝ) / 4)) * (8 * (n : ℝ) ^ ((1 : ℝ) / 4)) := by
          exact mul_le_mul hE hk hk0 (by linarith)
      _ = 16 * (n : ℝ) ^ ((1 : ℝ) / 2) := by rw [show (2 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4)
            * (8 * (n : ℝ) ^ ((1 : ℝ) / 4))
            = 16 * ((n : ℝ) ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4)) by ring, hmul]
      _ ≤ 32 * (n : ℝ) ^ ((1 : ℝ) / 2) := by
          have : (0 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
          linarith
  · -- d = 3: κ = 1, rate = n^{1/4}
    rw [Parking.External.greenL2Rate, kappa]
    norm_num
    linarith

/-! ### Step 3: the exponent the paper takes from dimension four on -/

/-- `r = 2 ∨ ⌈log(n+1)⌉`, the exponent of Step 3. -/
def rHigh (n : ℕ) : ℝ := max 2 ((Nat.ceil (Real.log ((n : ℝ) + 1)) : ℕ) : ℝ)

theorem two_le_rHigh (n : ℕ) : 2 ≤ rHigh n := le_max_left _ _

theorem rHigh_pos (n : ℕ) : 0 < rHigh n := lt_of_lt_of_le (by norm_num) (two_le_rHigh n)

theorem log_le_rHigh (n : ℕ) : Real.log ((n : ℝ) + 1) ≤ rHigh n :=
  le_trans (Nat.le_ceil _) (le_max_right _ _)

/-- The constant of Step 3: `r ≤ (2/log 2 + 2) log n` for `n ≥ 2`. -/
def rConst : ℝ := 2 / Real.log 2 + 2

theorem rConst_pos : 0 < rConst := by
  rw [rConst]
  have := log_two_pos
  positivity

theorem rHigh_le_log {n : ℕ} (hn : 2 ≤ n) : rHigh n ≤ rConst * Real.log n := by
  have hlogpos := log_pos_of_two_le hn
  have hlognn : (0 : ℝ) ≤ Real.log ((n : ℝ) + 1) := by
    refine Real.log_nonneg ?_
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hceil : ((Nat.ceil (Real.log ((n : ℝ) + 1)) : ℕ) : ℝ)
      ≤ Real.log ((n : ℝ) + 1) + 1 := le_of_lt (Nat.ceil_lt_add_one hlognn)
  have hmax : rHigh n ≤ 2 + Real.log ((n : ℝ) + 1) := by
    rw [rHigh]
    exact max_le (by linarith) (by linarith)
  have hlog1 : Real.log ((n : ℝ) + 1) ≤ 2 * Real.log n := log_succ_le_two_mul_log hn
  have htwo : (2 : ℝ) ≤ (2 / Real.log 2) * Real.log n := by
    rw [div_mul_eq_mul_div, le_div_iff₀ log_two_pos]
    have := log_two_le_log hn
    nlinarith
  rw [rConst]
  nlinarith

/-! ### The two error bounds -/

theorem upper_error_low {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGN : Parking.External.GreenNorms) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 2 ≤ n →
      Real.sqrt 8 * l2Norm (green d n) + 8 * greenMax d n
          + 8 * (((n : ℝ) + 1) ^ ((2 : ℝ) / 8)) * kappa d n
        ≤ K * (n : ℝ) ^ ((4 - (d : ℝ)) / 4) := by
  obtain ⟨⟨cL, CL, hcL, hCL, hLbd⟩, ⟨cM, CM, hcM, hCM, hMbd⟩⟩ := hGN d hd
  refine ⟨3 * CL + 16 * CM + 256, by positivity, fun n hn => ?_⟩
  have hrate0 : (0 : ℝ) ≤ Parking.External.greenL2Rate d n := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [Parking.External.greenL2Rate]
    split_ifs <;> first
      | exact Real.rpow_nonneg hn0 _
      | exact Real.sqrt_nonneg _
      | norm_num
  have hL := (hLbd n hn).2
  have hM := (hMbd n hn).2
  have hMr := greenMaxRate_le_greenL2Rate hd hd3 hn
  have hK := kappa_term_le_greenL2Rate hd hd3 hn
  have hexp : ((2 : ℝ) / 8) = (1 : ℝ) / 4 := by norm_num
  rw [hexp]
  have hsqrt8 : Real.sqrt 8 ≤ 3 := by
    rw [show (8 : ℝ) = 3 ^ 2 - 1 by norm_num]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 ^ 2 - 1 by norm_num),
      Real.sqrt_nonneg ((3 : ℝ) ^ 2 - 1)]
  have hL0 : (0 : ℝ) ≤ l2Norm (green d n) := Real.sqrt_nonneg _
  have hM0 : (0 : ℝ) ≤ greenMax d n := Real.iSup_nonneg fun x => green_nonneg n x
  have hMrate : greenMax d n ≤ 2 * CM * Parking.External.greenL2Rate d n := by
    refine hM.trans ?_
    calc CM * Parking.External.greenMaxRate d n
        ≤ CM * (2 * Parking.External.greenL2Rate d n) :=
          mul_le_mul_of_nonneg_left hMr (le_of_lt hCM)
      _ = 2 * CM * Parking.External.greenL2Rate d n := by ring
  rw [← greenL2Rate_eq_low hd hd3 n]
  nlinarith [hL, hK, hMrate, hL0, hM0, hrate0, hsqrt8, hcL.le, hcM.le]

theorem greenL2Rate_le_high {d : ℕ} (hd4 : 4 ≤ d) (n : ℕ) :
    Parking.External.greenL2Rate d n ≤ 1 + Real.sqrt (Real.log n) := by
  have hs : (0 : ℝ) ≤ Real.sqrt (Real.log n) := Real.sqrt_nonneg _
  rw [Parking.External.greenL2Rate]
  have h1 : d ≠ 1 := by omega
  have h2 : d ≠ 2 := by omega
  have h3 : d ≠ 3 := by omega
  rw [if_neg h1, if_neg h2, if_neg h3]
  split_ifs with h4
  · linarith
  · linarith

theorem greenMaxRate_high {d : ℕ} (hd4 : 4 ≤ d) (n : ℕ) :
    Parking.External.greenMaxRate d n = 1 := by
  rw [Parking.External.greenMaxRate, if_neg (by omega : d ≠ 1), if_neg (by omega : d ≠ 2)]

theorem kappa_high {d : ℕ} (hd4 : 4 ≤ d) (n : ℕ) : kappa d n = 1 := by
  rw [kappa, if_neg (by omega : d ≠ 1), if_neg (by omega : d ≠ 2)]

theorem sqrt_log_le_log {n : ℕ} (hn : 2 ≤ n) :
    Real.sqrt (Real.log n) ≤ Real.log n / Real.sqrt (Real.log 2) := by
  have hlogpos := log_pos_of_two_le hn
  have h2 := log_two_le_log hn
  have hs2 : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.mpr log_two_pos
  rw [le_div_iff₀ hs2]
  have hmul : Real.sqrt (Real.log n) * Real.sqrt (Real.log 2)
      ≤ Real.sqrt (Real.log n) * Real.sqrt (Real.log n) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
  have hself : Real.sqrt (Real.log n) * Real.sqrt (Real.log n) = Real.log n :=
    Real.mul_self_sqrt (le_of_lt hlogpos)
  linarith

theorem upper_error_high {d : ℕ} (hd4 : 4 ≤ d) (hGN : Parking.External.GreenNorms) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 2 ≤ n →
      Real.sqrt (rHigh n) * l2Norm (green d n) + rHigh n * greenMax d n
          + rHigh n * (((n : ℝ) + 1) ^ (2 / rHigh n)) * kappa d n
        ≤ K * Real.log n := by
  have hd : 1 ≤ d := le_trans (by norm_num) hd4
  obtain ⟨⟨cL, CL, hcL, hCL, hLbd⟩, ⟨cM, CM, hcM, hCM, hMbd⟩⟩ := hGN d hd
  set A : ℝ := Real.sqrt rConst with hA
  have hA0 : 0 < A := Real.sqrt_pos.mpr rConst_pos
  set B : ℝ := 1 / Real.sqrt (Real.log 2) with hB
  have hB0 : 0 < B := by
    rw [hB]
    exact div_pos one_pos (Real.sqrt_pos.mpr log_two_pos)
  have hrc := rConst_pos
  have hKpos : (0 : ℝ) < CL * A * (B + 1) + CM * rConst + rConst * Real.exp 2 := by
    have p1 : (0 : ℝ) < CL * A * (B + 1) := mul_pos (mul_pos hCL hA0) (by linarith)
    have p2 : (0 : ℝ) < CM * rConst := mul_pos hCM hrc
    have p3 : (0 : ℝ) < rConst * Real.exp 2 := mul_pos hrc (Real.exp_pos 2)
    linarith
  refine ⟨CL * A * (B + 1) + CM * rConst + rConst * Real.exp 2, hKpos,
    fun n hn => ?_⟩
  have hlogpos := log_pos_of_two_le hn
  have hlog0 : (0 : ℝ) ≤ Real.log n := le_of_lt hlogpos
  have hr0 : 0 < rHigh n := rHigh_pos n
  have hrle : rHigh n ≤ rConst * Real.log n := rHigh_le_log hn
  -- the square root of the exponent
  have hsq : Real.sqrt (rHigh n) ≤ A * Real.sqrt (Real.log n) := by
    rw [hA, ← Real.sqrt_mul (le_of_lt rConst_pos)]
    exact Real.sqrt_le_sqrt hrle
  -- the two Green norms
  have hL := (hLbd n hn).2
  have hM := (hMbd n hn).2
  rw [greenMaxRate_high hd4 n, mul_one] at hM
  have hLhigh : l2Norm (green d n) ≤ CL * (1 + Real.sqrt (Real.log n)) := by
    refine hL.trans ?_
    exact mul_le_mul_of_nonneg_left (greenL2Rate_le_high hd4 n) (le_of_lt hCL)
  -- the exponential factor
  have hnp : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hexp2 : ((n : ℝ) + 1) ^ (2 / rHigh n) ≤ Real.exp 2 :=
    rpow_two_div_le_exp_two hnp hr0 (log_le_rHigh n)
  have hexp0 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (2 / rHigh n) :=
    Real.rpow_nonneg (by linarith) _
  -- the three terms
  have hsl : Real.sqrt (Real.log n) ≤ B * Real.log n := by
    have := sqrt_log_le_log hn
    rw [hB, one_div, inv_mul_eq_div]
    exact this
  have hs0 : (0 : ℝ) ≤ Real.sqrt (Real.log n) := Real.sqrt_nonneg _
  have hsqsq : Real.sqrt (Real.log n) * Real.sqrt (Real.log n) = Real.log n :=
    Real.mul_self_sqrt hlog0
  have hterm1 : Real.sqrt (rHigh n) * l2Norm (green d n)
      ≤ CL * A * (B + 1) * Real.log n := by
    have h1 : Real.sqrt (rHigh n) * l2Norm (green d n)
        ≤ (A * Real.sqrt (Real.log n)) * (CL * (1 + Real.sqrt (Real.log n))) := by
      refine mul_le_mul hsq hLhigh (Real.sqrt_nonneg _) ?_
      positivity
    refine h1.trans ?_
    have hexpand : (A * Real.sqrt (Real.log n)) * (CL * (1 + Real.sqrt (Real.log n)))
        = A * CL * Real.sqrt (Real.log n)
          + A * CL * (Real.sqrt (Real.log n) * Real.sqrt (Real.log n)) := by ring
    rw [hexpand, hsqsq]
    have hAC : (0 : ℝ) ≤ A * CL := by positivity
    nlinarith [hsl, hAC]
  have hterm2 : rHigh n * greenMax d n ≤ CM * rConst * Real.log n := by
    have hM0 : (0 : ℝ) ≤ greenMax d n := Real.iSup_nonneg fun x => green_nonneg n x
    calc rHigh n * greenMax d n ≤ (rConst * Real.log n) * CM :=
          mul_le_mul hrle hM hM0 (mul_nonneg (le_of_lt rConst_pos) hlog0)
      _ = CM * rConst * Real.log n := by ring
  have hterm3 : rHigh n * (((n : ℝ) + 1) ^ (2 / rHigh n)) * kappa d n
      ≤ rConst * Real.exp 2 * Real.log n := by
    rw [kappa_high hd4 n, mul_one]
    calc rHigh n * (((n : ℝ) + 1) ^ (2 / rHigh n))
        ≤ (rConst * Real.log n) * Real.exp 2 :=
          mul_le_mul hrle hexp2 hexp0 (mul_nonneg (le_of_lt rConst_pos) hlog0)
      _ = rConst * Real.exp 2 * Real.log n := by ring
  nlinarith [hterm1, hterm2, hterm3, hlog0]

/-! ### The moment bound `eq:critical-moment` -/

theorem integrable_expMax_of_expAbs {ν : Measure ℤ} {θ : ℝ} (hθ : 0 < θ)
    (h : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) :
    Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν := by
  refine Integrable.mono' h
    (measurable_from_countable' (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (Real.exp_pos _))]
  refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ (le_of_lt hθ))
  exact max_le (le_abs_self _) (abs_nonneg _)

theorem law_isProb (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (law d ν) := by
  haveI := stackRankLaw_isProbability (d := d) hd
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : Site d => ν))
  exact inferInstanceAs
    (IsProbabilityMeasure ((LatticeProb.iidLaw d ν).prod (stackRankLaw d)))

/-- **`eq:critical-moment`.**  Step 1 combined with `lem:u-concentration`. -/
theorem exists_critical_moment (hd : 1 ≤ d) (hBern : Parking.External.Bernstein)
    (hConc : Parking.External.UConcentration) (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 2 ≤ r →
      Integrable (fun ω => ((U ω n 0 : ℕ) : ℝ) ^ r) (law d ν) ∧
      (∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ r ∂(law d ν)) ^ (1 / r)
        ≤ C * (meanu (law d ν) n + Real.sqrt r * l2Norm (green d n)
            + r * greenMax d n + r * ((n : ℝ) + 1) ^ (2 / r) * kappa d n) := by
  haveI := hν.prob
  obtain ⟨θ, hθ, hexpabs⟩ := hν.expMoment
  have hexp := integrable_expMax_of_expAbs hθ hexpabs
  obtain ⟨C₁, hC₁, h1⟩ := upper_step_one hd hBern ν hθ hexp
  obtain ⟨C₂, hC₂, h2⟩ := exists_uNorm_le hd hConc ν hθ hexpabs hexp
  refine ⟨C₁ * (1 + C₂), by positivity, fun n hn r hr2 => ⟨?_, ?_⟩⟩
  · exact integrable_U_rpow hd ν hθ hexp (by linarith) n 0
  · have hr0 : (0 : ℝ) < r := by linarith
    have hA := h1 n hn r hr2
    have hB := h2 n hn r hr2
    have hm0 : (0 : ℝ) ≤ meanu (law d ν) n :=
      integral_nonneg fun ω => uOf_nonneg ω n 0
    have hL0 : (0 : ℝ) ≤ Real.sqrt r * l2Norm (green d n) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hM0 : (0 : ℝ) ≤ r * greenMax d n :=
      mul_nonneg (le_of_lt hr0) (Real.iSup_nonneg fun x => green_nonneg n x)
    have hT0 : (0 : ℝ) ≤ r * ((n : ℝ) + 1) ^ (2 / r) * kappa d n := by
      have h1' : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (2 / r) := by
        refine Real.rpow_nonneg ?_ _
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      exact mul_nonneg (mul_nonneg (le_of_lt hr0) h1') (kappa_nonneg d n)
    set X : ℝ := (∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ r ∂(law d ν)) ^ (1 / r) with hX
    set Y : ℝ := (∫ ω, |uOf ω n 0| ^ r ∂(law d ν)) ^ (1 / r) with hY
    set m : ℝ := meanu (law d ν) n with hm
    set S1 : ℝ := Real.sqrt r * l2Norm (green d n) with hS1
    set S2 : ℝ := r * greenMax d n with hS2
    set T : ℝ := r * ((n : ℝ) + 1) ^ (2 / r) * kappa d n with hT
    have hinner : Y + T ≤ (1 + C₂) * (m + S1 + S2 + T) := by nlinarith [hB, hm0, hT0]
    calc X ≤ C₁ * (Y + T) := hA
      _ ≤ C₁ * ((1 + C₂) * (m + S1 + S2 + T)) :=
          mul_le_mul_of_nonneg_left hinner hC₁.le
      _ = C₁ * (1 + C₂) * (m + S1 + S2 + T) := by ring

/-! ### `eq:target` -/

/-- **`eq:target`.**  The mean odometer against the mean sandpile odometer and
`log n`, by Steps 2 and 3. -/
theorem exists_target (hd : 1 ≤ d) (hBern : Parking.External.Bernstein)
    (hConc : Parking.External.UConcentration)
    (hGrowth : Parking.External.SandpileGrowth) (hGN : Parking.External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      Integrable (fun ω => ((U ω n 0 : ℕ) : ℝ)) (law d ν) ∧
      meanU (law d ν) n ≤ C * (meanu (law d ν) n + Real.log n) := by
  haveI := hν.prob
  haveI := law_isProb hd ν
  obtain ⟨θ, hθ, hexpabs⟩ := hν.expMoment
  have hexp := integrable_expMax_of_expAbs hθ hexpabs
  obtain ⟨C, hC, hCle⟩ := exists_critical_moment hd hBern hConc ν hν
  have hUint : ∀ n : ℕ, Integrable (fun ω : Data d => ((U ω n 0 : ℕ) : ℝ)) (law d ν) := by
    intro n
    exact Integrable.congr (integrable_U_rpow hd ν hθ hexp (le_refl (1 : ℝ)) n 0)
      (Filter.Eventually.of_forall fun ω => Real.rpow_one _)
  have hmean_le : ∀ (n : ℕ) (r : ℝ), 2 ≤ r →
      Integrable (fun ω : Data d => ((U ω n 0 : ℕ) : ℝ) ^ r) (law d ν) →
      meanU (law d ν) n ≤ (∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ r ∂(law d ν)) ^ (1 / r) := by
    intro n r hr2 hint
    exact integral_le_rNorm (fun ω => Nat.cast_nonneg _) (hUint n) (by linarith) hint
  have hm0 : ∀ n : ℕ, (0 : ℝ) ≤ meanu (law d ν) n :=
    fun n => integral_nonneg fun ω => uOf_nonneg ω n 0
  by_cases hd3 : d ≤ 3
  · -- Step 2
    obtain ⟨K, hK, hKle⟩ := upper_error_low hd hd3 hGN
    obtain ⟨c, C', hc, hC', hBP⟩ :=
      (hGrowth d hd (realLaw ν) (realLaw_isProbability ν) (realLaw_mean ν hν)
        (realLaw_evariance_pos ν hν) (realLaw_evariance_lt_top ν hν)
        (realLaw_expMoment ν hν)).1 hd3
    refine ⟨C * (1 + K / c), by positivity, fun n hn => ⟨hUint n, ?_⟩⟩
    have hint := (hCle n (by omega) 8 (by norm_num)).1
    have hbound := (hCle n (by omega) 8 (by norm_num)).2
    have hjensen := hmean_le n 8 (by norm_num) hint
    have herr := hKle n hn
    have hlow : c * (n : ℝ) ^ ((4 - (d : ℝ)) / 4) ≤ meanu (law d ν) n := by
      rw [meanu_eq_meanSandpileReal hd ν n]
      exact (hBP n hn).1
    have hrate0 : (0 : ℝ) ≤ (n : ℝ) ^ ((4 - (d : ℝ)) / 4) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hlog0 : (0 : ℝ) ≤ Real.log n := le_of_lt (log_pos_of_two_le hn)
    have herr' : Real.sqrt 8 * l2Norm (green d n) + 8 * greenMax d n
        + 8 * (((n : ℝ) + 1) ^ ((2 : ℝ) / 8)) * kappa d n
          ≤ (K / c) * meanu (law d ν) n := by
      refine herr.trans ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      calc K * (n : ℝ) ^ ((4 - (d : ℝ)) / 4) * c
          = K * (c * (n : ℝ) ^ ((4 - (d : ℝ)) / 4)) := by ring
        _ ≤ K * meanu (law d ν) n := mul_le_mul_of_nonneg_left hlow hK.le
    have hKc0 : (0 : ℝ) ≤ K / c := le_of_lt (div_pos hK hc)
    calc meanU (law d ν) n
        ≤ (∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ (8 : ℝ) ∂(law d ν)) ^ (1 / (8 : ℝ)) := hjensen
      _ ≤ C * (meanu (law d ν) n + Real.sqrt 8 * l2Norm (green d n)
            + 8 * greenMax d n + 8 * ((n : ℝ) + 1) ^ (2 / (8 : ℝ)) * kappa d n) := hbound
      _ ≤ C * ((1 + K / c) * meanu (law d ν) n) := by
          refine mul_le_mul_of_nonneg_left ?_ hC.le
          have := herr'
          linarith
      _ ≤ C * (1 + K / c) * (meanu (law d ν) n + Real.log n) := by
          have h1 : (0 : ℝ) ≤ C * (1 + K / c) := by positivity
          nlinarith [mul_nonneg h1 hlog0]
  · -- Step 3
    have hd4 : 4 ≤ d := by omega
    obtain ⟨K, hK, hKle⟩ := upper_error_high hd4 hGN
    refine ⟨C * (1 + K), by positivity, fun n hn => ⟨hUint n, ?_⟩⟩
    have hr2 : (2 : ℝ) ≤ rHigh n := two_le_rHigh n
    have hint := (hCle n (by omega) (rHigh n) hr2).1
    have hbound := (hCle n (by omega) (rHigh n) hr2).2
    have hjensen := hmean_le n (rHigh n) hr2 hint
    have herr := hKle n hn
    have hlog0 : (0 : ℝ) ≤ Real.log n := le_of_lt (log_pos_of_two_le hn)
    calc meanU (law d ν) n
        ≤ (∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ (rHigh n) ∂(law d ν)) ^ (1 / rHigh n) := hjensen
      _ ≤ C * (meanu (law d ν) n + Real.sqrt (rHigh n) * l2Norm (green d n)
            + rHigh n * greenMax d n
            + rHigh n * ((n : ℝ) + 1) ^ (2 / rHigh n) * kappa d n) := hbound
      _ ≤ C * (meanu (law d ν) n + K * Real.log n) := by
          refine mul_le_mul_of_nonneg_left ?_ hC.le
          linarith
      _ ≤ C * (1 + K) * (meanu (law d ν) n + Real.log n) := by
          have h1 : (0 : ℝ) ≤ C * Real.log n := mul_nonneg hC.le hlog0
          have h2 : (0 : ℝ) ≤ C * K * meanu (law d ν) n :=
            mul_nonneg (mul_nonneg hC.le hK.le) (hm0 n)
          nlinarith [h1, h2]

end Parking

end
