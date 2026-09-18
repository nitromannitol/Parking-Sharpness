/-
The optimization over the horizon in Step 2 of `prop:near-divisible`
(`parking.tex:2872-2879`): "taking expectations and optimizing over `m` gives the
matching lower bounds for `d ≤ 4` and the stated lower bound for `d ≥ 5`".

From dimension four the horizon is `⌈e/δ⌉`, which makes `log m` at least
`log(e/δ)` while the drift `δm` costs at most a constant; the constant is then
absorbed once `δ` is small enough that the rate exceeds it.

Below dimension four the rate is `m^α` with `α = (4-d)/4`, and the horizon is
`K δ^{-1/(1-α)}` for a `K` with `K^{1-α} ≤ c₀/2`.  With `t = δ^{-1/(1-α)}` both
`t^α` and `δ t` equal `δ^{-α/(1-α)}`, the target rate, so the gain is
`(c₀ K^α - K)` times that rate, and the choice of `K` makes that at least
`c₀ K^α / 2` of it.  The rounding of the horizon to an integer costs `3δ`, which
is absorbed the same way.

`Parking.nearLowerTarget` is the target: the four rates of
`eq:near-divisible-upper` below dimension five, and `[log(e/δ)]^{2/d}` above.
-/
import Parking.Support.NearStep1
import Parking.Support.NearOptimize

open MeasureTheory
noncomputable section
namespace Parking

/-- The target rate of the lower bounds of `prop:near-divisible`: the four rates of
`eq:near-divisible-upper` below dimension five, and `[log(e/δ)]^{2/d}` above. -/
def nearLowerTarget (d : ℕ) (δ : ℝ) : ℝ :=
  if d ≤ 4 then Parking.nearRate d δ else Real.log (Real.exp 1 / δ) ^ ((2:ℝ) / d)

theorem two_le_maxCeil (s : ℝ) : 2 ≤ max 2 ⌈s⌉₊ := le_max_left _ _

theorem le_maxCeil (s : ℝ) : s ≤ ((max 2 ⌈s⌉₊ : ℕ) : ℝ) := by
  refine le_trans (Nat.le_ceil s) ?_
  exact_mod_cast Nat.cast_le.mpr (le_max_right 2 ⌈s⌉₊)

theorem maxCeil_le {s : ℝ} (hs : 0 ≤ s) : ((max 2 ⌈s⌉₊ : ℕ) : ℝ) ≤ s + 3 := by
  have h1 : ((⌈s⌉₊ : ℕ) : ℝ) ≤ s + 1 := le_of_lt (Nat.ceil_lt_add_one hs)
  have h2 : ((max 2 ⌈s⌉₊ : ℕ) : ℝ) = max 2 ((⌈s⌉₊ : ℕ) : ℝ) := by
    rw [Nat.cast_max]; norm_num
  rw [h2]
  exact max_le (by linarith) (by linarith)

/-- **The optimization over the horizon, from dimension four.**  Choosing the horizon
`⌈e/δ⌉` makes the logarithm at least `log(e/δ)` while the drift costs at most a constant. -/
theorem exists_horizon_ge_four (d : ℕ) (hd4 : 4 ≤ d) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ c δ₂ : ℝ, 0 < c ∧ 0 < δ₂ ∧ δ₂ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₂ →
      ∃ m : ℕ, 2 ≤ m ∧ c * nearLowerTarget d δ ≤ c₀ * lowerRate d m - δ * m := by
  have hEle : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hE1 : (1:ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  by_cases hd4' : d = 4
  · subst hd4'
    refine ⟨c₀ / 2, min 1 (Real.exp (1 - 12 / c₀)), by positivity,
      lt_min one_pos (Real.exp_pos _), min_le_left _ _, ?_⟩
    intro δ hδ0 hδ2
    have hδ1 : δ ≤ 1 := le_trans hδ2 (min_le_left _ _)
    have hδe : δ ≤ Real.exp (1 - 12 / c₀) := le_trans hδ2 (min_le_right _ _)
    have hEδ : 0 < Real.exp 1 / δ := by positivity
    have hPval : Real.log (Real.exp 1 / δ) = 1 - Real.log δ := by
      rw [Real.log_div (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hδ0), Real.log_exp]
    have hPlow : 12 / c₀ ≤ Real.log (Real.exp 1 / δ) := by
      have hlog := Real.log_le_log hδ0 hδe
      rw [Real.log_exp] at hlog
      rw [hPval]
      linarith
    refine ⟨max 2 ⌈Real.exp 1 / δ⌉₊, two_le_maxCeil _, ?_⟩
    have hm1 : Real.exp 1 / δ ≤ ((max 2 ⌈Real.exp 1 / δ⌉₊ : ℕ) : ℝ) := le_maxCeil _
    have hm2 : ((max 2 ⌈Real.exp 1 / δ⌉₊ : ℕ) : ℝ) ≤ Real.exp 1 / δ + 3 :=
      maxCeil_le (le_of_lt hEδ)
    have hlogm : Real.log (Real.exp 1 / δ) ≤ Real.log ((max 2 ⌈Real.exp 1 / δ⌉₊ : ℕ) : ℝ) :=
      Real.log_le_log hEδ hm1
    have hcancel : δ * (Real.exp 1 / δ) = Real.exp 1 := by field_simp
    have hdrift : δ * ((max 2 ⌈Real.exp 1 / δ⌉₊ : ℕ) : ℝ) ≤ 6 := by
      have h := mul_le_mul_of_nonneg_left hm2 hδ0.le
      rw [mul_add, hcancel] at h
      linarith
    rw [nearLowerTarget, if_pos (by norm_num : (4:ℕ) ≤ 4), Parking.nearRate,
      if_neg (by norm_num : ¬(4:ℕ) = 1), if_neg (by norm_num : ¬(4:ℕ) = 2),
      if_neg (by norm_num : ¬(4:ℕ) = 3), lowerRate, if_neg (by norm_num : ¬(4:ℕ) ≤ 3),
      if_pos (rfl : (4:ℕ) = 4)]
    have hmul : c₀ * Real.log (Real.exp 1 / δ)
        ≤ c₀ * Real.log ((max 2 ⌈Real.exp 1 / δ⌉₊ : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hlogm hc₀.le
    have hPc : (12:ℝ) ≤ c₀ * Real.log (Real.exp 1 / δ) := by
      rw [div_le_iff₀ hc₀] at hPlow
      rw [mul_comm] at hPlow
      exact hPlow
    linarith [hmul, hdrift, hPc]
  · have hd5 : 5 ≤ d := by omega
    have hdpos : (0:ℝ) < (d:ℝ) := by positivity
    set A : ℝ := max 1 (12 / c₀) with hA
    have hA1 : (1:ℝ) ≤ A := le_max_left _ _
    have hA0 : (0:ℝ) < A := lt_of_lt_of_le one_pos hA1
    refine ⟨c₀ / 2, min 1 (Real.exp (1 - A ^ ((d:ℝ) / 2))), by positivity,
      lt_min one_pos (Real.exp_pos _), min_le_left _ _, ?_⟩
    intro δ hδ0 hδ2
    have hδ1 : δ ≤ 1 := le_trans hδ2 (min_le_left _ _)
    have hδe : δ ≤ Real.exp (1 - A ^ ((d:ℝ) / 2)) := le_trans hδ2 (min_le_right _ _)
    have hEδ : 0 < Real.exp 1 / δ := by positivity
    have hPval : Real.log (Real.exp 1 / δ) = 1 - Real.log δ := by
      rw [Real.log_div (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hδ0), Real.log_exp]
    have hPlow : A ^ ((d:ℝ) / 2) ≤ Real.log (Real.exp 1 / δ) := by
      have hlog := Real.log_le_log hδ0 hδe
      rw [Real.log_exp] at hlog
      rw [hPval]
      linarith
    have hP0 : (0:ℝ) ≤ Real.log (Real.exp 1 / δ) :=
      le_trans (Real.rpow_nonneg hA0.le _) hPlow
    have hPA : A ≤ Real.log (Real.exp 1 / δ) ^ ((2:ℝ) / d) := by
      have hmono := Real.rpow_le_rpow (Real.rpow_nonneg hA0.le _) hPlow
        (by positivity : (0:ℝ) ≤ (2:ℝ) / d)
      rwa [← Real.rpow_mul hA0.le, div_mul_div_comm, show (d:ℝ) * 2 = 2 * d by ring,
        div_self (by positivity : (2:ℝ) * (d:ℝ) ≠ 0), Real.rpow_one] at hmono
    refine ⟨max 2 ⌈Real.exp 1 / δ⌉₊, two_le_maxCeil _, ?_⟩
    have hm1 : Real.exp 1 / δ ≤ ((max 2 ⌈Real.exp 1 / δ⌉₊ : ℕ) : ℝ) := le_maxCeil _
    have hm2 : ((max 2 ⌈Real.exp 1 / δ⌉₊ : ℕ) : ℝ) ≤ Real.exp 1 / δ + 3 :=
      maxCeil_le (le_of_lt hEδ)
    have hlogm : Real.log (Real.exp 1 / δ) ≤ Real.log ((max 2 ⌈Real.exp 1 / δ⌉₊ : ℕ) : ℝ) :=
      Real.log_le_log hEδ hm1
    have hrate : Real.log (Real.exp 1 / δ) ^ ((2:ℝ) / d)
        ≤ Real.log ((max 2 ⌈Real.exp 1 / δ⌉₊ : ℕ) : ℝ) ^ ((2:ℝ) / d) :=
      Real.rpow_le_rpow hP0 hlogm (by positivity)
    have hcancel : δ * (Real.exp 1 / δ) = Real.exp 1 := by field_simp
    have hdrift : δ * ((max 2 ⌈Real.exp 1 / δ⌉₊ : ℕ) : ℝ) ≤ 6 := by
      have h := mul_le_mul_of_nonneg_left hm2 hδ0.le
      rw [mul_add, hcancel] at h
      linarith
    have hAlow : 12 / c₀ ≤ A := le_max_right _ _
    have hsix : (6:ℝ) ≤ (c₀ / 2) * Real.log (Real.exp 1 / δ) ^ ((2:ℝ) / d) := by
      have h1 : 12 / c₀ ≤ Real.log (Real.exp 1 / δ) ^ ((2:ℝ) / d) := le_trans hAlow hPA
      rw [div_le_iff₀ hc₀, mul_comm] at h1
      linarith
    rw [nearLowerTarget, if_neg (by omega), lowerRate, if_neg (by omega), if_neg hd4']
    have hmul : c₀ * Real.log (Real.exp 1 / δ) ^ ((2:ℝ) / d)
        ≤ c₀ * Real.log ((max 2 ⌈Real.exp 1 / δ⌉₊ : ℕ) : ℝ) ^ ((2:ℝ) / d) :=
      mul_le_mul_of_nonneg_left hrate hc₀.le
    linarith [hmul, hdrift, hsix]

/-- **The optimization over the horizon, below dimension four.**  Choosing the horizon
`K δ^{-1/(1-α)}` with `K^{1-α} ≤ c₀/2` makes the gain a fixed fraction of
`δ^{-α/(1-α)}`. -/
theorem exists_horizon_pow {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ c δ₂ : ℝ, 0 < c ∧ 0 < δ₂ ∧ δ₂ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₂ →
      ∃ m : ℕ, 2 ≤ m ∧ c * δ ^ (-α / (1 - α)) ≤ c₀ * ((m : ℕ) : ℝ) ^ α - δ * m := by
  have hone : (0:ℝ) < 1 - α := by linarith
  set K : ℝ := min 1 ((c₀ / 2) ^ (1 / (1 - α))) with hKdef
  have hK0 : 0 < K := lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)
  have hKα0 : 0 < K ^ α := Real.rpow_pos_of_pos hK0 α
  have hKpow : K ^ (1 - α) ≤ c₀ / 2 := by
    have hle : K ≤ (c₀ / 2) ^ (1 / (1 - α)) := min_le_right _ _
    have h := Real.rpow_le_rpow hK0.le hle hone.le
    rwa [← Real.rpow_mul (by positivity : (0:ℝ) ≤ c₀ / 2),
      one_div_mul_cancel (ne_of_gt hone), Real.rpow_one] at h
  have hKsplit : K ^ (1 - α) * K ^ α = K := by
    rw [← Real.rpow_add hK0]
    norm_num
  have hne : (1:ℝ) - α ≠ 0 := ne_of_gt hone
  have hKle : K ≤ c₀ / 2 * K ^ α :=
    calc K = K ^ (1 - α) * K ^ α := hKsplit.symm
      _ ≤ c₀ / 2 * K ^ α := mul_le_mul_of_nonneg_right hKpow hKα0.le
  refine ⟨c₀ * K ^ α / 4, min 1 (c₀ * K ^ α / 12), by positivity,
    lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  intro δ hδ0 hδ2
  have hδ1 : δ ≤ 1 := le_trans hδ2 (min_le_left _ _)
  have hδs : δ ≤ c₀ * K ^ α / 12 := le_trans hδ2 (min_le_right _ _)
  set t : ℝ := δ ^ (-1 / (1 - α)) with htdef
  set R : ℝ := δ ^ (-α / (1 - α)) with hRdef
  have ht0 : 0 < t := Real.rpow_pos_of_pos hδ0 _
  have hR1 : (1:ℝ) ≤ R :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ0 hδ1
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hone.le)
  have hδt : δ * t = R := by
    have h1 : δ * t = δ ^ ((1:ℝ) + (-1 / (1 - α))) := by
      rw [Real.rpow_add hδ0, Real.rpow_one, htdef]
    rw [h1, hRdef]
    congr 1
    field_simp
    ring
  have htα : t ^ α = R := by
    have h1 : t ^ α = δ ^ ((-1 / (1 - α)) * α) := by
      rw [htdef, ← Real.rpow_mul hδ0.le]
    rw [h1, hRdef]
    congr 1
    field_simp
  set s : ℝ := K * t with hsdef
  have hs0 : 0 ≤ s := by positivity
  refine ⟨max 2 ⌈s⌉₊, two_le_maxCeil _, ?_⟩
  have hms : s ≤ ((max 2 ⌈s⌉₊ : ℕ) : ℝ) := le_maxCeil _
  have hms2 : ((max 2 ⌈s⌉₊ : ℕ) : ℝ) ≤ s + 3 := maxCeil_le hs0
  have hsα : s ^ α = K ^ α * R := by
    rw [hsdef, Real.mul_rpow hK0.le ht0.le, htα]
  have hmα : K ^ α * R ≤ ((max 2 ⌈s⌉₊ : ℕ) : ℝ) ^ α := by
    rw [← hsα]
    exact Real.rpow_le_rpow hs0 hms hα0.le
  have hdrift : δ * ((max 2 ⌈s⌉₊ : ℕ) : ℝ) ≤ K * R + 3 * δ := by
    have h := mul_le_mul_of_nonneg_left hms2 hδ0.le
    have he : δ * (s + 3) = K * R + 3 * δ := by
      rw [hsdef, ← hδt]; ring
    linarith [h, he.le, he.ge]
  have hR0 : (0:ℝ) ≤ R := by linarith
  have hmain : c₀ * (K ^ α * R) ≤ c₀ * ((max 2 ⌈s⌉₊ : ℕ) : ℝ) ^ α :=
    mul_le_mul_of_nonneg_left hmα hc₀.le
  have hKR : K * R ≤ c₀ / 2 * K ^ α * R := by
    have := mul_le_mul_of_nonneg_right hKle hR0
    linarith [this]
  have hsmall : 3 * δ ≤ c₀ * K ^ α / 4 * R := by
    have h1 : 3 * δ ≤ c₀ * K ^ α / 4 := by linarith
    have h2 : c₀ * K ^ α / 4 ≤ c₀ * K ^ α / 4 * R := by nlinarith [hR1, hKα0, hc₀]
    linarith
  nlinarith [hmain, hKR, hsmall, hdrift]

/-- **The optimization over the horizon of `prop:near-divisible`** (`parking.tex:2872-2879`).
For every `δ` small there is a horizon at which the lower rate of `thm:BP`, less the drift,
is at least a fixed multiple of the target rate. -/
theorem exists_horizon (d : ℕ) (hd : 1 ≤ d) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ c δ₂ : ℝ, 0 < c ∧ 0 < δ₂ ∧ δ₂ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₂ →
      ∃ m : ℕ, 2 ≤ m ∧ c * nearLowerTarget d δ ≤ c₀ * lowerRate d m - δ * m := by
  by_cases h1 : d = 1
  · subst h1
    obtain ⟨c, δ₂, hc, hδ₂, hδ₂1, h⟩ :=
      exists_horizon_pow (α := (3:ℝ)/4) (by norm_num) (by norm_num) hc₀
    refine ⟨c, δ₂, hc, hδ₂, hδ₂1, fun δ hδ0 hδle => ?_⟩
    obtain ⟨m, hm2, hm⟩ := h δ hδ0 hδle
    refine ⟨m, hm2, ?_⟩
    have hlr : lowerRate 1 m = ((m : ℕ) : ℝ) ^ ((3:ℝ)/4) := by
      rw [lowerRate, if_pos (by norm_num : (1:ℕ) ≤ 3)]
      norm_num
    have htgt : nearLowerTarget 1 δ = δ ^ (-((3:ℝ)/4) / (1 - (3:ℝ)/4)) := by
      rw [nearLowerTarget, if_pos (by norm_num : (1:ℕ) ≤ 4), Parking.nearRate, if_pos rfl]
      norm_num
    rw [hlr, htgt]
    exact hm
  by_cases h2 : d = 2
  · subst h2
    obtain ⟨c, δ₂, hc, hδ₂, hδ₂1, h⟩ :=
      exists_horizon_pow (α := (1:ℝ)/2) (by norm_num) (by norm_num) hc₀
    refine ⟨c, δ₂, hc, hδ₂, hδ₂1, fun δ hδ0 hδle => ?_⟩
    obtain ⟨m, hm2, hm⟩ := h δ hδ0 hδle
    refine ⟨m, hm2, ?_⟩
    have hlr : lowerRate 2 m = ((m : ℕ) : ℝ) ^ ((1:ℝ)/2) := by
      rw [lowerRate, if_pos (by norm_num : (2:ℕ) ≤ 3)]
      norm_num
    have htgt : nearLowerTarget 2 δ = δ ^ (-((1:ℝ)/2) / (1 - (1:ℝ)/2)) := by
      rw [nearLowerTarget, if_pos (by norm_num : (2:ℕ) ≤ 4), Parking.nearRate,
        if_neg (by norm_num : ¬(2:ℕ) = 1), if_pos rfl]
      norm_num
      rw [Real.rpow_neg_one]
    rw [hlr, htgt]
    exact hm
  by_cases h3 : d = 3
  · subst h3
    obtain ⟨c, δ₂, hc, hδ₂, hδ₂1, h⟩ :=
      exists_horizon_pow (α := (1:ℝ)/4) (by norm_num) (by norm_num) hc₀
    refine ⟨c, δ₂, hc, hδ₂, hδ₂1, fun δ hδ0 hδle => ?_⟩
    obtain ⟨m, hm2, hm⟩ := h δ hδ0 hδle
    refine ⟨m, hm2, ?_⟩
    have hlr : lowerRate 3 m = ((m : ℕ) : ℝ) ^ ((1:ℝ)/4) := by
      rw [lowerRate, if_pos (by norm_num : (3:ℕ) ≤ 3)]
      norm_num
    have htgt : nearLowerTarget 3 δ = δ ^ (-((1:ℝ)/4) / (1 - (1:ℝ)/4)) := by
      rw [nearLowerTarget, if_pos (by norm_num : (3:ℕ) ≤ 4), Parking.nearRate,
        if_neg (by norm_num : ¬(3:ℕ) = 1), if_neg (by norm_num : ¬(3:ℕ) = 2), if_pos rfl]
      norm_num
    rw [hlr, htgt]
    exact hm
  · exact exists_horizon_ge_four d (by omega) hc₀

/-- **The lower bounds of `prop:near-divisible`** (`parking.tex:2861-2879`).  Step 2 at the
horizon chosen by `Parking.exists_horizon`. -/
theorem exists_meanuLimit_lower {d : ℕ} (hd : 1 ≤ d)
    (hGrowth : Parking.External.SandpileGrowth)
    {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ} (hfam : NearFamily δ₀ ν θ M K) :
    ∃ c δ₁ : ℝ, 0 < c ∧ 0 < δ₁ ∧ δ₁ ≤ δ₀ ∧ ∀ δ ∈ Set.Ioc (0:ℝ) δ₁,
      ENNReal.ofReal (c * nearLowerTarget d δ)
        ≤ Parking.meanuLimit (Parking.law d (ν δ)) := by
  obtain ⟨c₀, δ₁, hc₀, hδ₁, hδ₁₀, hlow⟩ := exists_meanu_lower hd hGrowth hfam
  obtain ⟨c, δ₂, hc, hδ₂, hδ₂1, hhor⟩ := exists_horizon d hd hc₀
  refine ⟨c, min δ₁ δ₂, hc, lt_min hδ₁ hδ₂, le_trans (min_le_left _ _) hδ₁₀, ?_⟩
  intro δ hδ
  obtain ⟨m, hm2, hm⟩ := hhor δ hδ.1 (le_trans hδ.2 (min_le_right _ _))
  have hδmem : δ ∈ Set.Ioc (0:ℝ) δ₁ := ⟨hδ.1, le_trans hδ.2 (min_le_left _ _)⟩
  have h := hlow δ hδmem m hm2
  exact le_trans (ENNReal.ofReal_le_ofReal (le_trans hm h)) (ofReal_meanu_le_meanuLimit m)

end Parking
end
