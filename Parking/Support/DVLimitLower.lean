import Parking.Support.DVUpper
import Parking.Support.DVLimitUpper

/-!
# The lower limit of `-log E_0 e^{-a|R_t|} / t^{d/(d+2)}`

If `n^{2/d} dirichletRate d n → c`, then for every `ε > 0`, eventually

  `log E_0 e^{-a|R_t|} ≤ -(dvConst d a c - ε) t^{d/(d+2)}`

(`eventually_log_rangeExp_le`).  Write `r = t^{1/(d+2)}` and `s = r^d = t^{d/(d+2)}`, so that
`t = r^2 s`.  Since `|R_t| ≤ t + 1`,
`E_0 e^{-a|R_t|} ≤ ∑_{n ≤ t+1} e^{-an} P_0(|R_t| ≤ n)` (`rangeExp_le_sum`).  For
`n ≥ C₀ s` the factor `e^{-an}` is small.  For `n < C₀ s` the bound
`Parking.measureReal_rangeCard_le` is used with boxes of side `m = ⌊ε_b r⌋`, killing rate
`κ = M / r^2`, threshold `σ / √s` and the volume `N = ⌈K₀ (m+1)^d + η s⌉`, and the inequality
of means `Parking.dvConst_le` bounds `a n + t dirichletRate d N` below.
-/

noncomputable section

namespace Parking

open LatticeProb MeasureTheory Filter Topology

variable {d : ℕ}

/-- `E_0 e^{-a|R_t|} ≤ ∑_{n ≤ t+1} e^{-an} P_0(|R_t| ≤ n)`. -/
theorem rangeExp_le_sum (hd : 1 ≤ d) {a : ℝ} (ha : 0 ≤ a) (t : ℕ) :
    rangeExp d a t ≤ ∑ n ∈ Finset.range (t + 2),
      Real.exp (-(a * n)) * (siteWalkLaw d 0).real {X | LatticeProb.rangeCard X t ≤ n} := by
  have : NeZero d := ⟨by omega⟩
  rw [rangeExp_eq hd]
  have hm : ∀ n : ℕ, MeasurableSet {X : ℕ → Site d | LatticeProb.rangeCard X t ≤ n} := by
    intro n
    change MeasurableSet ((fun X : ℕ → Site d => LatticeProb.rangeCard X t) ⁻¹' {k : ℕ | k ≤ n})
    exact (LatticeProb.measurable_rangeCard t) MeasurableSet.of_discrete
  have hfm : Measurable fun X : ℕ → Site d => Real.exp (-(a * (LatticeProb.rangeCard X t : ℝ))) :=
    (LatticeProb.measurable_from_countable'
      (fun k : ℕ => Real.exp (-(a * (k : ℝ))))).comp (LatticeProb.measurable_rangeCard t)
  have hint : Integrable (fun X : ℕ → Site d => Real.exp (-(a * (LatticeProb.rangeCard X t : ℝ))))
      (siteWalkLaw d 0) := by
    refine Integrable.of_bound hfm.aestronglyMeasurable 1 (Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ha (Nat.cast_nonneg _)))
  have hint' : ∀ n ∈ Finset.range (t + 2), Integrable (fun X : ℕ → Site d =>
      Real.exp (-(a * n)) * {X : ℕ → Site d | LatticeProb.rangeCard X t ≤ n}.indicator
        (fun _ => (1 : ℝ)) X) (siteWalkLaw d 0) :=
    fun n _ => ((integrable_const (1 : ℝ)).indicator (hm n)).const_mul _
  calc ∫ X, Real.exp (-(a * (LatticeProb.rangeCard X t : ℝ))) ∂(siteWalkLaw d 0)
      ≤ ∫ X, ∑ n ∈ Finset.range (t + 2), Real.exp (-(a * n)) *
          {X : ℕ → Site d | LatticeProb.rangeCard X t ≤ n}.indicator (fun _ => (1 : ℝ)) X
          ∂(siteWalkLaw d 0) := by
        refine integral_mono hint (integrable_finsetSum _ hint') fun X => ?_
        have hR : LatticeProb.rangeCard X t ∈ Finset.range (t + 2) := by
          rw [Finset.mem_range]
          have := Finset.card_image_le (s := Finset.range (t + 1)) (f := X)
          rw [Finset.card_range] at this
          unfold LatticeProb.rangeCard
          omega
        have h1 : Real.exp (-(a * (LatticeProb.rangeCard X t : ℝ)))
            = Real.exp (-(a * (LatticeProb.rangeCard X t : ℝ))) *
              {Y : ℕ → Site d | LatticeProb.rangeCard Y t ≤ LatticeProb.rangeCard X t}.indicator
                (fun _ => (1 : ℝ)) X := by
          rw [Set.indicator_of_mem (show X ∈ {Y : ℕ → Site d | LatticeProb.rangeCard Y t ≤
            LatticeProb.rangeCard X t} from Set.mem_ofPred.mpr (le_refl _)), mul_one]
        refine le_of_eq_of_le h1 ?_
        exact Finset.single_le_sum (f := fun n : ℕ => Real.exp (-(a * n)) *
          {Y : ℕ → Site d | LatticeProb.rangeCard Y t ≤ n}.indicator (fun _ => (1 : ℝ)) X)
          (fun n _ => mul_nonneg (Real.exp_pos _).le
            (Set.indicator_nonneg (fun _ _ => zero_le_one) _)) hR
    _ = ∑ n ∈ Finset.range (t + 2), Real.exp (-(a * n)) *
          (siteWalkLaw d 0).real {X | LatticeProb.rangeCard X t ≤ n} := by
        rw [integral_finsetSum _ hint']
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [integral_const_mul, integral_indicator_const _ (hm n), smul_eq_mul, mul_one]

/-- `dvConst` increases with `a`. -/
theorem dvConst_mono {a a' c : ℝ} (ha : 0 ≤ a) (haa' : a ≤ a') (hc : 0 ≤ c) :
    dvConst d a c ≤ dvConst d a' c := by
  unfold dvConst
  refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) ?_ (by positivity))
    (by positivity)
  exact mul_le_mul_of_nonneg_left haa' (by positivity)

/-- **The main inequality**: `a n + t Λ (1 - err) ≥ s (dvConst (a/γ) ((1-e₀) c) - (a/γ)(η + 1/s))`
when `Λ ≥ c N^{-2/d}`, `N ≤ γ n + η s + 1` and `t s^{-2/d} = s`. -/
theorem dv_main_lower (hd : 1 ≤ d) {a c e₀ γ η s t n N Λ err : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (he₀ : e₀ ≤ 1) (hγ : 1 ≤ γ) (hη : 0 ≤ η) (hs : 0 < s) (ht : 0 ≤ t)
    (hts : t * s ^ (-(2 : ℝ) / d) = s) (hn : 0 ≤ n) (hN : 0 < N) (hNle : N ≤ γ * n + η * s + 1)
    (hΛ : c * N ^ (-(2 : ℝ) / d) ≤ Λ) (herr : err ≤ e₀) :
    s * (dvConst d (a / γ) ((1 - e₀) * c) - a / γ * (η + 1 / s)) ≤ a * n + t * Λ * (1 - err) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hγ0 : 0 < γ := by linarith
  set w := (γ * n + η * s + 1) / s with hw
  have hw0 : 0 < w := by positivity
  have hsw : s * w = γ * n + η * s + 1 := by rw [hw]; field_simp
  have hexp : -(2 : ℝ) / d ≤ 0 := by
    have : (0 : ℝ) ≤ 2 / d := by positivity
    rw [neg_div]; linarith
  have hN1 : (s * w) ^ (-(2 : ℝ) / d) ≤ N ^ (-(2 : ℝ) / d) :=
    Real.rpow_le_rpow_of_nonpos hN (by rw [hsw]; exact hNle) hexp
  have hsw2 : (s * w) ^ (-(2 : ℝ) / d) = s ^ (-(2 : ℝ) / d) * w ^ (-(2 : ℝ) / d) :=
    Real.mul_rpow hs.le hw0.le
  have hΛ0 : 0 ≤ Λ := le_trans (mul_nonneg hc (Real.rpow_nonneg hN.le _)) hΛ
  have h1 : t * Λ * (1 - e₀) ≤ t * Λ * (1 - err) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg ht hΛ0)
  have h2 : t * (c * (s ^ (-(2 : ℝ) / d) * w ^ (-(2 : ℝ) / d))) * (1 - e₀) ≤ t * Λ * (1 - e₀) := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ ht) (by linarith)
    rw [← hsw2]
    exact le_trans (mul_le_mul_of_nonneg_left hN1 hc) hΛ
  have h3 : t * (c * (s ^ (-(2 : ℝ) / d) * w ^ (-(2 : ℝ) / d))) * (1 - e₀)
      = s * ((1 - e₀) * c * w ^ (-(2 : ℝ) / d)) := by
    calc t * (c * (s ^ (-(2 : ℝ) / d) * w ^ (-(2 : ℝ) / d))) * (1 - e₀)
        = (t * s ^ (-(2 : ℝ) / d)) * ((1 - e₀) * c * w ^ (-(2 : ℝ) / d)) := by ring
      _ = s * ((1 - e₀) * c * w ^ (-(2 : ℝ) / d)) := by rw [hts]
  have h4 : a * n = s * (a / γ * w - a / γ * (η + 1 / s)) := by
    have : a / γ * w - a / γ * (η + 1 / s) = a / γ * (w - η - 1 / s) := by ring
    rw [this]
    have hwn : w - η - 1 / s = γ * n / s := by rw [hw]; field_simp; ring
    rw [hwn]
    field_simp
  have h5 := dvConst_le hd (a := a / γ) (c := (1 - e₀) * c) (by positivity)
    (mul_nonneg (by linarith) hc) hw0
  have h6 : s * (dvConst d (a / γ) ((1 - e₀) * c) - a / γ * (η + 1 / s))
      ≤ s * (a / γ * w - a / γ * (η + 1 / s)) + s * ((1 - e₀) * c * w ^ (-(2 : ℝ) / d)) := by
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ hs.le
    have : (1 - e₀) * c * w ^ (-(2 : ℝ) / d) = ((1 - e₀) * c) * w ^ (-(2 : ℝ) / d) := rfl
    linarith
  linarith

/-- **Perturbed constants.**  For `ε > 0` there are `δ, e₀ ∈ (0, 1/2]` and `ε₁ > 0` with
`dvConst (a(1-δ)/(1+δ)) ((1-e₀) max(c - ε₁, 0)) ≥ dvConst a c - ε/8`. -/
theorem exists_dvConst_params (d : ℕ) {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ e₀ ε₁ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ 0 < e₀ ∧ e₀ ≤ 1 / 2 ∧ 0 < ε₁ ∧
      dvConst d a c - ε / 8 ≤ dvConst d (a * (1 - δ) / (1 + δ)) ((1 - e₀) * max (c - ε₁) 0) := by
  have hcont := (continuous_dvConst d).continuousAt (x := (a, c))
  have hev := hcont.eventually (lt_mem_nhds (by linarith : dvConst d a c - ε / 8 < dvConst d a c))
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set δ := min (1 / 2) (ρ / (4 * a)) with hδ
  set e₀ := min (1 / 2) (ρ / (4 * (c + 1))) with he₀
  set ε₁ := ρ / 4 with hε₁
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have he₀0 : 0 < e₀ := lt_min (by norm_num) (by positivity)
  refine ⟨δ, e₀, ε₁, hδ0, min_le_left _ _, he₀0, min_le_left _ _, by positivity, ?_⟩
  refine (hball (y := (a * (1 - δ) / (1 + δ), (1 - e₀) * max (c - ε₁) 0)) ?_).le
  rw [Prod.dist_eq, max_lt_iff]
  constructor
  · rw [Real.dist_eq]
    have h1 : a - a * (1 - δ) / (1 + δ) = 2 * a * δ / (1 + δ) := by field_simp; ring
    have h2 : 2 * a * δ / (1 + δ) ≤ 2 * a * δ := div_le_self (by positivity) (by linarith)
    have h3 : 2 * a * δ ≤ ρ / 2 := by
      have := min_le_right (1 / 2) (ρ / (4 * a))
      rw [← hδ] at this
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    rw [abs_sub_comm, abs_of_nonneg (by rw [h1]; positivity)]
    linarith
  · rw [Real.dist_eq]
    have he₀le : e₀ * (c + 1) ≤ ρ / 4 := by
      have := min_le_right (1 / 2) (ρ / (4 * (c + 1)))
      rw [← he₀] at this
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    have hm1 : c - ε₁ ≤ max (c - ε₁) 0 := le_max_left _ _
    have hm2 : max (c - ε₁) 0 ≤ c := max_le (by linarith [show 0 < ε₁ by positivity]) hc
    have hlow : c - ρ / 4 - ρ / 4 ≤ (1 - e₀) * max (c - ε₁) 0 := by
      have : (1 - e₀) * max (c - ε₁) 0 ≥ (1 - e₀) * (c - ε₁) :=
        mul_le_mul_of_nonneg_left hm1 (by linarith [min_le_left (1 / 2 : ℝ) (ρ / (4 * (c + 1)))])
      nlinarith
    have hup : (1 - e₀) * max (c - ε₁) 0 ≤ c := by
      have h0 : 0 ≤ max (c - ε₁) 0 := le_max_right _ _
      nlinarith
    rw [abs_lt]
    constructor <;> linarith

/-! ### The two terms of the bound -/

/-- **The first term**: the event of a long time in porous boxes. -/
theorem first_term_le {n s t r ℓ q θ εb C₀ K : ℝ} (hn : n ≤ C₀ * s) (hs : 0 < s)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ 2 * εb ^ 2 * r ^ 2) (hεb : 0 < εb) (ht : t = r ^ 2 * s)
    (hq : 0 ≤ q) (hθ : 0 ≤ θ) (hqθ : C₀ + K + 2 ≤ q * θ / (4 * εb ^ 2)) (hs3 : 3 * q / 2 ≤ s) :
    2 * Real.exp (n - q * ((θ * t - 3 * ℓ) / (2 * ℓ))) ≤ 2 * Real.exp (-((K + 1) * s)) := by
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  have h1 : (θ * t - 3 * ℓ) / (2 * ℓ) = θ * t / (2 * ℓ) - 3 / 2 := by field_simp
  have h2 : θ * s / (4 * εb ^ 2) ≤ θ * t / (2 * ℓ) := by
    rw [ht, div_le_div_iff₀ (by positivity) (by positivity)]
    have : θ * s * (2 * ℓ) ≤ θ * s * (2 * (2 * εb ^ 2 * r ^ 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have h3 : (C₀ + K + 2) * s ≤ q * θ / (4 * εb ^ 2) * s := mul_le_mul_of_nonneg_right hqθ hs.le
  have h4 : q * θ / (4 * εb ^ 2) * s = q * (θ * s / (4 * εb ^ 2)) := by ring
  have h5 : q * (θ * s / (4 * εb ^ 2)) ≤ q * (θ * t / (2 * ℓ)) := mul_le_mul_of_nonneg_left h2 hq
  rw [h1]
  nlinarith

/-- The second term in exponential form. -/
theorem second_term_exp_le {a n t Λ err κ θ Cnt : ℝ} (tn : ℕ) (htn : (tn : ℝ) = t)
    (hx1 : Λ * (1 - err) ≤ 1) (hCnt : 1 ≤ Cnt) (ht : 0 ≤ t) :
    Real.exp (-(a * n)) * (Cnt * (Real.exp (κ * (θ * t)) * ((1 - Λ * (1 - err)) ^ tn
        * Real.sqrt (Real.exp κ * (2 * t + 1) ^ d))))
      ≤ Real.exp (-(a * n) - t * (Λ * (1 - err)) + κ * (θ * t) + Real.log Cnt + κ / 2
          + d * Real.log (2 * t + 1) / 2) := by
  set x := Λ * (1 - err)
  have h1 : (1 - x) ^ tn ≤ Real.exp (-(t * x)) := by
    have h := Real.add_one_le_exp (-x)
    calc (1 - x) ^ tn ≤ Real.exp (-x) ^ tn := pow_le_pow_left₀ (by linarith) (by linarith) _
      _ = Real.exp (-(t * x)) := by rw [← Real.exp_nat_mul, htn]; ring_nf
  have h2 : Real.sqrt (Real.exp κ * (2 * t + 1) ^ d)
      = Real.exp (κ / 2 + d * Real.log (2 * t + 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_log (by positivity : (0 : ℝ) < Real.exp κ * (2 * t + 1) ^ d),
      ← Real.exp_mul, Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp,
      Real.log_pow]
    ring_nf
  have h3 : Cnt = Real.exp (Real.log Cnt) := (Real.exp_log (by linarith)).symm
  calc Real.exp (-(a * n)) * (Cnt * (Real.exp (κ * (θ * t)) * ((1 - x) ^ tn
        * Real.sqrt (Real.exp κ * (2 * t + 1) ^ d))))
      ≤ Real.exp (-(a * n)) * (Cnt * (Real.exp (κ * (θ * t)) * (Real.exp (-(t * x))
        * Real.sqrt (Real.exp κ * (2 * t + 1) ^ d)))) := by
        gcongr
    _ = _ := by
        rw [h2]
        conv_lhs => rw [h3]
        simp only [← Real.exp_add]
        congr 1
        ring

/-! ### The scales -/

/-- With `r = t^{1/(d+2)}` and `s = t^{d/(d+2)}`: `r^d = s`, `t = r^2 s`, `s^{-2/d} r^2 = 1`. -/
theorem scale_facts (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) :
    (t ^ ((1 : ℝ) / (d + 2))) ^ d = t ^ ((d : ℝ) / (d + 2)) ∧
      t = (t ^ ((1 : ℝ) / (d + 2))) ^ 2 * t ^ ((d : ℝ) / (d + 2)) ∧
      (t ^ ((d : ℝ) / (d + 2))) ^ (-(2 : ℝ) / d) * (t ^ ((1 : ℝ) / (d + 2))) ^ 2 = 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : (t ^ ((1 : ℝ) / (d + 2))) ^ d = t ^ ((d : ℝ) / (d + 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1
    field_simp
  have h2 : (t ^ ((1 : ℝ) / (d + 2))) ^ 2 = t ^ ((2 : ℝ) / (d + 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1
    push_cast
    field_simp
  refine ⟨h1, ?_, ?_⟩
  · rw [h2, ← Real.rpow_add ht]
    have : (2 : ℝ) / (d + 2) + d / (d + 2) = 1 := by field_simp; ring
    rw [this, Real.rpow_one]
  · rw [h2, ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
    have : (d : ℝ) / (d + 2) * (-(2 : ℝ) / d) + 2 / (d + 2) = 0 := by field_simp; ring
    rw [this, Real.rpow_zero]

/-! ### The conditions of the soft-killing step -/

/-- The volume condition: `2^d Λ/((1-Λ) κ s_p^2) ≤ η s`. -/
theorem soft_vol_le (hd : 1 ≤ d) {Λ κ sp t s η cU M σ N : ℝ}
    (hΛ : Λ ≤ cU * N ^ (-(2 : ℝ) / d)) (hΛ1 : Λ ≤ 1 / 2) (hηs : η * s ≤ N) (hη : 0 < η)
    (hs : 0 < s) (hcU : 0 ≤ cU) (hM : 0 < M) (hσ : 0 < σ) (ht : 0 < t)
    (hκsp : κ * sp ^ 2 = M * σ ^ 2 / t) (hts : t * s ^ (-(2 : ℝ) / d) = s)
    (hMN : 2 ^ (d + 1) * cU * η ^ (-(2 : ℝ) / d) / (M * σ ^ 2) ≤ η) :
    2 ^ d * (Λ / ((1 - Λ) * κ * sp ^ 2)) ≤ η * s := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hexp : -(2 : ℝ) / d ≤ 0 := by
    have : (0 : ℝ) ≤ 2 / d := by positivity
    rw [neg_div]; linarith
  have hκsp0 : 0 < κ * sp ^ 2 := by rw [hκsp]; positivity
  have hN1 : N ^ (-(2 : ℝ) / d) ≤ (η * s) ^ (-(2 : ℝ) / d) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hηs hexp
  have hN2 : (η * s) ^ (-(2 : ℝ) / d) = η ^ (-(2 : ℝ) / d) * s ^ (-(2 : ℝ) / d) :=
    Real.mul_rpow hη.le hs.le
  have hΛ2 : Λ ≤ cU * η ^ (-(2 : ℝ) / d) * s ^ (-(2 : ℝ) / d) := by
    calc Λ ≤ cU * N ^ (-(2 : ℝ) / d) := hΛ
      _ ≤ cU * (η * s) ^ (-(2 : ℝ) / d) := mul_le_mul_of_nonneg_left hN1 hcU
      _ = cU * η ^ (-(2 : ℝ) / d) * s ^ (-(2 : ℝ) / d) := by rw [hN2]; ring
  have hden : (1 - Λ) * κ * sp ^ 2 = (1 - Λ) * (M * σ ^ 2 / t) := by rw [mul_assoc, hκsp]
  rw [hden]
  have h1Λ : 1 / 2 ≤ 1 - Λ := by linarith
  have hpos : 0 < (1 - Λ) * (M * σ ^ 2 / t) := by positivity
  rw [mul_div_assoc', div_le_iff₀ hpos]
  have hstep : 2 ^ d * Λ ≤ 2 ^ d * (cU * η ^ (-(2 : ℝ) / d) * s ^ (-(2 : ℝ) / d)) :=
    mul_le_mul_of_nonneg_left hΛ2 (by positivity)
  have hMN' : 2 ^ (d + 1) * cU * η ^ (-(2 : ℝ) / d) ≤ η * (M * σ ^ 2) := by
    rwa [div_le_iff₀ (by positivity)] at hMN
  have hfin : 2 ^ d * (cU * η ^ (-(2 : ℝ) / d) * s ^ (-(2 : ℝ) / d))
      ≤ η * s * ((1 / 2) * (M * σ ^ 2 / t)) := by
    have e1 : η * s * ((1 / 2) * (M * σ ^ 2 / t))
        = (η * (M * σ ^ 2)) / 2 * (s / t) := by ring
    have e2 : s / t = s ^ (-(2 : ℝ) / d) := by
      rw [div_eq_iff ht.ne']; linarith [hts]
    rw [e1, e2]
    have e3 : 2 ^ d * (cU * η ^ (-(2 : ℝ) / d) * s ^ (-(2 : ℝ) / d))
        = (2 ^ (d + 1) * cU * η ^ (-(2 : ℝ) / d)) / 2 * s ^ (-(2 : ℝ) / d) := by
      rw [pow_succ]; ring
    rw [e3]
    have hsp : 0 ≤ s ^ (-(2 : ℝ) / d) := Real.rpow_nonneg hs.le _
    exact mul_le_mul_of_nonneg_right (by linarith) hsp
  calc 2 ^ d * Λ ≤ 2 ^ d * (cU * η ^ (-(2 : ℝ) / d) * s ^ (-(2 : ℝ) / d)) := hstep
    _ ≤ η * s * ((1 / 2) * (M * σ ^ 2 / t)) := hfin
    _ ≤ η * s * ((1 - Λ) * (M * σ ^ 2 / t)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1Λ (by positivity)) (by positivity)

/-- The error condition: `softErr (n/(1-δ)) Λ κ s_p ≤ e₀`. -/
theorem soft_err_le {n δ Λ κ sp s r C₀ η cU M σ e₀ : ℝ} (hn : n ≤ C₀ * s) (hδ : δ < 1) (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ cU * η ^ (-(2 : ℝ) / d) * s ^ (-(2 : ℝ) / d))
    (hΛ1 : Λ ≤ 1 / 2) (hvol : Λ / ((1 - Λ) * κ * sp ^ 2) ≤ η * s) (hs : 0 < s) (hσ : 0 < σ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η) (hC₀ : 0 ≤ C₀) (hsp : sp = σ / Real.sqrt s)
    (hκ : κ = M / r ^ 2) (hsr : s ^ (-(2 : ℝ) / d) * r ^ 2 = 1)
    (hσerr : 2 * σ * Real.sqrt (C₀ / (1 - δ) + η) + σ ^ 2 * (C₀ / (1 - δ)) ≤ e₀ / 2)
    (hMerr : 2 * cU * η ^ (-(2 : ℝ) / d) / M ≤ e₀ / 2) :
    softErr (n / (1 - δ)) Λ κ sp ≤ e₀ := by
  have hδ' : 0 < 1 - δ := by linarith
  have hsqs : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsp0 : 0 ≤ sp := by rw [hsp]; positivity
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  unfold softErr
  set X := Λ / ((1 - Λ) * κ * sp ^ 2) with hX
  -- the first term
  have hA1 : n / (1 - δ) + X ≤ (C₀ / (1 - δ) + η) * s := by
    have : n / (1 - δ) ≤ C₀ / (1 - δ) * s := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hδ']; linarith
    linarith
  have hA2 : Real.sqrt (n / (1 - δ) + X)
      ≤ Real.sqrt (C₀ / (1 - δ) + η) * Real.sqrt s := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hA1
  have hA : 2 * sp * Real.sqrt (n / (1 - δ) + X) ≤ 2 * σ * Real.sqrt (C₀ / (1 - δ) + η) := by
    calc 2 * sp * Real.sqrt (n / (1 - δ) + X)
        ≤ 2 * sp * (Real.sqrt (C₀ / (1 - δ) + η) * Real.sqrt s) :=
          mul_le_mul_of_nonneg_left hA2 (by positivity)
      _ = 2 * σ * Real.sqrt (C₀ / (1 - δ) + η) := by
          rw [hsp]; field_simp
  -- the second term
  have hB : sp ^ 2 * (n / (1 - δ)) ≤ σ ^ 2 * (C₀ / (1 - δ)) := by
    rw [hsp, div_pow, Real.sq_sqrt hs.le]
    rw [div_mul_div_comm, div_le_iff₀ (by positivity)]
    have : σ ^ 2 * n ≤ σ ^ 2 * (C₀ * s) := mul_le_mul_of_nonneg_left hn (by positivity)
    calc σ ^ 2 * n ≤ σ ^ 2 * (C₀ * s) := this
      _ = σ ^ 2 * (C₀ / (1 - δ)) * (s * (1 - δ)) := by field_simp
  -- the third term
  have hC : Λ / ((1 - Λ) * κ) ≤ 2 * cU * η ^ (-(2 : ℝ) / d) / M := by
    have h1Λ : 1 / 2 ≤ 1 - Λ := by linarith
    rw [div_le_div_iff₀ (by positivity) hM]
    have h1 : Λ * M ≤ cU * η ^ (-(2 : ℝ) / d) * s ^ (-(2 : ℝ) / d) * M :=
      mul_le_mul_of_nonneg_right hΛ hM.le
    have h2 : cU * η ^ (-(2 : ℝ) / d) * s ^ (-(2 : ℝ) / d) * M
        = cU * η ^ (-(2 : ℝ) / d) * κ * (s ^ (-(2 : ℝ) / d) * r ^ 2) := by
      rw [hκ]; field_simp
    rw [hsr, mul_one] at h2
    have hcη : 0 ≤ cU * η ^ (-(2 : ℝ) / d) := by
      by_contra hneg
      push Not at hneg
      have : Λ * M < 0 := by
        calc Λ * M ≤ cU * η ^ (-(2 : ℝ) / d) * κ := h1.trans (le_of_eq h2)
          _ < 0 := mul_neg_of_neg_of_pos hneg hκ0
      nlinarith
    have h3 : cU * η ^ (-(2 : ℝ) / d) * κ ≤ 2 * cU * η ^ (-(2 : ℝ) / d) * ((1 - Λ) * κ) := by
      have : κ ≤ 2 * ((1 - Λ) * κ) := by nlinarith
      nlinarith
    linarith
  linarith

/-- The count of candidate sets in the exponent. -/
theorem log_count_le {K₀ t : ℕ} {Kmax : ℝ} (hK : (K₀ : ℝ) ≤ Kmax) :
    Real.log ((((K₀ + 1) * ((2 * t + 1) ^ d) ^ K₀ : ℕ)) : ℝ)
      ≤ Kmax * (1 + d * Real.log (2 * t + 1)) := by
  push_cast
  have h2t : (1 : ℝ) ≤ 2 * t + 1 := by have : (0 : ℝ) ≤ t := Nat.cast_nonneg t; linarith
  have hlog0 : 0 ≤ Real.log (2 * t + 1) := Real.log_nonneg h2t
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have h1 : Real.log ((K₀ : ℝ) + 1) ≤ K₀ := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < K₀ + 1)
    linarith
  have hK0 : (0 : ℝ) ≤ K₀ := Nat.cast_nonneg _
  have h2 : (K₀ : ℝ) * (d * Real.log (2 * t + 1)) ≤ Kmax * (d * Real.log (2 * t + 1)) :=
    mul_le_mul_of_nonneg_right hK (by positivity)
  nlinarith

/-! ### The bound for a fixed small range size -/

theorem combine_two_terms {P T1 T2 E X Y : ℝ} (hP : P ≤ T1 + T2) (h1 : E * T1 ≤ 2 * X)
    (h2 : E * T2 ≤ Y) (hXY : X ≤ Y) (hE : 0 ≤ E) : E * P ≤ 3 * Y := by
  have := mul_le_mul_of_nonneg_left hP hE
  nlinarith

/-- **The bound for a range size below `C₀ s`.** -/
theorem small_n_bound (hd : 1 ≤ d) {a c K ε : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hε : 0 < ε)
    {m : ℕ} [NeZero m] {δ p₀ e₀ cl η σ M θ εb C₀ Kmax : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hp₀ : 0 ≤ p₀)
    (hhit : ∀ (z y : Site d), y ∈ boxCell m z → ∀ A : Finset (Site d), A ⊆ boxCell m z →
      δ * (m : ℝ) ^ d ≤ A.card →
        p₀ ≤ (siteWalkLaw d y).real {Y | ∃ j, 1 ≤ j ∧ j ≤ 2 * m ^ 2 ∧ Y j ∈ A})
    (he₀1 : e₀ ≤ 1 / 2) (hcl : 0 ≤ cl) (hη : 0 < η) (hσ : 0 < σ) (hM : 0 < M) (hθ : 0 < θ)
    (hεb : 0 < εb) (hC₀ : 0 < C₀)
    (hK : K - ε / 8 ≤ dvConst d (a * (1 - δ) / (1 + δ)) ((1 - e₀) * cl))
    (haη : a * η ≤ ε / 16)
    (hσerr : 2 * σ * Real.sqrt (C₀ / (1 - δ) + η) + σ ^ 2 * (C₀ / (1 - δ)) ≤ e₀ / 2)
    (hMerr : 2 * (c + 1) * η ^ (-(2 : ℝ) / d) / M ≤ e₀ / 2)
    (hMN : 2 ^ (d + 1) * (c + 1) * η ^ (-(2 : ℝ) / d) / (M * σ ^ 2) ≤ η)
    (hMθ : M * θ ≤ ε / 8)
    (hqθ : C₀ + K + 2 ≤ (1 - Real.exp (-1)) * p₀ * θ / (4 * εb ^ 2))
    {Nthr : ℕ}
    (hΛlow : ∀ N : ℕ, Nthr ≤ N → cl * (N : ℝ) ^ (-(2 : ℝ) / d) ≤ dirichletRate d N)
    (hΛup : ∀ N : ℕ, Nthr ≤ N → dirichletRate d N ≤ (c + 1) * (N : ℝ) ^ (-(2 : ℝ) / d))
    (hΛhalf : ∀ N : ℕ, Nthr ≤ N → dirichletRate d N ≤ 1 / 2)
    {t : ℕ} {r s : ℝ} (hr1 : 1 ≤ r) (hs0 : 0 < s) (hrs : r ^ d = s)
    (hts : (t : ℝ) = r ^ 2 * s) (htss : (t : ℝ) * s ^ (-(2 : ℝ) / d) = s)
    (hsr : s ^ (-(2 : ℝ) / d) * r ^ 2 = 1)
    (hm : (m : ℝ) ≤ εb * r) (hm2 : εb * r / 2 ≤ m) (hmγ : (((m : ℝ) + 1) / m) ^ d ≤ 1 + δ)
    (h2m : 2 * m ^ 2 ≤ t) (hNthr : (Nthr : ℝ) ≤ η * s)
    (hs3 : 3 * ((1 - Real.exp (-1)) * p₀) / 2 ≤ s) (has : a / s ≤ ε / 16)
    (hKmax : 2 ^ d * C₀ / ((1 - δ) * εb ^ d) ≤ Kmax)
    (hlog : (Kmax + 2) * (1 + d * Real.log (2 * t + 1)) + M / 2 ≤ ε / 8 * s)
    (n : ℕ) (hn : (n : ℝ) < C₀ * s) :
    Real.exp (-(a * n)) * (siteWalkLaw d 0).real {X | LatticeProb.rangeCard X t ≤ n}
      ≤ 3 * Real.exp (-((K - ε / 2) * s)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hr0 : 0 < r := by linarith only [hr1]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_neZero m
  have hδ' : 0 < 1 - δ := by linarith only [hδ1]
  have htpos : (0 : ℝ) < t := by rw [hts]; positivity
  set κ := M / r ^ 2 with hκ
  set sp := σ / Real.sqrt s with hsp
  have hκ0 : 0 < κ := by positivity
  have hsp0 : 0 < sp := by positivity
  set K₀ := fullBound d n m δ with hK₀
  have hK₀le : (K₀ : ℝ) ≤ n / ((1 - δ) * (m : ℝ) ^ d) := Nat.floor_le (by positivity)
  set N : ℕ := ⌈((K₀ * (m + 1) ^ d : ℕ) : ℝ) + η * s⌉₊ with hN
  have hKm0 : (0 : ℝ) ≤ ((K₀ * (m + 1) ^ d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hNge : ((K₀ * (m + 1) ^ d : ℕ) : ℝ) + η * s ≤ N := Nat.le_ceil _
  have hηs0 : 0 < η * s := by positivity
  have hNle : (N : ℝ) ≤ ((K₀ * (m + 1) ^ d : ℕ) : ℝ) + η * s + 1 :=
    (Nat.ceil_lt_add_one (by linarith only [hKm0, hηs0])).le
  have hηsN : η * s ≤ N := by linarith only [hKm0, hNge]
  have hNthrN : Nthr ≤ N := by
    have : (Nthr : ℝ) ≤ N := hNthr.trans hηsN
    exact_mod_cast this
  set Λ := dirichletRate d N with hΛ
  have hΛ0 : 0 ≤ Λ := dirichletRate_nonneg d N
  have hΛhalf' := hΛhalf N hNthrN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le hηs0 hηsN
  have hexp : -(2 : ℝ) / d ≤ 0 := by
    have : (0 : ℝ) ≤ 2 / d := by positivity
    rw [neg_div]; linarith only [this]
  have hΛ' : Λ ≤ (c + 1) * η ^ (-(2 : ℝ) / d) * s ^ (-(2 : ℝ) / d) := by
    have h1 := hΛup N hNthrN
    have h2 : (N : ℝ) ^ (-(2 : ℝ) / d) ≤ (η * s) ^ (-(2 : ℝ) / d) :=
      Real.rpow_le_rpow_of_nonpos hηs0 hηsN hexp
    rw [Real.mul_rpow hη.le hs0.le] at h2
    calc Λ ≤ (c + 1) * (N : ℝ) ^ (-(2 : ℝ) / d) := h1
      _ ≤ (c + 1) * (η ^ (-(2 : ℝ) / d) * s ^ (-(2 : ℝ) / d)) :=
          mul_le_mul_of_nonneg_left h2 (by linarith only [hc])
      _ = (c + 1) * η ^ (-(2 : ℝ) / d) * s ^ (-(2 : ℝ) / d) := by ring
  have hκsp : κ * sp ^ 2 = M * σ ^ 2 / t := by
    rw [hκ, hsp, div_pow, Real.sq_sqrt hs0.le, hts]
    field_simp
  have hvol := soft_vol_le hd (hΛup N hNthrN) hΛhalf' hηsN hη hs0 (by linarith only [hc]) hM
    hσ htpos hκsp htss hMN
  have h1Λ : 0 < 1 - Λ := by linarith only [hΛhalf']
  have hX0 : 0 ≤ Λ / ((1 - Λ) * κ * sp ^ 2) := by positivity
  have hvol' : Λ / ((1 - Λ) * κ * sp ^ 2) ≤ η * s := by
    have h2d : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
    calc Λ / ((1 - Λ) * κ * sp ^ 2) ≤ 2 ^ d * (Λ / ((1 - Λ) * κ * sp ^ 2)) :=
          le_mul_of_one_le_left hX0 h2d
      _ ≤ η * s := hvol
  have hδlt : δ < 1 := by linarith only [hδ1]
  have herr := soft_err_le hn.le hδlt hΛ0 hΛ' hΛhalf' hvol' hs0 hσ hM hr0 hη
    hC₀.le hsp hκ hsr hσerr hMerr
  have herr1 : softErr (n / (1 - δ)) Λ κ sp < 1 := by linarith only [herr, he₀1]
  have hNcond : ((fullBound d n m δ * (m + 1) ^ d : ℕ) : ℝ)
      + 2 ^ d * (Λ / ((1 - Λ) * κ * sp ^ 2)) ≤ N := by
    rw [← hK₀]; linarith only [hvol, hNge]
  have hΛ1 : Λ < 1 := by linarith only [hΛhalf']
  have hP := measureReal_rangeCard_le hd hδ0 hδlt hp₀ hhit hκ0 hsp0 h2m n N (θ := θ)
    hΛ1 hNcond herr1
  rw [← hΛ] at hP
  set err := softErr (n / (1 - δ)) Λ κ sp with herrdef
  -- the first term
  set q := (1 - Real.exp (-1)) * p₀ with hq
  have he1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hq0 : 0 ≤ q := mul_nonneg (by linarith only [he1]) hp₀
  have hℓ : (0 : ℝ) < ((2 * m ^ 2 : ℕ) : ℝ) := by
    have : 0 < 2 * m ^ 2 := by have := Nat.pos_of_neZero m; positivity
    exact_mod_cast this
  have hℓr : ((2 * m ^ 2 : ℕ) : ℝ) ≤ 2 * εb ^ 2 * r ^ 2 := by
    have h1 : (m : ℝ) ^ 2 ≤ (εb * r) ^ 2 := pow_le_pow_left₀ hmpos.le hm 2
    calc ((2 * m ^ 2 : ℕ) : ℝ) = 2 * (m : ℝ) ^ 2 := by push_cast; ring
      _ ≤ 2 * (εb * r) ^ 2 := by linarith only [h1]
      _ = 2 * εb ^ 2 * r ^ 2 := by ring
  have hT1 := first_term_le (n := (n : ℝ)) (K := K) hn.le hs0 hℓ hℓr hεb hts hq0 hθ.le hqθ hs3
  -- the second term
  have herr0 : 0 ≤ err := softErr_nonneg (by positivity) hΛ0 hΛ1 hκ0 hsp0
  have hx1 : Λ * (1 - err) ≤ 1 := by
    have : Λ * (1 - err) ≤ Λ := mul_le_of_le_one_right hΛ0 (by linarith only [herr0])
    linarith only [this, hΛhalf']
  have hCnt : (1 : ℝ) ≤ (((fullBound d n m δ + 1) * ((2 * t + 1) ^ d) ^ fullBound d n m δ : ℕ) : ℝ) := by
    have : 1 ≤ (fullBound d n m δ + 1) * ((2 * t + 1) ^ d) ^ fullBound d n m δ :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact_mod_cast this
  have hT2 := second_term_exp_le (a := a) (n := (n : ℝ)) (κ := κ) (θ := θ) (d := d) t rfl hx1
    hCnt htpos.le
  -- the main inequality
  set γ := (((m : ℝ) + 1) / m) ^ d / (1 - δ) with hγ
  have hγ1 : 1 ≤ γ := by
    rw [hγ, le_div_iff₀ hδ', one_mul]
    have h1 : (1 : ℝ) ≤ ((m : ℝ) + 1) / m := by rw [le_div_iff₀ hmpos]; linarith only
    have h2 := one_le_pow₀ (n := d) h1
    linarith only [h2, hδ0]
  have hγle : γ ≤ (1 + δ) / (1 - δ) := div_le_div_of_nonneg_right hmγ hδ'.le
  have hK₀γ : ((K₀ * (m + 1) ^ d : ℕ) : ℝ) ≤ γ * n := by
    push_cast
    have hmd : (0 : ℝ) < (m : ℝ) ^ d := by positivity
    calc (K₀ : ℝ) * ((m : ℝ) + 1) ^ d ≤ n / ((1 - δ) * (m : ℝ) ^ d) * ((m : ℝ) + 1) ^ d :=
          mul_le_mul_of_nonneg_right hK₀le (by positivity)
      _ = γ * n := by rw [hγ, div_pow]; field_simp
  have hNγ : (N : ℝ) ≤ γ * n + η * s + 1 := by linarith only [hNle, hK₀γ]
  have hmain := dv_main_lower hd ha.le hcl (by linarith only [he₀1]) hγ1 hη.le hs0 htpos.le htss
    (Nat.cast_nonneg n) hNpos hNγ (hΛlow N hNthrN) herr
  have hdv : dvConst d (a * (1 - δ) / (1 + δ)) ((1 - e₀) * cl)
      ≤ dvConst d (a / γ) ((1 - e₀) * cl) := by
    refine dvConst_mono (by positivity) ?_ (mul_nonneg (by linarith only [he₀1]) hcl)
    have hγ0 : 0 < γ := by linarith only [hγ1]
    have h1 : γ * (1 - δ) ≤ 1 + δ := by
      rw [hγ, div_mul_cancel₀ _ hδ'.ne']; exact hmγ
    rw [div_le_div_iff₀ (by linarith only [hδ0]) hγ0]
    calc a * (1 - δ) * γ = a * (γ * (1 - δ)) := by ring
      _ ≤ a * (1 + δ) := mul_le_mul_of_nonneg_left h1 ha.le
  have hcorr : a / γ * (η + 1 / s) ≤ ε / 8 := by
    have h1 : a / γ * (η + 1 / s) ≤ a * (η + 1 / s) :=
      mul_le_mul_of_nonneg_right (div_le_self ha.le hγ1) (by positivity)
    have h2 : a * (η + 1 / s) = a * η + a / s := by ring
    linarith only [h1, h2, haη, has]
  have hmain' : (K - ε / 4) * s ≤ a * n + t * Λ * (1 - err) := by
    have h : K - ε / 4 ≤ dvConst d (a / γ) ((1 - e₀) * cl) - a / γ * (η + 1 / s) := by
      linarith only [hK, hdv, hcorr]
    calc (K - ε / 4) * s = s * (K - ε / 4) := by ring
      _ ≤ s * (dvConst d (a / γ) ((1 - e₀) * cl) - a / γ * (η + 1 / s)) :=
          mul_le_mul_of_nonneg_left h hs0.le
      _ ≤ _ := hmain
  -- the error terms
  have hκθ : κ * (θ * t) = M * θ * s := by rw [hκ, hts]; field_simp
  have hr2 : 1 ≤ r ^ 2 := one_le_pow₀ hr1
  have hκM : κ ≤ M := by rw [hκ]; exact div_le_self hM.le hr2
  have hK₀max : (K₀ : ℝ) ≤ Kmax := by
    refine le_trans ?_ hKmax
    have hmd : (εb * r / 2) ^ d ≤ (m : ℝ) ^ d := pow_le_pow_left₀ (by positivity) hm2 d
    have hmd' : (εb * r / 2) ^ d = εb ^ d * s / 2 ^ d := by rw [div_pow, mul_pow, hrs]
    rw [hmd'] at hmd
    have hpos : 0 < (1 - δ) * (εb ^ d * s / 2 ^ d) := by positivity
    calc (K₀ : ℝ) ≤ n / ((1 - δ) * (m : ℝ) ^ d) := hK₀le
      _ ≤ C₀ * s / ((1 - δ) * (εb ^ d * s / 2 ^ d)) := by
          refine div_le_div₀ (by positivity) hn.le hpos ?_
          exact mul_le_mul_of_nonneg_left hmd hδ'.le
      _ = 2 ^ d * C₀ / ((1 - δ) * εb ^ d) := by field_simp
  have hlogC := log_count_le (d := d) (t := t) hK₀max
  have hL0 : 0 ≤ Real.log (2 * (t : ℝ) + 1) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ t := Nat.cast_nonneg t; linarith only [this])
  have hKmax0 : 0 ≤ Kmax := le_trans (Nat.cast_nonneg _) hK₀max
  have hdL : 0 ≤ (d : ℝ) * Real.log (2 * t + 1) := mul_nonneg hd0.le hL0
  have hErr : κ * (θ * t) + Real.log (((fullBound d n m δ + 1) * ((2 * t + 1) ^ d) ^
      fullBound d n m δ : ℕ) : ℝ) + κ / 2 + d * Real.log (2 * t + 1) / 2 ≤ ε / 4 * s := by
    rw [hκθ, ← hK₀]
    have hMθs : M * θ * s ≤ ε / 8 * s := mul_le_mul_of_nonneg_right hMθ hs0.le
    have hexpand : (Kmax + 2) * (1 + d * Real.log (2 * t + 1))
        = Kmax * (1 + d * Real.log (2 * t + 1)) + 2 + 2 * (d * Real.log (2 * t + 1)) := by ring
    linarith only [hMθs, hlogC, hκM, hlog, hexpand, hdL]
  have hexpo : -(a * n) - t * (Λ * (1 - err)) + κ * (θ * t)
      + Real.log (((fullBound d n m δ + 1) * ((2 * t + 1) ^ d) ^ fullBound d n m δ : ℕ) : ℝ)
      + κ / 2 + d * Real.log (2 * t + 1) / 2 ≤ -((K - ε / 2) * s) := by
    have e1 : t * (Λ * (1 - err)) = t * Λ * (1 - err) := by ring
    linarith only [e1, hmain', hErr]
  have hT2' := hT2.trans (Real.exp_le_exp.mpr hexpo)
  have hea : Real.exp (-(a * n)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ a * n := mul_nonneg ha.le (Nat.cast_nonneg n)
    linarith only [this])
  have hfirst : Real.exp (-(a * n)) * (2 * Real.exp ((n : ℝ) - (1 - Real.exp (-1)) * p₀ *
      ((θ * t - 3 * ((2 * m ^ 2 : ℕ) : ℝ)) / (2 * ((2 * m ^ 2 : ℕ) : ℝ)))))
      ≤ 2 * Real.exp (-((K + 1) * s)) :=
    (mul_le_of_le_one_left (mul_nonneg zero_le_two (Real.exp_pos _).le) hea).trans hT1
  have hKs : Real.exp (-((K + 1) * s)) ≤ Real.exp (-((K - ε / 2) * s)) := by
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    exact mul_le_mul_of_nonneg_right (by linarith only [hε]) hs0.le
  exact combine_two_terms hP hfirst hT2' hKs (Real.exp_pos _).le

/-- **The bound at a fixed time**, from the bound for each range size. -/
theorem log_rangeExp_le_of_terms (hd : 1 ≤ d) {a K ε s : ℝ} (ha : 0 ≤ a) {t : ℕ}
    (hterm : ∀ n : ℕ, Real.exp (-(a * n)) * (siteWalkLaw d 0).real
      {X | LatticeProb.rangeCard X t ≤ n} ≤ 3 * Real.exp (-((K - ε / 2) * s)))
    (hlogt : Real.log (3 * ((t : ℝ) + 2)) ≤ ε / 2 * s) :
    Real.log (rangeExp d a t) ≤ -((K - ε) * s) := by
  have hZ := rangeExp_pos hd ha t
  have hsum := rangeExp_le_sum hd ha t
  have hle : rangeExp d a t ≤ ((t : ℝ) + 2) * (3 * Real.exp (-((K - ε / 2) * s))) := by
    refine hsum.trans ?_
    calc ∑ n ∈ Finset.range (t + 2), Real.exp (-(a * n)) *
          (siteWalkLaw d 0).real {X | LatticeProb.rangeCard X t ≤ n}
        ≤ ∑ _n ∈ Finset.range (t + 2), 3 * Real.exp (-((K - ε / 2) * s)) :=
          Finset.sum_le_sum fun n _ => hterm n
      _ = ((t : ℝ) + 2) * (3 * Real.exp (-((K - ε / 2) * s))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  have hL := Real.log_le_log hZ hle
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
    Real.log_exp] at hL
  have e : Real.log ((t : ℝ) + 2) + Real.log 3 = Real.log (3 * ((t : ℝ) + 2)) := by
    rw [Real.log_mul (by norm_num) (by positivity)]; ring
  linarith only [hL, e, hlogt]

/-- The large range sizes: `e^{-an} ≤ e^{-(K+1)s}` when `a n ≥ (K+1) s`. -/
theorem large_n_bound (hd : 1 ≤ d) {a K ε s C₀ : ℝ} (ha : 0 < a) (hs : 0 ≤ s) (hε : 0 < ε)
    (hC₀ : K + 1 ≤ a * C₀) {t n : ℕ} (hn : C₀ * s ≤ n) :
    Real.exp (-(a * n)) * (siteWalkLaw d 0).real {X | LatticeProb.rangeCard X t ≤ n}
      ≤ 3 * Real.exp (-((K - ε / 2) * s)) := by
  have : NeZero d := ⟨by omega⟩
  have hP : (siteWalkLaw d 0).real {X | LatticeProb.rangeCard X t ≤ n} ≤ 1 := measureReal_le_one
  have hP0 : 0 ≤ (siteWalkLaw d 0).real {X | LatticeProb.rangeCard X t ≤ n} := measureReal_nonneg
  have h1 : Real.exp (-(a * n)) ≤ Real.exp (-((K - ε / 2) * s)) := by
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    have h2 : (K + 1) * s ≤ a * C₀ * s := mul_le_mul_of_nonneg_right hC₀ hs
    have h3 : a * C₀ * s ≤ a * n := by
      calc a * C₀ * s = a * (C₀ * s) := by ring
        _ ≤ a * n := mul_le_mul_of_nonneg_left hn ha.le
    have h4 : (K - ε / 2) * s ≤ (K + 1) * s := mul_le_mul_of_nonneg_right (by linarith) hs
    linarith
  calc Real.exp (-(a * n)) * (siteWalkLaw d 0).real {X | LatticeProb.rangeCard X t ≤ n}
      ≤ Real.exp (-(a * n)) * 1 := mul_le_mul_of_nonneg_left hP (Real.exp_pos _).le
    _ ≤ 3 * Real.exp (-((K - ε / 2) * s)) := by
        have := Real.exp_pos (-((K - ε / 2) * s))
        linarith

/-! ### Eventual facts -/

/-- `log (3 (t + 2)) ≤ c' t^{d/(d+2)}` eventually. -/
theorem eventually_log_le (hd : 1 ≤ d) {c' : ℝ} (hc' : 0 < c') :
    ∀ᶠ t : ℕ in atTop, Real.log (3 * ((t : ℝ) + 2)) ≤ c' * (t : ℝ) ^ ((d : ℝ) / (d + 2)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set ρ : ℝ := (d : ℝ) / (d + 2) with hρ
  have hρ0 : 0 < ρ := by positivity
  have ho := isLittleO_log_rpow_atTop hρ0
  have htend : Tendsto (fun t : ℕ => 3 * ((t : ℝ) + 2)) atTop atTop :=
    (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop).const_mul_atTop
      (by norm_num)
  have h9 : (0 : ℝ) < (9 : ℝ) ^ ρ := by positivity
  have hb := (ho.comp_tendsto htend).bound (c := c' / (9 : ℝ) ^ ρ) (by positivity)
  filter_upwards [hb, eventually_ge_atTop 1] with t ht ht1
  have ht1' : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  simp only [Function.comp, Real.norm_eq_abs] at ht
  have hx : 0 ≤ 3 * ((t : ℝ) + 2) := by positivity
  rw [abs_of_nonneg (Real.rpow_nonneg hx _)] at ht
  have h1 : (3 * ((t : ℝ) + 2)) ^ ρ ≤ (9 * (t : ℝ)) ^ ρ :=
    Real.rpow_le_rpow hx (by linarith) hρ0.le
  have h2 : (9 * (t : ℝ)) ^ ρ = (9 : ℝ) ^ ρ * (t : ℝ) ^ ρ :=
    Real.mul_rpow (by norm_num) (by positivity)
  calc Real.log (3 * ((t : ℝ) + 2)) ≤ |Real.log (3 * ((t : ℝ) + 2))| := le_abs_self _
    _ ≤ c' / (9 : ℝ) ^ ρ * (3 * ((t : ℝ) + 2)) ^ ρ := ht
    _ ≤ c' / (9 : ℝ) ^ ρ * ((9 : ℝ) ^ ρ * (t : ℝ) ^ ρ) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = c' * (t : ℝ) ^ ρ := by field_simp

/-- `((m + 1)/m)^d ≤ 1 + δ` for large `m`. -/
theorem exists_ratio_pow_le (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m → 0 < m → (((m : ℝ) + 1) / m) ^ d ≤ 1 + δ := by
  have h0 := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h1 : Tendsto (fun m : ℕ => (1 + 1 / (m : ℝ)) ^ d) atTop (𝓝 ((1 + 0) ^ d)) :=
    (tendsto_const_nhds.add h0).pow d
  simp only [add_zero, one_pow] at h1
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp (h1.eventually (gt_mem_nhds (by linarith :
    (1 : ℝ) < 1 + δ)))
  refine ⟨M₀, fun m hm hmpos => ?_⟩
  have hmr : (0 : ℝ) < m := by exact_mod_cast hmpos
  have : ((m : ℝ) + 1) / m = 1 + 1 / m := by field_simp
  rw [this]
  exact (hM₀ m hm).le

/-! ### The lower limit -/

/-- **The upper bound on the range moment at the scale `t^{d/(d+2)}`.** -/
theorem eventually_log_rangeExp_le (hd : 1 ≤ d) {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c)
    (hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ ((2 : ℝ) / d) * dirichletRate d n) atTop (𝓝 c))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop,
      Real.log (rangeExp d a t) ≤ -((dvConst d a c - ε) * (t : ℝ) ^ ((d : ℝ) / (d + 2))) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set K := dvConst d a c with hK
  have hK0 : 0 ≤ K := dvConst_nonneg ha.le hc
  obtain ⟨δ, e₀, ε₁, hδ0, hδ1, he₀0, he₀1, hε₁0, hKδ⟩ := exists_dvConst_params d ha hc hε
  set cl := max (c - ε₁) 0 with hcldef
  have hcl : 0 ≤ cl := le_max_right _ _
  have hδ' : 0 < 1 - δ := by linarith only [hδ1]
  -- the constants
  set C₀ := (K + 1) / a + 1 with hC₀def
  have hC₀ : 0 < C₀ := by positivity
  have hC₀K : K + 1 ≤ a * C₀ := by
    rw [hC₀def, mul_add, mul_div_cancel₀ _ ha.ne', mul_one]; linarith only [ha]
  set η := min 1 (ε / (16 * a)) with hηdef
  have hη : 0 < η := lt_min one_pos (by positivity)
  have haη : a * η ≤ ε / 16 := by
    have h := min_le_right 1 (ε / (16 * a))
    rw [← hηdef] at h
    calc a * η ≤ a * (ε / (16 * a)) := mul_le_mul_of_nonneg_left h ha.le
      _ = ε / 16 := by field_simp
  set A := C₀ / (1 - δ) + η with hA
  set B := C₀ / (1 - δ) with hB
  have hB0 : 0 ≤ B := by positivity
  have hsqA : 0 ≤ Real.sqrt A := Real.sqrt_nonneg _
  set σ := min 1 (e₀ / (2 * (2 * Real.sqrt A + B + 1))) with hσdef
  have hσ : 0 < σ := lt_min one_pos (by positivity)
  have hσ1 : σ ≤ 1 := min_le_left _ _
  have hσerr : 2 * σ * Real.sqrt (C₀ / (1 - δ) + η) + σ ^ 2 * (C₀ / (1 - δ)) ≤ e₀ / 2 := by
    rw [← hA, ← hB]
    have h1 : σ ≤ e₀ / (2 * (2 * Real.sqrt A + B + 1)) := min_le_right _ _
    have h2 : σ ^ 2 * B ≤ σ * B := by
      have : σ ^ 2 ≤ σ := by nlinarith
      exact mul_le_mul_of_nonneg_right this hB0
    have h3 : σ * (2 * Real.sqrt A + B + 1) ≤ e₀ / 2 := by
      rw [le_div_iff₀ (by positivity)] at h1
      linarith only [h1]
    nlinarith
  set P1 := 4 * (c + 1) * η ^ (-(2 : ℝ) / d) / e₀ with hP1
  set P2 := 2 ^ (d + 1) * (c + 1) * η ^ (-(2 : ℝ) / d) / (σ ^ 2 * η) with hP2
  have hP1pos : 0 < P1 := by positivity
  have hP2pos : 0 < P2 := by positivity
  set M := max P1 P2 + 1 with hMdef
  have hM : 0 < M := by positivity
  have hMP1 : P1 ≤ M := by rw [hMdef]; linarith only [le_max_left P1 P2]
  have hMP2 : P2 ≤ M := by rw [hMdef]; linarith only [le_max_right P1 P2]
  have hMerr : 2 * (c + 1) * η ^ (-(2 : ℝ) / d) / M ≤ e₀ / 2 := by
    rw [div_le_iff₀ hM]
    have : e₀ / 2 * P1 = 2 * (c + 1) * η ^ (-(2 : ℝ) / d) := by rw [hP1]; field_simp; ring
    nlinarith
  have hMN : 2 ^ (d + 1) * (c + 1) * η ^ (-(2 : ℝ) / d) / (M * σ ^ 2) ≤ η := by
    rw [div_le_iff₀ (by positivity)]
    have : η * (P2 * σ ^ 2) = 2 ^ (d + 1) * (c + 1) * η ^ (-(2 : ℝ) / d) := by
      rw [hP2]; field_simp
    have h2 : η * (P2 * σ ^ 2) ≤ η * (M * σ ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMP2 (by positivity)) hη.le
    linarith only [this, h2]
  set θ := ε / (8 * M) with hθdef
  have hθ : 0 < θ := by positivity
  have hMθ : M * θ ≤ ε / 8 := by rw [hθdef]; field_simp; linarith only
  obtain ⟨p₀, hp₀, m₀, hhit⟩ := exists_hit_prob_ge hd hδ0
  set q := (1 - Real.exp (-1)) * p₀ with hqdef
  have he1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hq : 0 < q := mul_pos (by linarith only [he1]) hp₀
  set εb := min 1 (Real.sqrt (q * θ / (4 * (C₀ + K + 2)))) with hεbdef
  have hεb : 0 < εb := lt_min one_pos (Real.sqrt_pos.mpr (by positivity))
  have hεb1 : εb ≤ 1 := min_le_left _ _
  have hqθ : C₀ + K + 2 ≤ (1 - Real.exp (-1)) * p₀ * θ / (4 * εb ^ 2) := by
    rw [← hqdef, le_div_iff₀ (by positivity)]
    have h1 : εb ≤ Real.sqrt (q * θ / (4 * (C₀ + K + 2))) := min_le_right _ _
    have h2 : εb ^ 2 ≤ q * θ / (4 * (C₀ + K + 2)) := by
      calc εb ^ 2 ≤ (Real.sqrt (q * θ / (4 * (C₀ + K + 2)))) ^ 2 :=
            pow_le_pow_left₀ hεb.le h1 2
        _ = q * θ / (4 * (C₀ + K + 2)) := Real.sq_sqrt (by positivity)
    rw [le_div_iff₀ (by positivity)] at h2
    linarith only [h2]
  set Kmax := 2 ^ d * C₀ / ((1 - δ) * εb ^ d) with hKmaxdef
  have hKmax0 : 0 ≤ Kmax := by positivity
  obtain ⟨M₀, hM₀⟩ := exists_ratio_pow_le d hδ0
  -- the thresholds in the volume
  have hev1 : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ ((2 : ℝ) / d) * dirichletRate d N ∈ Set.Ioo (c - ε₁) (c + 1) :=
    hlim.eventually (Ioo_mem_nhds (by linarith only [hε₁0]) (by linarith only))
  have hneg : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(2 : ℝ) / d)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by positivity : (0 : ℝ) < 2 / d)).comp
      tendsto_natCast_atTop_atTop
    refine h.congr fun n => ?_
    simp only [Function.comp, neg_div]
  have hev2 : ∀ᶠ N : ℕ in atTop, (c + 1) * (N : ℝ) ^ (-(2 : ℝ) / d) < 1 / 2 :=
    (hneg.const_mul (c + 1)).eventually (gt_mem_nhds (by rw [mul_zero]; norm_num))
  obtain ⟨Nthr, hNthr⟩ := eventually_atTop.mp ((hev1.and hev2).and (eventually_ge_atTop 1))
  have hNpq : ∀ N : ℕ, Nthr ≤ N →
      (N : ℝ) ^ ((2 : ℝ) / d) * (N : ℝ) ^ (-(2 : ℝ) / d) = 1 := by
    intro N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (hNthr N hN).2
    rw [← Real.rpow_add hNpos, neg_div, add_neg_cancel, Real.rpow_zero]
  have hΛup : ∀ N : ℕ, Nthr ≤ N → dirichletRate d N ≤ (c + 1) * (N : ℝ) ^ (-(2 : ℝ) / d) := by
    intro N hN
    have h1 := ((hNthr N hN).1.1).2
    have hq0 : 0 ≤ (N : ℝ) ^ (-(2 : ℝ) / d) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    calc dirichletRate d N = ((N : ℝ) ^ ((2 : ℝ) / d) * dirichletRate d N)
          * (N : ℝ) ^ (-(2 : ℝ) / d) := by
          rw [mul_comm ((N : ℝ) ^ ((2 : ℝ) / d)), mul_assoc, hNpq N hN, mul_one]
      _ ≤ (c + 1) * (N : ℝ) ^ (-(2 : ℝ) / d) := mul_le_mul_of_nonneg_right h1.le hq0
  have hΛlow : ∀ N : ℕ, Nthr ≤ N → cl * (N : ℝ) ^ (-(2 : ℝ) / d) ≤ dirichletRate d N := by
    intro N hN
    have h1 := ((hNthr N hN).1.1).1
    have hq0 : 0 ≤ (N : ℝ) ^ (-(2 : ℝ) / d) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    rcases le_total (c - ε₁) 0 with hce | hce
    · rw [hcldef, max_eq_right hce, zero_mul]; exact dirichletRate_nonneg d N
    · rw [hcldef, max_eq_left hce]
      calc (c - ε₁) * (N : ℝ) ^ (-(2 : ℝ) / d)
          ≤ ((N : ℝ) ^ ((2 : ℝ) / d) * dirichletRate d N) * (N : ℝ) ^ (-(2 : ℝ) / d) :=
            mul_le_mul_of_nonneg_right h1.le hq0
        _ = dirichletRate d N := by
            rw [mul_comm ((N : ℝ) ^ ((2 : ℝ) / d)), mul_assoc, hNpq N hN, mul_one]
  have hΛhalf : ∀ N : ℕ, Nthr ≤ N → dirichletRate d N ≤ 1 / 2 := fun N hN =>
    (hΛup N hN).trans (hNthr N hN).1.2.le
  -- the thresholds in time
  have hrt : Tendsto (fun t : ℕ => (t : ℝ) ^ ((1 : ℝ) / (d + 2))) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  have hst : Tendsto (fun t : ℕ => (t : ℝ) ^ ((d : ℝ) / (d + 2))) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  set R₁ : ℝ := max 1 ((2 * ((max m₀ M₀ : ℕ) + 1) + 2) / εb) with hR₁
  set S₁ : ℝ := max (max 2 (Nthr / η)) (max (3 * q / 2) (max (16 * a / ε)
    (16 * ((Kmax + 2) + M / 2) / ε))) with hS₁
  set c₁ : ℝ := ε / (16 * ((Kmax + 2) * d + 1)) with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  filter_upwards [hrt.eventually_ge_atTop R₁, hst.eventually_ge_atTop S₁,
    eventually_log_le hd hc₁0, eventually_ge_atTop 1] with t hrR hsS hlogc ht1
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht1
  set r := (t : ℝ) ^ ((1 : ℝ) / (d + 2)) with hrdef
  set s := (t : ℝ) ^ ((d : ℝ) / (d + 2)) with hsdef
  obtain ⟨hrs, hts, hsr⟩ := scale_facts hd htpos
  rw [← hrdef, ← hsdef] at hrs hts hsr
  have htss : (t : ℝ) * s ^ (-(2 : ℝ) / d) = s := mul_rpow_scale hd htpos
  have hr1 : 1 ≤ r := le_trans (le_max_left _ _) hrR
  have hr0 : 0 < r := by linarith only [hr1]
  have hs2 : 2 ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hsS
  have hs0 : 0 < s := by linarith only [hs2]
  have hsN : (Nthr : ℝ) / η ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hsS
  have hsq : 3 * q / 2 ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hsS
  have hsa : 16 * a / ε ≤ s :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hsS
  have hsK : 16 * ((Kmax + 2) + M / 2) / ε ≤ s :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hsS
  -- the box side
  have hεbr : 2 * ((max m₀ M₀ : ℕ) + 1) + 2 ≤ εb * r := by
    have h := le_trans (le_max_right _ _) hrR
    rw [div_le_iff₀ hεb] at h
    linarith only [h]
  set m : ℕ := ⌊εb * r⌋₊ with hmdef
  have hm : (m : ℝ) ≤ εb * r := Nat.floor_le (by positivity)
  have hmlb : εb * r - 1 < m := by
    have := Nat.lt_floor_add_one (εb * r); rw [← hmdef] at this; linarith only [this]
  have hm2 : εb * r / 2 ≤ m := by linarith only [hmlb, hεbr]
  have hmax : ((max m₀ M₀ : ℕ) : ℝ) < m := by linarith only [hmlb, hεbr]
  have hmax' : max m₀ M₀ < m := by exact_mod_cast hmax
  have hmm₀ : m₀ ≤ m := le_trans (le_max_left _ _) hmax'.le
  have hmM₀ : M₀ ≤ m := le_trans (le_max_right _ _) hmax'.le
  have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hmax'
  have : NeZero m := ⟨by omega⟩
  have hmγ := hM₀ m hmM₀ hmpos
  have h2m : 2 * m ^ 2 ≤ t := by
    have h1 : (m : ℝ) ≤ r := hm.trans (mul_le_of_le_one_left hr0.le hεb1)
    have h2 : (2 * m ^ 2 : ℝ) ≤ t := by
      have h3 : (m : ℝ) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2
      have h4 : 2 * r ^ 2 ≤ r ^ 2 * s := by
        calc 2 * r ^ 2 = r ^ 2 * 2 := by ring
          _ ≤ r ^ 2 * s := mul_le_mul_of_nonneg_left hs2 (by positivity)
      rw [hts]; linarith only [h3, h4]
    exact_mod_cast h2
  have hNthr' : (Nthr : ℝ) ≤ η * s := by
    rw [div_le_iff₀ hη] at hsN; linarith only [hsN]
  have has : a / s ≤ ε / 16 := by
    rw [div_le_iff₀ hs0]; rw [div_le_iff₀ hε] at hsa; linarith only [hsa]
  have hlog2 : Real.log (2 * (t : ℝ) + 1) ≤ Real.log (3 * ((t : ℝ) + 2)) :=
    Real.log_le_log (by positivity) (by linarith only [htpos])
  have hlog : (Kmax + 2) * (1 + d * Real.log (2 * t + 1)) + M / 2 ≤ ε / 8 * s := by
    have h1 : (Kmax + 2) + M / 2 ≤ ε / 16 * s := by
      rw [div_le_iff₀ hε] at hsK; linarith only [hsK]
    have hL0 : 0 ≤ Real.log (2 * (t : ℝ) + 1) := Real.log_nonneg (by linarith only [htpos])
    have h2 : (Kmax + 2) * (d * Real.log (2 * t + 1)) ≤ (Kmax + 2) * (d * (c₁ * s)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hlog2.trans hlogc) hd0.le)
        (by linarith only [hKmax0])
    have h3 : (Kmax + 2) * (d * (c₁ * s)) ≤ ε / 16 * s := by
      have : (Kmax + 2) * d * c₁ ≤ ε / 16 := by
        have hX : 0 < (Kmax + 2) * d + 1 := by positivity
        have hfrac : ((Kmax + 2) * d) / ((Kmax + 2) * d + 1) ≤ 1 :=
          div_le_one_of_le₀ (by linarith only) hX.le
        calc (Kmax + 2) * d * c₁ = ε / 16 * (((Kmax + 2) * d) / ((Kmax + 2) * d + 1)) := by
              rw [hc₁]; field_simp
          _ ≤ ε / 16 * 1 := mul_le_mul_of_nonneg_left hfrac (by positivity)
          _ = ε / 16 := mul_one _
      calc (Kmax + 2) * (d * (c₁ * s)) = ((Kmax + 2) * d * c₁) * s := by ring
        _ ≤ ε / 16 * s := mul_le_mul_of_nonneg_right this hs0.le
    have e : (Kmax + 2) * (1 + d * Real.log (2 * t + 1))
        = (Kmax + 2) + (Kmax + 2) * (d * Real.log (2 * t + 1)) := by ring
    linarith only [h1, h2, h3, e]
  have hlogt : Real.log (3 * ((t : ℝ) + 2)) ≤ ε / 2 * s := by
    have : c₁ ≤ ε / 2 := by
      have hX : (1 : ℝ) ≤ (Kmax + 2) * d + 1 := by
        have : 0 ≤ (Kmax + 2) * d := by positivity
        linarith only [this]
      rw [hc₁]
      calc ε / (16 * ((Kmax + 2) * d + 1)) ≤ ε / (16 * 1) :=
            div_le_div_of_nonneg_left hε.le (by norm_num) (by linarith only [hX])
        _ ≤ ε / 2 := by linarith only [hε]
    exact hlogc.trans (mul_le_mul_of_nonneg_right this hs0.le)
  -- each range size
  have hterm : ∀ n : ℕ, Real.exp (-(a * n)) * (siteWalkLaw d 0).real
      {X | LatticeProb.rangeCard X t ≤ n} ≤ 3 * Real.exp (-((K - ε / 2) * s)) := by
    intro n
    by_cases hn : (n : ℝ) < C₀ * s
    · exact small_n_bound hd ha hc hε hδ0 hδ1 hp₀.le (hhit m hmm₀) he₀1 hcl hη hσ hM hθ hεb hC₀
        hKδ haη hσerr hMerr hMN hMθ hqθ hΛlow hΛup hΛhalf hr1 hs0 hrs hts htss hsr hm hm2 hmγ
        h2m hNthr' hsq has le_rfl hlog n hn
    · exact large_n_bound hd ha hs0.le hε hC₀K (le_of_not_gt hn)
  exact log_rangeExp_le_of_terms hd ha.le hterm hlogt

end Parking

end
