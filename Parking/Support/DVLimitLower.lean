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

end Parking

end
