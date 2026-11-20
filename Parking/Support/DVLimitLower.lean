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

end Parking

end
