/-
The range quantities of `thm:subcritical-tail` (`parking.tex:2497-2502`).

The upper bound of `thm:subcritical` and the lower bound of `lem:range-lower`
are both averages over the walk alone: the first of `e^{-a|R_t|}`, the second of
`q^{|R_t|-1}` with `q = \P(\eta(0)\geq0)`.  Writing `q = e^{-a_1}` turns the
second into the first, so the Donsker-Varadhan estimate applies to both.  The
positivity of `q` and of `\E\eta(0)^+` comes from `\P(\eta(0)>0)>0`, and `q<1`,
which is what makes `a_1` positive, comes from the negative mean.
-/
import Parking.Support.Near
import Parking.Support.RangeHitting
import Parking.Support.RangeLower
import Parking.Support.Cov

open MeasureTheory

noncomputable section

namespace Parking

variable {d : ℕ}

/-- The integrand of `rangeExp` is integrable against the walk law. -/
theorem integrable_rangeExpFun (hd : 1 ≤ d) {a : ℝ} (ha : 0 ≤ a) (t : ℕ) :
    Integrable (fun p : ℕ → Fin d × Bool =>
      Real.exp (-(a * (rangeCard (0 : Site d) p t : ℝ)))) (walkLaw d) := by
  haveI : IsProbabilityMeasure (walkLaw d) := walkLaw_isProbability (d := d) hd
  have hmeas : Measurable fun p : ℕ → Fin d × Bool =>
      Real.exp (-(a * ((rangeCard (0 : Site d) p t : ℝ)))) :=
    (Measurable.of_discrete (β := ℝ) (f := fun n : ℕ => Real.exp (-(a * (n : ℝ))))).comp
      (measurable_rangeCard (0 : Site d) t)
  refine (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_one_iff.2
    (by nlinarith [show (0:ℝ) ≤ (rangeCard (0 : Site d) p t : ℝ) from Nat.cast_nonneg _, ha])

/-- **`E_0 e^{-a|R_t|}` is positive**, because the range is at most `t+1`. -/
theorem rangeExp_pos (hd : 1 ≤ d) {a : ℝ} (ha : 0 ≤ a) (t : ℕ) :
    0 < rangeExp d a t := by
  haveI : IsProbabilityMeasure (walkLaw d) := walkLaw_isProbability (d := d) hd
  have hlb : ∀ p : ℕ → Fin d × Bool,
      Real.exp (-(a * ((t : ℝ) + 1))) ≤ Real.exp (-(a * (rangeCard (0 : Site d) p t : ℝ))) := by
    intro p
    refine Real.exp_le_exp.2 ?_
    have h1 : (rangeCard (0 : Site d) p t : ℝ) ≤ (t : ℝ) + 1 := by
      exact_mod_cast rangeCard_le_succ (0 : Site d) p t
    nlinarith [ha, h1]
  have h2 : ∫ _p : ℕ → Fin d × Bool, Real.exp (-(a * ((t : ℝ) + 1))) ∂(walkLaw d)
      ≤ rangeExp d a t := by
    rw [rangeExp]
    exact integral_mono (integrable_const _) (integrable_rangeExpFun hd ha t) hlb
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h2
  exact lt_of_lt_of_le (Real.exp_pos _) h2

/-- **`E_0 e^{-a|R_t|}` decreases in `a`.** -/
theorem rangeExp_anti (hd : 1 ≤ d) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (t : ℕ) :
    rangeExp d b t ≤ rangeExp d a t := by
  have hb : (0 : ℝ) ≤ b := le_trans ha hab
  rw [rangeExp, rangeExp]
  refine integral_mono (integrable_rangeExpFun hd hb t) (integrable_rangeExpFun hd ha t) ?_
  intro p
  refine Real.exp_le_exp.2 ?_
  have hn : (0 : ℝ) ≤ (rangeCard (0 : Site d) p t : ℝ) := Nat.cast_nonneg _
  nlinarith [hab, hn]

/-- **The chance of a nonnegative count is positive** when the law charges the
positive integers. -/
theorem nonnegProb_pos {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hpos : 0 < ν (Set.Ioi (0 : ℤ))) : 0 < (ν {j : ℤ | 0 ≤ j}).toReal := by
  have hsub : Set.Ioi (0 : ℤ) ⊆ {j : ℤ | 0 ≤ j} := by
    intro x hx
    simp only [Set.mem_setOf_eq]
    exact le_of_lt hx
  have hle : ν (Set.Ioi (0 : ℤ)) ≤ ν {j : ℤ | 0 ≤ j} := measure_mono hsub
  exact ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le hpos hle)) (measure_ne_top ν _)

/-- **A law of negative mean charges the negative integers**, so the chance of a
nonnegative count is below one. -/
theorem nonnegProb_lt_one {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hmean : ∫ k, (k : ℝ) ∂ν < 0) : (ν {j : ℤ | 0 ≤ j}).toReal < 1 := by
  by_contra hcon
  push Not at hcon
  have hms : MeasurableSet {j : ℤ | 0 ≤ j} := MeasurableSet.of_discrete
  have hone : ν {j : ℤ | 0 ≤ j} = 1 := by
    have hle : ν {j : ℤ | 0 ≤ j} ≤ 1 := prob_le_one
    have hle' : (ν {j : ℤ | 0 ≤ j}).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (by simp) hle
    exact (ENNReal.toReal_eq_one_iff _).1 (le_antisymm hle' hcon)
  have hcompl : ν ({j : ℤ | 0 ≤ j}ᶜ) = 0 := by
    rw [prob_compl_eq_one_sub hms, hone, tsub_self]
  have hae : (0 : ℤ → ℝ) ≤ᵐ[ν] fun k : ℤ => (k : ℝ) := by
    rw [Filter.EventuallyLE, ae_iff]
    refine measure_mono_null (fun k hk => ?_) hcompl
    simp only [Pi.zero_apply, Set.mem_setOf_eq, not_le] at hk
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
    exact_mod_cast hk
  have hge : 0 ≤ ∫ k, (k : ℝ) ∂ν := integral_nonneg_of_ae hae
  linarith

/-- **`E\eta(0)^+>0`** when the law charges the positive integers. -/
theorem integral_posPart_pos {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hpos : 0 < ν (Set.Ioi (0 : ℤ))) :
    0 < ∫ k, max (k : ℝ) 0 ∂ν := by
  have hintp : Integrable (fun k : ℤ => max (k : ℝ) 0) ν := by
    refine hint.mono' (measurable_int_fun (fun k : ℤ => max (k : ℝ) 0)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hae : (0 : ℤ → ℝ) ≤ᵐ[ν] fun k : ℤ => max (k : ℝ) 0 :=
    Filter.Eventually.of_forall fun k => le_max_right _ _
  rw [integral_pos_iff_support_of_nonneg_ae hae hintp]
  have hsupp : Function.support (fun k : ℤ => max (k : ℝ) 0) = Set.Ioi (0 : ℤ) := by
    ext k
    simp only [Function.mem_support, ne_eq, Set.mem_Ioi]
    constructor
    · intro h
      by_contra hk
      push Not at hk
      exact h (max_eq_right (by exact_mod_cast hk))
    · intro h hz
      have h1 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast h
      rw [max_eq_left (le_of_lt h1)] at hz
      linarith
  rw [hsupp]
  exact hpos

/-- **The range exponential at `-\log q` is below the power integral of
`lem:range-lower`.** -/
theorem rangeExp_le_powIntegral (hd : 1 ≤ d) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (t : ℕ)
    (hIR : Integrable
      (fun p : ℕ → Fin d × Bool => q ^ (rangeCard (0 : Site d) p t - 1)) (walkLaw d)) :
    rangeExp d (-Real.log q) t
      ≤ ∫ p, q ^ (rangeCard (0 : Site d) p t - 1) ∂(walkLaw d) := by
  have ha : 0 ≤ -Real.log q := by
    have h := Real.log_nonpos (le_of_lt hq0) hq1
    linarith
  have hpt : ∀ p : ℕ → Fin d × Bool,
      Real.exp (-(-Real.log q * (rangeCard (0 : Site d) p t : ℝ)))
        ≤ q ^ (rangeCard (0 : Site d) p t - 1) := by
    intro p
    have heq : Real.exp (-(-Real.log q * (rangeCard (0 : Site d) p t : ℝ)))
        = q ^ (rangeCard (0 : Site d) p t) := by
      rw [show -(-Real.log q * (rangeCard (0 : Site d) p t : ℝ))
            = ((rangeCard (0 : Site d) p t : ℕ) : ℝ) * Real.log q from by ring,
        Real.exp_nat_mul, Real.exp_log hq0]
    rw [heq]
    exact pow_le_pow_of_le_one (le_of_lt hq0) hq1 (Nat.sub_le _ 1)
  rw [rangeExp]
  exact integral_mono (integrable_rangeExpFun hd ha t) hIR hpt

end Parking

end
