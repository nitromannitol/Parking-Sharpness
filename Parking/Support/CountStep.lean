/-
The arithmetic of Step 2 at a single site.

Step 2 of `lem:product` (`parking.tex:2367-2394`) bounds the conditional
covariance at a site carrying `k` particles by `2k(f(k) - f(k-1))` and then
compares the mean of that bound with `Cov(f(Y), Y)` through the summation by
parts of `Support/CovParts.lean`.  Only the values `k ≥ 1` contribute, and there
the weight `k` is exactly the weight the summation by parts produces, so the
comparison is term by term.
-/
import Parking.Support.CovParts

open MeasureTheory

noncomputable section

namespace Parking

variable {ν : Measure ℤ} [IsProbabilityMeasure ν]

/-- **The mean of the one-site bound of Step 2 is at most twice the covariance
of `f(Y)` with `Y`.** -/
theorem integral_count_step_le {f : ℤ → ℝ}
    (hfmono : Monotone f) (hfbdd : ∀ k : ℤ, |f k| ≤ 1)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k, (k : ℝ) ∂ν ≤ 0) :
    ∫ k, ((k.toNat : ℝ) * (2 * (f k - f (k - 1)))) ∂ν
      ≤ 2 * cov ν f (fun k : ℤ => (k : ℝ)) := by
  have hstep := tsum_step_le_cov (ν := ν) (B := 1) hfmono hfbdd hint hmean
  have hgb : ∀ k : ℤ, |(k.toNat : ℝ) * (2 * (f k - f (k - 1)))| ≤ 4 * |(k : ℝ)| := by
    intro k
    have h1 := hfbdd k
    have h2 := hfbdd (k - 1)
    have h3 : |(k.toNat : ℝ)| ≤ |(k : ℝ)| := by
      rcases le_or_gt 0 k with hk | hk
      · have hk' : ((k.toNat : ℤ) : ℝ) = (k : ℝ) := by
          exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hk)
        rw [show ((k.toNat : ℝ)) = ((k.toNat : ℤ) : ℝ) by push_cast; ring, hk']
      · have hk0 : k.toNat = 0 := Int.toNat_of_nonpos (by omega)
        rw [hk0]
        simp
    have habs : |f k - f (k - 1)| ≤ 2 := by
      have := abs_sub (f k) (f (k - 1))
      calc |f k - f (k - 1)| ≤ |f k| + |f (k - 1)| := abs_sub _ _
        _ ≤ 2 := by linarith
    have h4 : |2 * (f k - f (k - 1))| ≤ 4 := by
      rw [abs_mul, abs_two]
      linarith
    calc |(k.toNat : ℝ) * (2 * (f k - f (k - 1)))|
        = |(k.toNat : ℝ)| * |2 * (f k - f (k - 1))| := abs_mul _ _
      _ ≤ |(k : ℝ)| * 4 := mul_le_mul h3 h4 (abs_nonneg _) (abs_nonneg _)
      _ = 4 * |(k : ℝ)| := by ring
  have hgi : Integrable (fun k : ℤ => (k.toNat : ℝ) * (2 * (f k - f (k - 1)))) ν := by
    refine Integrable.mono' (hint.const_mul 4)
      (measurable_int_fun _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => ?_)
    simpa [Real.norm_eq_abs] using hgb k
  have hpt : ∀ k : ℤ, ν.real {k} • ((k.toNat : ℝ) * (2 * (f k - f (k - 1))))
      = 2 * (if 1 ≤ k then (f k - f (k - 1)) * ((k : ℝ) * (ν {k}).toReal) else 0) := by
    intro k
    by_cases hk : 1 ≤ k
    · have hk0 : ((k.toNat : ℝ)) = (k : ℝ) := by
        have : ((k.toNat : ℤ) : ℝ) = (k : ℝ) :=
          congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg (by omega))
        rw [show ((k.toNat : ℝ)) = ((k.toNat : ℤ) : ℝ) by push_cast; ring, this]
      rw [if_pos hk, smul_eq_mul, measureReal_def, hk0]
      ring
    · have hk0 : k.toNat = 0 := Int.toNat_of_nonpos (by omega)
      rw [if_neg hk, smul_eq_mul, hk0]
      simp
  rw [integral_countable hgi, tsum_congr hpt, (hstep.1).tsum_mul_left 2]
  exact mul_le_mul_of_nonneg_left hstep.2 (by norm_num)

end Parking

end
