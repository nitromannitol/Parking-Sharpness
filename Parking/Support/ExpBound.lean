/-
Elementary bounds on the exponential used to differentiate under the integral
sign in Step 3 of `lem:product` (`parking.tex:2409-2412`).

The two increments of the tilt are compared through `Real.add_one_le_exp`:
`abs_exp_sub_exp_le` is the mean value bound `|e^a - e^b| ≤ |a - b| e^{a ∨ b}`
without the mean value theorem, and `mul_exp_le_exp_div` turns the factor of
`x` that differentiating produces into a slightly larger exponential.  Together
they give `abs_exp_sub_exp_bound`, the dominating function that makes the
difference quotients of `s ↦ e^{sx}` integrable uniformly for `s` in `[0, s₁]`
whenever `s₁` is below the threshold `θ` of the exponential moment.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

namespace Parking

/-- **The increment of the exponential.**  `|e^a - e^b| ≤ |a - b| e^{a ∨ b}`. -/
theorem abs_exp_sub_exp_le (a b : ℝ) :
    |Real.exp a - Real.exp b| ≤ |a - b| * Real.exp (max a b) := by
  rcases le_total b a with h | h
  · rw [max_eq_left h]
    have h1 : Real.exp b ≤ Real.exp a := Real.exp_le_exp.mpr h
    have h2 : (b - a) + 1 ≤ Real.exp (b - a) := Real.add_one_le_exp (b - a)
    have h3 : Real.exp (b - a) * Real.exp a = Real.exp b := by
      rw [← Real.exp_add]; ring_nf
    have h4 : (0 : ℝ) < Real.exp a := Real.exp_pos a
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ Real.exp a - Real.exp b),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b)]
    nlinarith [h2, h3, h4]
  · rw [max_eq_right h]
    have h1 : Real.exp a ≤ Real.exp b := Real.exp_le_exp.mpr h
    have h2 : (a - b) + 1 ≤ Real.exp (a - b) := Real.add_one_le_exp (a - b)
    have h3 : Real.exp (a - b) * Real.exp b = Real.exp a := by
      rw [← Real.exp_add]; ring_nf
    have h4 : (0 : ℝ) < Real.exp b := Real.exp_pos b
    rw [abs_of_nonpos (by linarith : Real.exp a - Real.exp b ≤ 0),
      abs_of_nonpos (by linarith : a - b ≤ 0)]
    nlinarith [h2, h3, h4]

/-- **A factor of `x` costs an arbitrarily small increase of the rate.** -/
theorem mul_exp_le_exp_div {x s t : ℝ} (hst : s < t) :
    x * Real.exp (s * x) ≤ Real.exp (t * x) / (t - s) := by
  have hts : (0 : ℝ) < t - s := by linarith
  have h1 : (t - s) * x + 1 ≤ Real.exp ((t - s) * x) := Real.add_one_le_exp ((t - s) * x)
  have h2 : Real.exp ((t - s) * x) * Real.exp (s * x) = Real.exp (t * x) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : (0 : ℝ) < Real.exp (s * x) := Real.exp_pos (s * x)
  rw [le_div_iff₀ hts]
  nlinarith [h1, h2, h3, Real.exp_pos ((t - s) * x)]

/-- **The dominating bound for the difference quotients of the tilt.**  For
`0 ≤ lam, s ≤ s₁ < θ` the increment of `s ↦ e^{sx}` is at most `|s - lam|`
times a function of `x` alone that is integrable whenever `e^{θ x}` and `|x|`
are. -/
theorem abs_exp_sub_exp_bound {θ s₁ lam s : ℝ} (h1 : s₁ < θ) (hlam0 : 0 ≤ lam)
    (hlam1 : lam ≤ s₁) (hs0 : 0 ≤ s) (hs1 : s ≤ s₁) (x : ℝ) :
    |Real.exp (s * x) - Real.exp (lam * x)|
      ≤ |s - lam| * (Real.exp (θ * x) / (θ - s₁) + |x|) := by
  have hbase := abs_exp_sub_exp_le (s * x) (lam * x)
  have hfac : |s * x - lam * x| = |s - lam| * |x| := by rw [← sub_mul, abs_mul]
  have habs : (0 : ℝ) ≤ |s - lam| := abs_nonneg _
  have hts : (0 : ℝ) < θ - s₁ := by linarith
  rcases le_or_gt 0 x with hx | hx
  · have hmax : max (s * x) (lam * x) ≤ s₁ * x :=
      max_le (mul_le_mul_of_nonneg_right hs1 hx) (mul_le_mul_of_nonneg_right hlam1 hx)
    have hexp : Real.exp (max (s * x) (lam * x)) ≤ Real.exp (s₁ * x) := Real.exp_le_exp.mpr hmax
    have hE2 : x * Real.exp (s₁ * x) ≤ Real.exp (θ * x) / (θ - s₁) := mul_exp_le_exp_div h1
    have hxabs : |x| = x := abs_of_nonneg hx
    have hstep : |s * x - lam * x| * Real.exp (max (s * x) (lam * x))
        ≤ |s - lam| * (x * Real.exp (s₁ * x)) := by
      rw [hfac, hxabs, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hx) habs
    nlinarith [hbase, hstep, hE2, habs, abs_nonneg x]
  · have hs' : s * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs0 (le_of_lt hx)
    have hl' : lam * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam0 (le_of_lt hx)
    have hexp : Real.exp (max (s * x) (lam * x)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (max_le hs' hl')
    have hpos : (0 : ℝ) ≤ Real.exp (θ * x) / (θ - s₁) :=
      div_nonneg (Real.exp_nonneg _) (le_of_lt hts)
    have hstep : |s * x - lam * x| * Real.exp (max (s * x) (lam * x)) ≤ |s - lam| * |x| := by
      rw [hfac]
      exact mul_le_of_le_one_right (mul_nonneg habs (abs_nonneg x)) hexp
    nlinarith [hbase, hstep, habs, hpos, abs_nonneg x]

end Parking

end
