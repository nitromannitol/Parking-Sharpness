/-
Theorem 7.2 of parking.tex, frozen.  `parking.tex:1403-1416` (label
`thm:upper`):

  "Let $\eta=(\eta(x))_{x\in\Z^d}$ be independent copies of a nonconstant
   integer-valued $\eta(0)$ which has mean zero and satisfies
   $\E e^{\theta|\eta(0)|}<\infty$ for some $\theta>0$.  There is $C<\infty$
   such that, for every $n\geq2$, $\E U_n(0)\leq C(\E u_n(0)+\log n)$.  More
   generally, for every $r\geq2$,
   $(\E U_n(0)^r)^{1/r}\leq C(\E u_n(0)+\sqrt r\,\|g_n\|_2+r\max_xg_n(x)
     +r(n+1)^{2/r}\kappa_d(n))$."

The moment bound is stated for `n ≥ 1`, the range in which the proof of its
first step works; the paper's `n ≥ 2` governs the first display.  The moments
on the left are asserted finite alongside the bounds, which is what
`eq:apriori-finite` gives, so that an undefined integral cannot satisfy them
through its junk value.  The four
results the proof quotes without proving them here enter as explicit
hypotheses: the growth of the mean sandpile odometer, the martingale moment
inequality, the concentration of the sandpile odometer, and the asymptotics of
the two Green norms of `eq:green-norms`, which Steps 2 and 3 read.
-/
import Parking.External.SandpileGrowth
import Parking.External.Bernstein
import Parking.External.UConcentration
import Parking.External.GreenNorms
import Parking.Support.UpperTarget

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.upper (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration)
    (hGreenNorms : Parking.External.GreenNorms)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    ∃ C : ℝ, 0 < C ∧
      (∀ n : ℕ, 2 ≤ n → Integrable (fun ω => (Parking.U ω n 0 : ℝ)) (Parking.law d ν) ∧
        Parking.meanU (Parking.law d ν) n
          ≤ C * (Parking.meanu (Parking.law d ν) n + Real.log n)) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 2 ≤ r →
        Integrable (fun ω => (Parking.U ω n 0 : ℝ) ^ r) (Parking.law d ν) ∧
        (∫ ω, (Parking.U ω n 0 : ℝ) ^ r ∂(Parking.law d ν)) ^ (1 / r)
          ≤ C * (Parking.meanu (Parking.law d ν) n
              + Real.sqrt r * Parking.l2Norm (Parking.green d n)
              + r * Parking.greenMax d n
              + r * ((n : ℝ) + 1) ^ (2 / r) * Parking.kappa d n))
-- FROZEN-STATEMENT-END
:= by
  haveI := hν.prob
  obtain ⟨Ct, hCt, ht⟩ :=
    Parking.exists_target hd hBernstein hConcentration hGrowth hGreenNorms ν hν
  obtain ⟨Cm, hCm, hm⟩ := Parking.exists_critical_moment hd hBernstein hConcentration ν hν
  refine ⟨Ct + Cm, by linarith, fun n hn => ⟨(ht n hn).1, ?_⟩,
    fun n hn r hr => ⟨(hm n hn r hr).1, ?_⟩⟩
  · have hb : (0 : ℝ) ≤ Parking.meanu (Parking.law d ν) n + Real.log n := by
      have h1 : (0 : ℝ) ≤ Parking.meanu (Parking.law d ν) n :=
        integral_nonneg fun ω => Parking.uOf_nonneg ω n 0
      have h2 : (0 : ℝ) ≤ Real.log n := le_of_lt (Parking.log_pos_of_two_le hn)
      linarith
    refine (ht n hn).2.trans ?_
    nlinarith [mul_nonneg hCm.le hb]
  · have hr0 : (0 : ℝ) < r := by linarith
    have hb : (0 : ℝ) ≤ Parking.meanu (Parking.law d ν) n
        + Real.sqrt r * Parking.l2Norm (Parking.green d n)
        + r * Parking.greenMax d n
        + r * ((n : ℝ) + 1) ^ (2 / r) * Parking.kappa d n := by
      have h1 : (0 : ℝ) ≤ Parking.meanu (Parking.law d ν) n :=
        integral_nonneg fun ω => Parking.uOf_nonneg ω n 0
      have h2 : (0 : ℝ) ≤ Real.sqrt r * Parking.l2Norm (Parking.green d n) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have h3 : (0 : ℝ) ≤ r * Parking.greenMax d n :=
        mul_nonneg (le_of_lt hr0) (Real.iSup_nonneg fun x => Parking.green_nonneg n x)
      have h4 : (0 : ℝ) ≤ r * ((n : ℝ) + 1) ^ (2 / r) * Parking.kappa d n := by
        have h5 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (2 / r) := by
          refine Real.rpow_nonneg ?_ _
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        exact mul_nonneg (mul_nonneg (le_of_lt hr0) h5) (Parking.kappa_nonneg d n)
      linarith
    refine (hm n hn r hr).2.trans ?_
    nlinarith [mul_nonneg hCt.le hb]
