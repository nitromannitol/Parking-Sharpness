/-
Theorem 1.2 of parking.tex, frozen.  `parking.tex:159-168` (label `thm:master`):

  "Let $\eta=(\eta(x))_{x\in\Z^d}$ have i.i.d. integer-valued coordinates.
   Suppose that $\eta(0)$ is nonconstant, $\E\eta(0)=0$, and
   $\E e^{\theta|\eta(0)|}<\infty$ for some $\theta>0$.  Then there are
   $0<c\leq C<\infty$ such that, for every $n\geq2$,
   $c(\E u_n(0)+\log n)\leq\E U_n(0)\leq C(\E u_n(0)+\log n)$."

The two constants are bound before `n`, so they are genuine constants.  Only
the upper bound uses the exponential moment, as the paper notes after the
statement; both directions are frozen together because the paper states them
as one display.  The upper bound is `thm:upper`, whose proof quotes the growth
of the mean sandpile odometer, the martingale moment inequality and the
concentration estimate; all three enter as explicit hypotheses.

The results the proof quotes without proving them here enter as explicit
hypotheses.  The upper bound is the first display of `thm:upper`, so this node
carries every external that `thm:upper` carries, the collected Green estimates
among them.
-/
import Parking.External.SandpileGrowth
import Parking.External.Bernstein
import Parking.External.UConcentration
import Parking.External.GreenNorms
import Parking.Frozen.CorCritical
import Parking.Support.MasterChain

open MeasureTheory ProbabilityTheory

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.master (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration)
    (hGreenNorms : Parking.External.GreenNorms)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hprob : IsProbabilityMeasure ν)
    (hnonconst : ∀ k : ℤ, ν {k} ≠ 1) (hmean : ∫ k, (k : ℝ) ∂ν = 0)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * (Parking.meanu (Parking.law d ν) n + Real.log n) ≤ Parking.meanU (Parking.law d ν) n ∧
        Parking.meanU (Parking.law d ν) n ≤ C * (Parking.meanu (Parking.law d ν) n + Real.log n)
-- FROZEN-STATEMENT-END
:= by
  exact Parking.master_of_cor_critical Parking.Frozen.cor_critical
    hGrowth hBernstein hConcentration hGreenNorms d hd ν hprob hnonconst hmean θ hθ hexp
