/-
Corollary 1.3 of parking.tex, frozen.  `parking.tex:174-188` (label `cor:growth`):

  "Under the assumptions of Theorem 1.2,
   $\E U_n(0)\asymp n^{(4-d)/4}$ for $d\leq3$ and $\asymp\log n$ for $d\geq4$.
   When $d\leq3$, $S_t\asymp(t+1)^{-d/4}$ for every $t\geq0$.  When $d\geq4$,
   there are $0<c\leq C<\infty$ such that, for every $t\geq0$,
   $c/(t+1)\leq S_t\leq C\log(t+2)/(t+1)$."

The corollary depends on Theorem 1.2, so it carries the same hypotheses: the
growth of the mean sandpile odometer, the martingale moment inequality and the
concentration estimate.  `E U_n(0)` is compared for `n ≥ 2`, where the
logarithm is positive.

The results the proof quotes without proving them here enter as explicit
hypotheses.  The proof inserts `thm:BP` into the master bound, so this node
carries every external that `thm:master` carries, the collected Green estimates
among them.
-/
import Parking.External.SandpileGrowth
import Parking.External.Bernstein
import Parking.External.UConcentration
import Parking.External.GreenNorms
import Parking.Support.GrowthChain

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.growth (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration)
    (hGreenNorms : Parking.External.GreenNorms)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    (d ≤ 3 → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      (∀ n : ℕ, 2 ≤ n →
        c * (n : ℝ) ^ ((4 - (d : ℝ)) / 4) ≤ Parking.meanU (Parking.law d ν) n ∧
          Parking.meanU (Parking.law d ν) n ≤ C * (n : ℝ) ^ ((4 - (d : ℝ)) / 4)) ∧
      (∀ t : ℕ,
        c * ((t : ℝ) + 1) ^ (-((d : ℝ) / 4)) ≤ Parking.S (Parking.law d ν) t ∧
          Parking.S (Parking.law d ν) t ≤ C * ((t : ℝ) + 1) ^ (-((d : ℝ) / 4)))) ∧
    (4 ≤ d → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      (∀ n : ℕ, 2 ≤ n →
        c * Real.log n ≤ Parking.meanU (Parking.law d ν) n ∧
          Parking.meanU (Parking.law d ν) n ≤ C * Real.log n) ∧
      (∀ t : ℕ,
        c / ((t : ℝ) + 1) ≤ Parking.S (Parking.law d ν) t ∧
          Parking.S (Parking.law d ν) t ≤ C * Real.log ((t : ℝ) + 2) / ((t : ℝ) + 1)))
-- FROZEN-STATEMENT-END
:= by
  exact Parking.growth_of_master hGrowth hBernstein hConcentration hGreenNorms d hd ν hν
