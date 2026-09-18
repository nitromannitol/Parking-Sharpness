/-
Theorem 8.2 of parking.tex, frozen.  `parking.tex:1586-1595` (label
`thm:four-sparse`):

  "Let $d=4$ and, for $0<\eps\leq1/2$, let $(\eta(x))_{x\in\Z^4}$ be
   independent and identically distributed, with $\eta(0)$ taking the values
   $1$ and $-1$ with probability $\eps/2$ each and $0$ otherwise.  There is
   $c>0$, independent of $\eps$, such that
   $\liminf_{n\to\infty}\frac{\E U_n(0)}{\E u_n(0)}\geq c\log(e/\eps)$."

The constant is independent of `ε`, so it is bound before it.  The three-point
law with parameter `ε/2` is `Parking.threePointLaw (ε/2)`, already used by
`thm:nearest-counterexample`.  The two results the proof quotes without proving
them here, the growth of the mean sandpile odometer and the optimal stopping
representation, enter as explicit hypotheses. The asymptotic lower bound is
written as an eventual inequality, with a smaller universal constant. This
avoids a real liminf whose boundedness would require additional cited inputs
used by the separate upper-ratio theorem.
-/
import Parking.Support.ThreePointLaw
import Parking.External.SandpileGrowth
import Parking.External.Stopping
import Parking.Support.FourSparseChain

open MeasureTheory Filter Topology

-- Convexity and homogeneity follow directly from the odometer recursion,
-- so the proof does not need the quoted stopping representation.
set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.four_sparse (hGrowth : Parking.External.SandpileGrowth)
    (hStopping : Parking.External.Stopping) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∀ᶠ n : ℕ in atTop, c * Real.log (Real.exp 1 / ε) ≤
        Parking.meanU (Parking.law 4 (Parking.threePointLaw (ε / 2))) n /
          Parking.meanu (Parking.law 4 (Parking.threePointLaw (ε / 2))) n
-- FROZEN-STATEMENT-END
:= by
  exact Parking.four_sparse_of_growth hGrowth
