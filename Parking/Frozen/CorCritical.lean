/-
Corollary 6.2 of parking.tex, frozen.  `parking.tex:1339-1346` (label
`cor:critical`):

  "Let $\eta=(\eta(x))_{x\in\Z^d}$ be independent copies of a nonconstant
   integer-valued $\eta(0)$ with mean zero.  Then there are $c,C>0$, with $c$
   universal, such that, for every $n\geq2$,
   $\E U_n(0)\geq\max\{\E u_n(0),\ c\log n-C\}$."

`c` is universal, so it is bound before the dimension and the law; `C` is
bound after them.
-/
import Parking.Frozen.CriticalDensity
import Parking.Support.CriticalChain

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.cor_critical :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (ν : Measure ℤ), IsProbabilityMeasure ν →
      (∀ k : ℤ, ν {k} ≠ 1) → Integrable (fun k : ℤ => |(k : ℝ)|) ν →
      ∫ k, (k : ℝ) ∂ν = 0 →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        max (Parking.meanu (Parking.law d ν) n) (c * Real.log n - C)
          ≤ Parking.meanU (Parking.law d ν) n
-- FROZEN-STATEMENT-END
:= by
  exact Parking.cor_critical_of_critical_density Parking.Frozen.critical_density
