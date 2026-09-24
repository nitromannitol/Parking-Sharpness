/-
Theorem 1.4 of parking.tex, frozen.  `parking.tex:207-238` (label `thm:trichotomy`):

  "(i) [$d\leq3$] almost surely and in $L^r$ for every $r\geq1$,
   $(U_n(0)-u_n(0))/\E u_n(0)\to0$.  Consequently $\E U_n(0)/\E u_n(0)\to1$, and
   $n^{-(4-d)/4}\E U_n(0)$ converges to a limit in $(0,\infty)$.
   (ii) [$d=4$] For every $n\geq1$ the ratio $\E U_n(0)/\E u_n(0)$ is at least
   one.  For each fixed law this ratio is bounded above uniformly in $n$, but
   for every $B>0$ there is a law satisfying the hypotheses with
   $\liminf_n \E U_n(0)/\E u_n(0)\geq B$.
   (iii) [$d\geq5$] If in addition $\eta(0)$ is bounded below, then
   $\E U_n(0)\asymp\log n$ and $\E|U_n(0)-u_n(0)|\asymp\log n$, while
   $\E U_n(0)/\E u_n(0)\to\infty$."

`L^r` convergence is written as the `r`-th absolute moment tending to zero,
together with the finiteness of that moment, so that an undefined integral
cannot satisfy the convergence through its junk value; the almost-sure
statement is over the full law of the data.  The three parts are frozen as one
conjunction because the paper states them as one theorem.  The results the
proof quotes without proving them here enter as explicit hypotheses: the growth
of the mean sandpile odometer, and, through `prop:discrepancy`, the martingale
moment inequality and the concentration estimate.  Part (ii) invokes
`thm:four-sparse`, whose proof uses the optimal stopping representation, so
that enters as well.

Parts (i) and (iii) read the growth of the mean odometers off `cor:growth`, so
this node carries every external that `cor:growth` carries, the collected Green
estimates among them.
-/
import Parking.External.SandpileGrowth
import Parking.External.Bernstein
import Parking.External.UConcentration
import Parking.External.GreenNorms
import Parking.External.Stopping

import Parking.Support.LowMeanLimits
import Parking.Support.FourRatio
import Parking.Support.HighDiscrepancy

open MeasureTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.trichotomy (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration)
    (hGreenNorms : Parking.External.GreenNorms)
    (hStopping : Parking.External.Stopping) (d : ℕ) (hd : 1 ≤ d) :
    (d ≤ 3 → ∀ (ν : Measure ℤ), Parking.CriticalLaw ν →
      (∀ᵐ ω ∂(Parking.law d ν),
        Tendsto (fun n : ℕ => ((Parking.U ω n 0 : ℝ) - Parking.uOf ω n 0) /
          Parking.meanu (Parking.law d ν) n) atTop (𝓝 0)) ∧
      (∀ r : ℝ, 1 ≤ r →
        (∀ n : ℕ, Integrable (fun ω => |((Parking.U ω n 0 : ℝ) - Parking.uOf ω n 0) /
          Parking.meanu (Parking.law d ν) n| ^ r) (Parking.law d ν)) ∧
        Tendsto (fun n : ℕ => ∫ ω, |((Parking.U ω n 0 : ℝ) - Parking.uOf ω n 0) /
          Parking.meanu (Parking.law d ν) n| ^ r ∂(Parking.law d ν)) atTop (𝓝 0)) ∧
      Tendsto (fun n : ℕ => Parking.meanU (Parking.law d ν) n /
        Parking.meanu (Parking.law d ν) n) atTop (𝓝 1) ∧
      ∃ L : ℝ, 0 < L ∧ Tendsto (fun n : ℕ =>
        (n : ℝ) ^ (-((4 - (d : ℝ)) / 4)) * Parking.meanU (Parking.law d ν) n) atTop (𝓝 L)) ∧
    (d = 4 → (∀ (ν : Measure ℤ), Parking.CriticalLaw ν →
      (∀ n : ℕ, 1 ≤ n → 1 ≤ Parking.meanU (Parking.law d ν) n / Parking.meanu (Parking.law d ν) n) ∧
      ∃ B : ℝ, ∀ n : ℕ, 1 ≤ n →
        Parking.meanU (Parking.law d ν) n / Parking.meanu (Parking.law d ν) n ≤ B) ∧
      ∀ B : ℝ, 0 < B → ∃ ν : Measure ℤ, Parking.CriticalLaw ν ∧
        B ≤ liminf (fun n : ℕ => Parking.meanU (Parking.law d ν) n /
          Parking.meanu (Parking.law d ν) n) atTop) ∧
    (5 ≤ d → ∀ (ν : Measure ℤ), Parking.CriticalLaw ν → (∃ b : ℤ, ν (Set.Iio b) = 0) →
      (∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
        c * Real.log n ≤ Parking.meanU (Parking.law d ν) n ∧
          Parking.meanU (Parking.law d ν) n ≤ C * Real.log n ∧
        c * Real.log n ≤ ∫ ω, |(Parking.U ω n 0 : ℝ) - Parking.uOf ω n 0| ∂(Parking.law d ν) ∧
          ∫ ω, |(Parking.U ω n 0 : ℝ) - Parking.uOf ω n 0| ∂(Parking.law d ν) ≤ C * Real.log n) ∧
      Tendsto (fun n : ℕ => Parking.meanU (Parking.law d ν) n /
        Parking.meanu (Parking.law d ν) n) atTop atTop)
-- FROZEN-STATEMENT-END
:= by
  refine ⟨?_, ?_, ?_⟩
  · intro hd3 ν hν
    exact ⟨Parking.ae_discrepancy_tendsto_zero hd hd3 hGrowth hBernstein hConcentration
        hGreenNorms ν hν,
      fun r hr => Parking.discrepancy_moment_tendsto_zero hd hd3 hGrowth hBernstein
        hConcentration hGreenNorms ν hν r hr,
      Parking.low_mean_ratio_tendsto_one hd hd3 hGrowth hBernstein hConcentration
        hGreenNorms ν hν,
      Parking.low_meanU_scaling_limit hd hd3 hGrowth hBernstein hConcentration
        hGreenNorms ν hν⟩
  · intro hd4
    subst d
    exact ⟨fun ν hν => Parking.four_mean_ratio_bounds hGrowth hBernstein hConcentration
        hGreenNorms ν hν,
      fun B hB => Parking.exists_four_mean_ratio_large hGrowth hBernstein hConcentration
        hGreenNorms hStopping B hB⟩
  · intro hd5 ν hν hb
    exact ⟨Parking.high_mean_discrepancy_bounds hd hd5 hGrowth hBernstein hConcentration
        hGreenNorms ν hν hb,
      Parking.high_mean_ratio_tendsto_atTop hd hd5 hGrowth hBernstein hConcentration
        hGreenNorms ν hν hb⟩
