/-
**The growth rate of the mean divisible odometer alone**, extracted directly from
`Parking.External.SandpileGrowth` (`thm:BP`) via `Parking.meanu_eq_meanSandpileReal`
(`Parking/Support/CriticalLawReal.lean`), with NO other External hypothesis.

`Parking.Support.GrowthMeans`'s `meanU_growth` derives the analogous growth rate of the
PARTICLE odometer's mean, `meanU`, and along the way needs `Bernstein`, `UConcentration`
and `GreenNorms` too (to run the master comparison between `meanU` and `meanu`).  This
file isolates the strictly weaker fact about `meanu` alone, which needs `SandpileGrowth`
and nothing else: `meanu`'s two-sided polynomial bound is `hGrowth`'s own `d ≤ 3` clause,
read at the real pushforward `realLaw ν` of the critical law, with no comparison to the
particle odometer at all.

This is the quantitative input the vanishing-distance clause of `prop:spatial-scaling`
needs.  Matching the ABSOLUTE threshold `ε` of the rescaled comparison
`R^{d/2-2}|U_n(z) - u_n(z)|` against the RELATIVE threshold `ε' · meanu(n)` that
`prop:discrepancy`'s tail bound is stated with, uniformly over a compact range of rescaled
times, needs both the lower bound (so the relative threshold does not degenerate) and the
upper bound (so a single `ε'`, chosen from the largest rescaled time in the compact set,
controls the whole range).
-/
import Parking.Support.CriticalLawReal
import Parking.Support.MeanPos
import Parking.Support.CriticalChain

noncomputable section

namespace Parking

open MeasureTheory

/-- **The mean divisible odometer's two-sided polynomial growth**, `d ≤ 3`, from
`SandpileGrowth` alone. -/
theorem exists_meanu_growth_bounds (hGrowth : Parking.External.SandpileGrowth)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    ∃ b B : ℝ, 0 < b ∧ 0 < B ∧ ∀ n : ℕ, 2 ≤ n →
      b * (n : ℝ) ^ ((4 - (d : ℝ)) / 4) ≤ Parking.meanu (Parking.law d ν) n ∧
        Parking.meanu (Parking.law d ν) n ≤ B * (n : ℝ) ^ ((4 - (d : ℝ)) / 4) := by
  haveI := hν.prob
  have hBP := hGrowth d hd (realLaw ν) (realLaw_isProbability ν) (realLaw_mean ν hν)
    (realLaw_evariance_pos ν hν) (realLaw_evariance_lt_top ν hν) (realLaw_expMoment ν hν)
  obtain ⟨b, B, hb, hB, hbound⟩ := hBP.1 hd3
  refine ⟨b, B, hb, hB, fun n hn => ?_⟩
  have hsp := hbound n hn
  rwa [← meanu_eq_meanSandpileReal hd ν n] at hsp

/-- **`meanu` is monotone in the horizon**: the divisible odometer only grows with the time
horizon (`u_monotone_time`), so its mean does too. -/
theorem meanu_monotone (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    Monotone (fun n : ℕ => Parking.meanu (Parking.law d ν) n) := by
  haveI := hν.prob
  intro n m hnm
  exact integral_mono (integrable_uOf hd ν hν.integrable_abs n 0)
    (integrable_uOf hd ν hν.integrable_abs m 0)
    (fun ω => u_monotone_time hd (fun y => (ω.1 y : ℝ)) 0 hnm)

end Parking

end
