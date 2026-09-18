/-
The comparison of the two limit means, for the lower bounds of `thm:near`
(`parking.tex:2897-2903`).

"Theorem thm:comparison gives `E U_∞^δ(0) ≥ E u_∞^δ(0)`.  Proposition
prop:near-divisible now gives the claimed bounds when `d ≤ 3`."

`thm:comparison` is sealed at every horizon, and `Parking.meanu_le_meanU` is its
form in the mean.  What is added here is the passage to the limits, which live in
`ℝ≥0∞` and in two different shapes: the divisible limit mean is the supremum over
the horizon of the means, and the particle limit mean is the lower integral of the
pointwise supremum.  Both ends of the comparison are read through
`ofReal_integral_eq_lintegral_ofReal` at a fixed horizon and then `lintegral_mono`.
-/
import Parking.Support.NearBounded
import Parking.Support.CriticalChain

open MeasureTheory ProbabilityTheory LatticeProb
open scoped ENNReal NNReal

noncomputable section
namespace Parking
variable {d : ℕ}

/-- **`thm:comparison` in the limit mean.**  The limit mean divisible odometer is at most
the limit mean particle odometer. -/
theorem meanuLimit_le_meanUlimit (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) :
    Parking.meanuLimit (Parking.law d ν) ≤ Parking.meanUlimit (Parking.law d ν) := by
  refine iSup_le fun n => ?_
  have h1 : Parking.meanu (Parking.law d ν) n ≤ Parking.meanU (Parking.law d ν) n :=
    meanu_le_meanU hd ν hint n
  have hIU : Integrable (fun ω : Data d => ((Parking.U ω n 0 : ℕ) : ℝ)) (Parking.law d ν) :=
    integrable_U_law hd ν hint n 0
  have h2 : ENNReal.ofReal (Parking.meanU (Parking.law d ν) n)
      = ∫⁻ ω, ENNReal.ofReal ((Parking.U ω n 0 : ℕ) : ℝ) ∂(Parking.law d ν) := by
    rw [Parking.meanU]
    exact ofReal_integral_eq_lintegral_ofReal hIU
      (Filter.Eventually.of_forall fun ω => Nat.cast_nonneg _)
  have h3 : ∀ ω : Data d, ENNReal.ofReal ((Parking.U ω n 0 : ℕ) : ℝ)
      ≤ ((Parking.Ulimit ω 0 : ℕ∞) : ℝ≥0∞) := by
    intro ω
    rw [ENNReal.ofReal_natCast, Parking.Ulimit, ENat.toENNReal_iSup]
    refine le_trans (le_of_eq ?_)
      (le_iSup (fun m : ℕ => ((((Parking.U ω m 0 : ℕ) : ℕ∞)) : ℝ≥0∞)) n)
    simp
  calc ENNReal.ofReal (Parking.meanu (Parking.law d ν) n)
      ≤ ENNReal.ofReal (Parking.meanU (Parking.law d ν) n) := ENNReal.ofReal_le_ofReal h1
    _ = ∫⁻ ω, ENNReal.ofReal ((Parking.U ω n 0 : ℕ) : ℝ) ∂(Parking.law d ν) := h2
    _ ≤ ∫⁻ ω, ((Parking.Ulimit ω 0 : ℕ∞) : ℝ≥0∞) ∂(Parking.law d ν) :=
        lintegral_mono h3
    _ = Parking.meanUlimit (Parking.law d ν) := rfl

end Parking
end
