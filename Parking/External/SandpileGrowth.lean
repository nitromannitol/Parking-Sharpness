/-
External input: the growth of the mean divisible sandpile odometer, as the
paper quotes it (`parking.tex:919-933`, `thm:BP`), from Bou-Rabee and
Panagiotis, *Quantitative explosion and percolation of the divisible sandpile*
(Theorem 1.3, Corollary 6.2, Theorem 6.6 and equation (94) there), multiplied
by `2d` to match the normalization used here.

Assumed here.  It enters only as an explicit hypothesis of the theorems that
use it; the companion formalization of that paper proves it.
-/
import Parking.Basic

open MeasureTheory ProbabilityTheory Filter Topology

/-- The mean sandpile odometer for a real i.i.d. field: this input allows the
field to be real valued, not only integer valued. -/
noncomputable def Parking.External.meanSandpileReal (d : ℕ) (ν : Measure ℝ) (n : ℕ) : ℝ :=
  ∫ η, Parking.u η n 0 ∂(LatticeProb.iidLaw d ν)

-- FROZEN-STATEMENT-BEGIN
/-- Theorem 1.3, Corollary 6.2, Theorem 6.6 and equation (94) of the divisible
sandpile paper, as quoted in `parking.tex`. -/
def Parking.External.SandpileGrowth : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
    ∫ z, z ∂ν = 0 → 0 < evariance id ν → evariance id ν < ⊤ →
    (∃ θ : ℝ, 0 < θ ∧ Integrable (fun z => Real.exp (θ * |z|)) ν) →
    (d ≤ 3 → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        c * (n : ℝ) ^ ((4 - (d : ℝ)) / 4) ≤ Parking.External.meanSandpileReal d ν n ∧
          Parking.External.meanSandpileReal d ν n ≤ C * (n : ℝ) ^ ((4 - (d : ℝ)) / 4)) ∧
    (d = 4 → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        c * Real.log n ≤ Parking.External.meanSandpileReal d ν n ∧
          Parking.External.meanSandpileReal d ν n ≤ C * Real.log n) ∧
    (5 ≤ d → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        c * (Real.log n) ^ ((2 : ℝ) / d) ≤ Parking.External.meanSandpileReal d ν n ∧
          Parking.External.meanSandpileReal d ν n ≤ C * Real.log (n + 1)) ∧
    (5 ≤ d → (∃ b : ℝ, ∀ᵐ z ∂ν, b ≤ z) → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        c * (Real.log n) ^ ((2 : ℝ) / d) ≤ Parking.External.meanSandpileReal d ν n ∧
          Parking.External.meanSandpileReal d ν n ≤ C * (Real.log n) ^ ((2 : ℝ) / d)) ∧
    (d ≤ 3 → ∃ L : ℝ, 0 < L ∧
        Tendsto (fun n : ℕ => (n : ℝ) ^ (-((4 - (d : ℝ)) / 4)) * Parking.External.meanSandpileReal d ν n)
          atTop (𝓝 L))
-- FROZEN-STATEMENT-END

