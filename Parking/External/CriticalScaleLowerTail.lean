/-
The critical-scale lower tail estimate of Bou-Rabee and Panagiotis,
sandpile.tex:1696-1720, cited at parking.tex:1807-1833.

The exact lower tail at the critical scale is retained in that paper's mass
normalization, σ = 1 + 2dζ. Its VarianceScale and MultivariateBerryEsseen
hypotheses are retained explicitly and restated in separate external nodes.
The constants precede the one-site law, the horizon and the real threshold L;
the dimension, variance lower bound, normalized third-moment bound and a are
their only parameters. In particular every positivity, integrability and
finite-variance hypothesis of the source theorem is retained.

This is a cited input: it is assumed here and no proof of this Prop is
asserted in this repository.
-/
import Parking.External.VarianceScale
import Parking.External.MultivariateBerryEsseen

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
/-- The critical-scale lower tail estimate of Bou-Rabee and Panagiotis,
`sandpile.tex:1696-1720`, cited at `parking.tex:1807-1833`. -/
def Parking.External.CriticalScaleLowerTail : Prop :=
  Parking.External.VarianceScale → Parking.External.MultivariateBerryEsseen →
  ∀ (d : ℕ) (_hd : 1 ≤ d) (_hd3 : d ≤ 3) (ν₀ M : ℝ) (_hν₀ : 0 < ν₀)
    (a : ℝ) (_ha : 0 < a) (_ha' : a < 4 / (4 - (d : ℝ))),
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
      ∫ z, z ∂ν = 0 → 0 < evariance id ν → evariance id ν < ⊤ →
      Integrable (fun z => |z| ^ 3) ν →
      ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
      ∫ z, |z| ^ 3 ∂ν ≤ M * variance id ν ^ ((3 : ℝ) / 2) →
      ∀ (t : ℕ) (L : ℝ), 3 ≤ t → 2 ≤ L → L ^ a ≤ (t : ℝ) / 2 →
        Parking.CriticalScale.centeredMassLaw d ν
            {σ | Parking.CriticalScale.odometer σ t 0 ≤ (t : ℝ) ^ ((4 - (d : ℝ)) / 4) / L} ≤
          ENNReal.ofReal (C * L ^ (-c) + C * Parking.CriticalScale.lowerTailRemainder d t L a)
-- FROZEN-STATEMENT-END
