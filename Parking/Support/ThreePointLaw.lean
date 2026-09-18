import Parking.Basic

open MeasureTheory

/-- The three-point law `P(±1) = p`, `P(0) = 1 - 2p` on `ℤ`. -/
noncomputable def Parking.threePointLaw (p : ℝ) : Measure ℤ :=
  ENNReal.ofReal p • Measure.dirac 1 + ENNReal.ofReal p • Measure.dirac (-1) +
    ENNReal.ofReal (1 - 2 * p) • Measure.dirac 0

