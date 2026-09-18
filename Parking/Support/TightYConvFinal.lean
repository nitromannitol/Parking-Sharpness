/-
`hYconv`, unconditionally: assembles `Parking.tendsto_integral_Y_of_hWalk` (`TightYConv.lean`)
with a concrete quarter-Brownian motion (`Parking.exists_isQuarterBrownian_cont`,
`TightQuarterBrownian.lean`), its finite-dimensional convergence to the rescaled oriented walk
(`Parking.hWalk_of_quarterBrownian`, `TightWalkConv.lean`), and the everywhere-continuous noise
modification (`Parking.exists_continuousOn_modification_contZ_box`,
`TightNoiseModification.lean`).  This is `hYconv` in exactly the shape
`Parking.oriented_scaling_of_cutoff` needs, closed with no `sorry` and no External beyond the
two already registered (`Parking.External.BinomialLocalCLT`,
`Parking.External.OrientedStoppingStability`).
-/
import Parking.Support.TightYConv
import Parking.Support.TightWalkConv

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

namespace Parking

/-- **`hYconv`, unconditionally.** -/
theorem hYconv_unconditional (ν : Measure ℤ) (hν : CriticalLaw ν)
    (hBinomial : External.BinomialLocalCLT) (hStability : External.OrientedStoppingStability) :
    ∀ A : ℕ, ∀ f : ℝ → ℝ, (∃ C : ℝ, ∀ x y, dist (f x) (f y) ≤ C) →
      (∃ K, LipschitzWith K f) →
      ∃ c : ℝ, Tendsto (fun n => ∫ w, f (Y A n w) ∂(orientedLaw 2 ν)) atTop (𝓝 c) := by
  intro A f hfb hflip
  obtain ⟨ΩB, mΩB, PB, B, hBmeas, hBQuarter, hBcont⟩ := exists_isQuarterBrownian_cont
  haveI : IsProbabilityMeasure PB :=
    (isGaussianProcess_quarterBrownian hBQuarter).isProbabilityMeasure
  obtain ⟨Yfield, hYmeas, hYmod, hYcont⟩ := exists_continuousOn_modification_contZ_box
    (v := ∫ x : ℝ, x ^ 2 ∂(realLaw ν)) (realLaw_sq_integral_pos ν hν).le zero_le_one
    (Nat.cast_nonneg A)
  exact tendsto_integral_Y_of_hWalk ν hν hBinomial hStability PB B hBQuarter A
    (fun m ts hts F => hWalk_of_quarterBrownian PB B hBmeas hBQuarter m ts hts F)
    hYmeas hYcont hYmod f hfb hflip

end Parking

end
