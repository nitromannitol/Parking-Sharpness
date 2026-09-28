import Parking.Support.Near
import LatticeProb.Prob.ConvexOrder
import LatticeProb.Prob.Laplace
import LatticeProb.Prob.ExpTail
import Parking.Support.CriticalLawReal
import LatticeProb.Prob.ConvexProduct
import Parking.Support.UConvex
import LatticeProb.Prob.MapPi
import LatticeProb.Prob.NearFamily

/-!
# The law of the recentred scenery (`parking.tex:2744-2747`)

The law of the recentred scenery `ξ_δ = η_δ + δ` of `parking.tex:2744-2747`. Under
`iidLaw d (ν δ)` the field `η` is an independent family of integers with one-site law
`ν δ`, and `xi δ η` adds the constant `δ` in every coordinate, so `xi δ` pushes that law
forward to the i.i.d. real field whose one-site law is `shiftLaw δ (ν δ)`, the image of
`ν δ` under `k ↦ k + δ`.

The hypotheses of `Parking.NearFamily` say exactly that this one-site law has mean zero
and an exponential moment bounded uniformly in `δ`: the family's mean is `-δ`, so the
shift recentres it, and `|k + δ| ≤ |k| + |δ|` costs only the factor `e^{θ|δ|} ≤ e^{θδ₀}`.
Those two facts are what the convex comparison of `LatticeProb/Prob/ConvexOrder.lean`
consumes, and they are the source of the uniformity in `δ` of Step 1 of `lem:mean-horizon`.
-/

open LatticeProb.ConvexOrder (measurable_intShift shiftLaw)

noncomputable section

namespace Parking

open MeasureTheory LatticeProb

variable {d : ℕ}

/-- **The law of the recentred scenery.**  The recentred scenery pushes the i.i.d.
integer field forward to the i.i.d. real field with one-site law `shiftLaw δ ν`. -/
theorem law_map_xi (δ : ℝ) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    (LatticeProb.iidLaw d ν).map (fun η : Site d → ℤ => Parking.xi δ η)
      = LatticeProb.iidLaw d (shiftLaw δ ν) :=
  LatticeProb.iidLaw_map_pi d ν (measurable_intShift δ)

end Parking

end
