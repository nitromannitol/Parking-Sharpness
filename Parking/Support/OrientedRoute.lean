/- The directed Green increment as a sum of one-layer routing discrepancies. -/
import Parking.Support.OrientedPotential
import Parking.Support.OrientedRoutingCoordinate

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

/-- The increment of the truncated Green function under one directed
instruction is the sum over the horizons of the one-layer discrepancy
`orientedRouteDisc`. -/
theorem orientedGreen_sub_instruction_eq_sum_routeDisc (M : ℕ) (y z : Site d) :
    orientedGreen d M z - (∑ i : Fin d, orientedGreen d M (y + unit i)) / d =
      ∑ l ∈ Finset.range M, orientedRouteDisc l y z := by
  simp only [orientedGreen, Finset.sum_div]
  rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [orientedRouteDisc, ← Finset.sum_div, ← orientedLayer_succ]

end Parking
end
