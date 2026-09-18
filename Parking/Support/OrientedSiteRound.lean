/-
The directed error at the origin, unrolled as one sum over the sites of the box,
the rounds and the departure stacks (`parking.tex:3240-3250`).
-/
import Parking.Support.OrientedArrivalLayer
import Parking.Support.OrientedFiniteRoute

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

/-- The directed error at the origin is the sum over the sites of the box of radius `n + 1`,
the rounds `k < n` and the departure stacks of `y`, of the routing discrepancy. -/
theorem wErrOriented_eq_siteRoundSum (η : Site d → ℤ) (σ : Site d × ℕ → Site d)
    (hσ : ∀ q : Site d × ℕ, ∃ i : Fin d, σ q = q.1 + unit i) (n : ℕ) :
    wErrOriented η σ n 0 = ∑ y ∈ boxFinset (0 : Site d) (n + 1),
      ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range (orientedOdometer η σ k y),
        orientedRouteDisc (n - (k + 1)) y (σ (y, j)) := by
  rw [wErrOriented_eq_finiteRoute η σ hσ n]
  simp only [orientedFiniteRoute]
  rw [Finset.sum_comm]

end Parking
end
