/- The directed error field is the routing error of the directed instruction law. -/
import Parking.Support.OrientedError
import Parking.Support.OrientedRoutingUnroll

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

/-- The error field of the directed recursion is the routing error of the
directed instruction law. -/
theorem wErrOriented_eq_orientedError (η : Site d → ℤ) (σ : Site d × ℕ → Site d) :
    wErrOriented η σ = orientedError η σ := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    rw [show wErrOriented η σ (n + 1) x = orientedOp (wErrOriented η σ n) x +
        ∑ i : Fin d, ((arrivals σ (x - unit i) x (orientedOdometer η σ n (x - unit i)) : ℝ)
          - (orientedOdometer η σ n (x - unit i) : ℝ) / d) from rfl,
      show orientedError η σ (n + 1) x = orientedOp (orientedError η σ n) x
        + orientedNoise η σ n x from rfl, ih]
    simp only [orientedNoise, orientedArrivalCount, Nat.cast_sum]
    rw [orientedOp, Finset.sum_sub_distrib, ← Finset.sum_div, orientedOp]

/-- The unrolled representation of the directed error field. -/
theorem wErrOriented_eq_layers (η : Site d → ℤ) (σ : Site d × ℕ → Site d) (n : ℕ) (x : Site d) :
    wErrOriented η σ n x = ∑ k ∈ range n,
      orientedLayerAverage (orientedNoise η σ k) (n - (k + 1)) x := by
  rw [wErrOriented_eq_orientedError, orientedError_eq_layers]

/-- The maximal walk average of the directed error field is that of the routing error. -/
theorem wStarOriented_eq_orientedMaxMean (η : Site d → ℤ) (σ : Site d × ℕ → Site d)
    (n : ℕ) (x : Site d) :
    wStarOriented η σ n x = orientedMaxMean (orientedError η σ) n x := by
  rw [wStarOriented, wErrOriented_eq_orientedError]

end Parking
end
