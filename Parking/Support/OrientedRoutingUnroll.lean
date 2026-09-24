/- Convolution expansion of the directed routing error. -/
import Parking.Support.OrientedRouting
import Parking.Support.OrientedRoutingCoordinate

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

theorem orientedError_eq_layers (η : Site d → ℤ) (σ : Site d × ℕ → Site d) (n : ℕ) (x : Site d) :
    orientedError η σ n x = ∑ k ∈ range n,
      orientedLayerAverage (orientedNoise η σ k) (n - (k + 1)) x := by
  induction n generalizing x with
  | zero => simp [orientedError]
  | succ n ih =>
    change orientedOp (orientedError η σ n) x + orientedNoise η σ n x = _
    rw [show orientedError η σ n =
      (fun y => ∑ k ∈ range n, orientedLayerAverage (orientedNoise η σ k) (n - (k + 1)) y)
      from funext ih, orientedOp_sum (range n)
        (fun k y => orientedLayerAverage (orientedNoise η σ k) (n - (k + 1)) y), sum_range_succ]
    have he : ∀ k ∈ range n, n + 1 - (k + 1) = (n - (k + 1)) + 1 := fun k hk => by
      have := mem_range.mp hk
      omega
    simp only [Nat.sub_self, orientedLayerAverage_zero]
    congr 1
    exact sum_congr rfl fun k hk => by rw [he k hk, orientedLayerAverage_succ]

theorem orientedLayerAverage_at_zero (f : Site d → ℝ) (l : ℕ) :
    orientedLayerAverage f l 0 = ∑' y : Site d, orientedLayer d l y * f y := by
  simp only [orientedLayerAverage, zero_add]

end Parking
