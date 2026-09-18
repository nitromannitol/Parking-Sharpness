/- Jensen for the directed maximal walk average. -/
import Parking.Support.OrientedPathMax
import Parking.Support.OrientedMaximum
import Parking.Support.Lp

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

/-- Jensen for the directed maximal walk average: its `r`-th power is at most
the average of the `r`-th powers of the directed maximum. -/
theorem orientedMaxMean_rpow_le (hd : 1 ≤ d) (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d)
    {r : ℝ} (hr : 1 ≤ r) :
    orientedMaxMean F n x ^ r
      ≤ ∫ p, orientedMax F n x p ^ r ∂(walkLaw d) := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  have hMn : ∀ p, 0 ≤ orientedMax F n x p := fun p => orientedMax_nonneg F n x p
  have hMi : Integrable (orientedMax F n x) (walkLaw d) := integrable_orientedMax hd F n x
  have hMri : Integrable (fun p => orientedMax F n x p ^ r) (walkLaw d) := by
    apply integrable_of_finite_dependence hd n
    intro p q hpq
    rw [orientedMax_congr F n x hpq]
  simpa only [orientedMaxMean] using rpow_integral_le hMn hMi hr hMri

end Parking
end
