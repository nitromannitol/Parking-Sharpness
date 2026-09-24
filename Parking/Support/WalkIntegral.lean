import Parking.Support.WBound

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Integration commutes with the finite-range walk operator. -/
theorem integral_walkOp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → Site d → ℝ) (x : Site d) (hi : ∀ y ∈ nbrFinset x, Integrable (fun ω => f ω y) μ) :
    ∫ ω, walkOp (f ω) x ∂μ = walkOp (fun y => ∫ ω, f ω y ∂μ) x := by
  simp only [walkOp_eq_nbrFinset]
  rw [integral_div, integral_finsetSum _ hi]
end Parking
