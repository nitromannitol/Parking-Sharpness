import Parking.Support.EscapeGap

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The two-target instruction weight, averaged over its possible destinations. -/
def holeKernel (d : ℕ) (x z y : Site d) : ℝ :=
  ∫ a, (1 - escapePotential d x (y + stepVec a)) *
    (1 - escapePotential d z (y + stepVec a)) ∂(stepLaw d)

theorem holeKernel_nonneg (hd : 3 ≤ d) (x z y : Site d) : 0 ≤ holeKernel d x z y :=
  integral_nonneg fun a => mul_nonneg (sub_nonneg.mpr (escapePotential_bounds hd x (y + stepVec a)).2)
    (sub_nonneg.mpr (escapePotential_bounds hd z (y + stepVec a)).2)

theorem holeKernel_eq_walkOp (hd : 1 ≤ d) (x z y : Site d) :
    holeKernel d x z y = walkOp (fun v =>
      (fullGreen d (v - x) / escapeConst d) * (fullGreen d (v - z) / escapeConst d)) y := by
  simp only [holeKernel, escapePotential, sub_sub_cancel]
  exact integral_stepLaw_add hd (fun v =>
    (fullGreen d (v - x) / escapeConst d) * (fullGreen d (v - z) / escapeConst d)) y

/-- Every real function of one direction is integrable. -/
theorem integrable_step_fun (hd : 1 ≤ d) (f : Fin d × Bool → ℝ) : Integrable f (stepLaw d) := by
  haveI := stepLaw_isProbability hd
  exact integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)
end Parking
