/- Linearity of spatial directional differentiation. -/
import Parking.Generic.SpaceTimeDerivatives

noncomputable section
namespace Parking.Generic.SpaceTimeDerivatives
variable {d : ℕ}

theorem spaceDeriv_sub {f g : ℝ × (Fin d → ℝ) → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (i : Fin d) :
    spaceDeriv (fun p => f p - g p) i = fun p => spaceDeriv f i p - spaceDeriv g i p := by
  funext p
  simp only [spaceDeriv, fderiv_fun_sub (hf p) (hg p)]
  rfl

end Parking.Generic.SpaceTimeDerivatives
