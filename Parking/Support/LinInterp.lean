/-
**The interpolated, rescaled linear membrane field**, `Parking.linHatInterp`: the
`(d+1)`-dimensional piecewise multilinear interpolation (`Parking.hatInterpD`,
`Parking/Support/HatInterpD.lean`) of the grid values of BP's own `Z_R`
(BouRabeePanagiotis2026, page 27, `Z_R(r,w) := R^{d/2-2} Σ_z g_{⌊R²r⌋}(⌊Rw⌋,z)ζ(z)`), from
the mesh `R^{-2}Z_+ × R^{-1}Z^d`.  This is BP's own `Z_R^{lin}`, "the standard interpolation
of `Z_R`" their own text names.

The grid field fed to `hatInterpD` is `fun (m:ℤ) (c:Site d) => R^{d/2-2}·linPotential ζ
m.toNat c`; evaluating `hatInterpD` at the rescaled point `(R²·s, R·x)` reads off exactly
`Z_R` at the integer grid points nearest `(R²s, Rx)` and interpolates between them, matching
`Parking.barDivisible`'s own scaling convention (`R^{d/2-2}·u_{⌊sR²⌋}(⌊Rx⌋)`) with `u`
replaced by the LINEAR field `linPotential` and the floor replaced by genuine interpolation.
Continuity is immediate from `Parking.continuous_hatInterpD`, general-purpose and already
proved; nothing new is needed for it.
-/
import Parking.Support.HatInterpD
import Parking.Support.LinPotential
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

noncomputable section

namespace Parking

variable {d : ℕ}

/-- **The interpolated, rescaled linear membrane field**, BP's own `Z_R^{lin}`: the
piecewise multilinear interpolation of `R^{d/2-2}·linPotential ζ` from the mesh
`R^{-2}ℤ_+ × R^{-1}ℤ^d`, read at the real space-time point `p = (s,x)`. -/
def linHatInterp {d : ℕ} (ζ : Site d → ℝ) (R : ℝ) (p : ℝ × (Fin d → ℝ)) : ℝ :=
  hatInterpD (fun m c => R ^ ((d : ℝ) / 2 - 2) * linPotential ζ m.toNat c)
    (R ^ 2 * p.1, fun i => R * p.2 i)

/-- **`linHatInterp` at a fixed scale `R` is continuous, jointly in space and time.**
Immediate from `Parking.continuous_hatInterpD`, composed with the continuous rescaling map
`p ↦ (R²p.1, R•p.2)`. -/
theorem continuous_linHatInterp (ζ : Site d → ℝ) (R : ℝ) :
    Continuous (linHatInterp ζ R) := by
  unfold linHatInterp
  exact (continuous_hatInterpD _).comp
    ((continuous_const.mul continuous_fst).prodMk
      (continuous_pi fun i => continuous_const.mul (continuous_apply i |>.comp continuous_snd)))

/-- **A continuous field cut off by a fixed compactly supported continuous test function is
a genuine bounded continuous function.**  The standard way of testing "convergence in law
locally uniformly" without building `C_loc` as its own topological space object: the cutoff
`χ` fixes a compact set outside which the bundled function is identically zero, so it is
automatically bounded (`BoundedContinuousFunction.ofCompactSupport`). -/
def cutoffBC {d : ℕ} (χ f : ℝ × (Fin d → ℝ) → ℝ) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hf : Continuous f) : BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℝ :=
  ofCompactSupport (fun p => χ p * f p) (hχ.mul hf) hχc.mul_right

end Parking

end
