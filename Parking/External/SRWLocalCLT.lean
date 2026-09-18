/-
External input: the multivariate local central limit theorem for the simple random walk,
in the exact uniform form Bou-Rabee and Panagiotis, *Quantitative explosion and percolation
of the divisible sandpile* (BP, already cited by `Parking.External.SpatialFixedTimeTightness`
and `Parking.External.GreenNorms`), state and use as their own equation (25) (Section 3.1,
"Heat-kernel input", page 19), attributed there to Lawler and Limic, *Random Walk: A Modern
Introduction*, Theorem 2.1.3, Eq. (2.8):

  "We also use the following form of the local central limit theorem [Lawler and Limic 2010,
   Theorem 2.1.3, Eq. (2.8)]: for all `0 < δ < T < ∞` and `C₀ < ∞`,

     lim_{R→∞} R^d · sup { |p_ℓ(x,y) - 2 R^{-d} p^{BM}_{ℓ/R²}(R^{-1}x, R^{-1}y)| :
                            δR² ≤ ℓ ≤ TR², |x-y| ≤ C₀R, p_ℓ(x,y) > 0 } = 0,

   where `p^{BM}` is the Brownian heat kernel from (14).  The factor 2 accounts for parity:
   for fixed `x` and `ℓ`, the sites `y` with `p_ℓ(x,y) > 0` form one parity class, whose
   scaled counting measure has density 1/2."

`Parking.Support.LinTimeShift`, `LinPotentialSum`, `LinCovariance` and `LinCovarianceGlue`
already reduce BP's own Proposition 4.3 covariance formula for the linear membrane field `V`,

    Cov(V_n(x), V_m(y)) = Var(η(0)) · Σ_{a<n} Σ_{b<m} srwHeat(a+b, y-x)

(`Parking.integral_linPotential_mul_closed_form`), to a finite sum of the discrete heat
kernel `LatticeProb.srwHeat`.  Identifying its `R → ∞` scaling limit (`n = ⌊sR²⌋`,
`m = ⌊tR²⌋`, `x, y` lattice points with `x/R, y/R` fixed reals) — the covariance engine's own
scalar limit, needed for the finite-dimensional convergence clause of `prop:spatial-scaling`
— is exactly a Riemann-sum-to-integral limit whose summand this local central limit theorem
controls uniformly; no such uniform comparison of `srwHeat` to the continuum kernel is proved
in this repository or the shared library (only two-sided ORDER-of-magnitude bounds,
`Parking.External.GreenNorms`, and a one-sided Gaussian upper bound,
`LatticeProb.srwHeat_gaussian`/`srwHeat_diag_le`, neither of which pins down a limit).

Assumed here, exactly as BP state it (their equation (25), itself an unproved citation in
BP), not proved in this repository. The Brownian heat kernel `contHeatKernel` transcribes
BP's equation (14), `p_t^{BM}(x,y) := (4πt/(2d))^{-d/2} exp(-d|x-y|²/(2t))`, generator
`(2d)^{-1}Δ` matching `parking.tex`'s own `L`.
-/
import Parking.Support.LinCovarianceGlue

open MeasureTheory LatticeProb

namespace Parking.External

/-- **The Brownian heat kernel**, BP's equation (14): `p_t^{BM}(x,y) = (4πt/(2d))^{-d/2}
exp(-d|x-y|²/(2t))`, for the Brownian motion on `ℝ^d` with generator `(2d)^{-1}Δ`. -/
noncomputable def contHeatKernel (d : ℕ) (t : ℝ) (x y : Fin d → ℝ) : ℝ :=
  (4 * Real.pi * t / (2 * d)) ^ (-(d : ℝ) / 2) *
    Real.exp (-(d : ℝ) * (∑ i, (x i - y i) ^ 2) / (2 * t))

end Parking.External

-- FROZEN-STATEMENT-BEGIN
/-- The multivariate local central limit theorem for the simple random walk on `Z^d`,
uniform on the parabolic window `δR² ≤ ℓ ≤ TR²`, `|x-y| ≤ C₀R`, in the exact form
Bou-Rabee-Panagiotis (2026) state and use it as their own equation (25), citing Lawler and
Limic, *Random Walk: A Modern Introduction*, Theorem 2.1.3, Eq. (2.8). -/
def Parking.External.SRWLocalCLT : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ δ T C₀ : ℝ, 0 < δ → δ ≤ T → 0 ≤ C₀ →
    ∀ ε : ℝ, 0 < ε →
      ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
        ∀ ℓ : ℕ, δ * R ^ 2 ≤ (ℓ : ℝ) → (ℓ : ℝ) ≤ T * R ^ 2 →
        ∀ x y : Parking.Site d, (∑ i, ((x i : ℝ) - (y i : ℝ)) ^ 2) ≤ (C₀ * R) ^ 2 →
        0 < LatticeProb.srwHeat d ℓ (x - y) →
          R ^ d * |LatticeProb.srwHeat d ℓ (x - y) -
              2 * (R ^ d)⁻¹ *
                Parking.External.contHeatKernel d ((ℓ : ℝ) / R ^ 2)
                  (fun i => (x i : ℝ) / R) (fun i => (y i : ℝ) / R)| < ε
-- FROZEN-STATEMENT-END
