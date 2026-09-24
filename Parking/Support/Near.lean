/-
The standing hypotheses and the quantities of Section 9 of `parking.tex`.

`NearFamily d δ₀ ν θ M K` is the hypothesis block of `thm:near`
(`parking.tex:314-335`), transcribed exactly as `Parking/Frozen/Near.lean`
transcribes it (the definition is the library's
`LatticeProb.ConvexOrder.NearFamily`, exported into `Parking`): probability laws of mean `-δ`, a nonconstant law at `δ = 0`,
exponential moments finite and bounded uniformly in `δ`, and a coupling of
`η_δ(0)` with `η_0(0)` of expected absolute difference at most `K δ`.  The
integrability is part of the bound on the exponential moments; without it the
Bochner integral of a nonintegrable function is zero and every family, however
heavy tailed, would satisfy the hypothesis.

`rangeExp d a t` is `E_0 e^{-a|R_t|}`, `resolventThreshold d C a` is the
threshold `T` of `eq:range-threshold`, and `xi δ η` is the recentred scenery
`ξ_δ = η_δ + δ` of `parking.tex:2744-2747`.
-/
import Parking.Support.Range
import LatticeProb.Prob.NearFamily

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Parking

export LatticeProb.ConvexOrder (NearFamily)

/-- The rate of Theorem 1.7. -/
noncomputable def nearRate (d : ℕ) (δ : ℝ) : ℝ :=
  if d = 1 then δ ^ (-(3 : ℝ))
  else if d = 2 then δ⁻¹
  else if d = 3 then δ ^ (-(1 : ℝ) / 3)
  else Real.log (Real.exp 1 / δ)

/-- `E_0 e^{-a|R_t|}`, an average over the walk alone. -/
def rangeExp (d : ℕ) (a : ℝ) (t : ℕ) : ℝ :=
  ∫ p, Real.exp (-(a * (rangeCard (0 : Site d) p t : ℝ))) ∂(walkLaw d)

/-- The threshold `T` of `eq:range-threshold`, with `Λ = log(e/a)`. -/
def resolventThreshold (d : ℕ) (C a : ℝ) : ℝ :=
  C * (if d = 1 then a ^ (-(2 : ℝ)) * Real.log (Real.exp 1 / a) ^ (3 : ℕ)
    else if d = 2 then a⁻¹ * Real.log (Real.exp 1 / a) ^ (3 : ℕ)
    else a⁻¹ * Real.log (Real.exp 1 / a) ^ (2 : ℕ))

/-- The recentred scenery `ξ_δ = η_δ + δ`, of mean zero. -/
def xi {d : ℕ} (δ : ℝ) (η : Site d → ℤ) (y : Site d) : ℝ := (η y : ℝ) + δ

end Parking

end
