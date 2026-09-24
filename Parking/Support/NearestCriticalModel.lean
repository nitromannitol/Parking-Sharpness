/-
The mass normalization used by the cited critical lower-tail theorem,
`sandpile.tex:1696-1720`, and its kernel and moment vocabulary.
The mass is σ = 1 + 2dη. The recursion divides by 2d, so its odometer
agrees with Parking.u η without rescaling the output.
-/
import Parking.Basic
import LatticeProb.Walk.LatticeGreen
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import LatticeProb.Walk.Correlation
import LatticeProb.Walk.VarianceScale
noncomputable section
open MeasureTheory ProbabilityTheory LatticeProb Filter Topology
namespace Parking.CriticalScale

export LatticeProb (corrRate varianceRate)

def relax {d : ℕ} (σ u : Site d → ℝ) (x : Site d) : ℝ :=
  max 0 ((σ x - 1 + nbrSum u x) / (2 * d))
def odometer {d : ℕ} (σ : Site d → ℝ) : ℕ → Site d → ℝ
  | 0 => fun _ => 0
  | t + 1 => relax σ (odometer σ t)
def centeredMassLaw (d : ℕ) (ν : Measure ℝ) : Measure (Site d → ℝ) :=
  LatticeProb.iidLaw d (ν.map fun z => 1 + 2 * (d : ℝ) * z)

/-- The `k`-step transition probability `p_k(x, y)` of simple random walk.
Reuses `LatticeProb.LocalCLT.heatKernel`, to which this is definitionally
equal (same recursion, `Site d` is `LatticeProb.Site d`). -/
abbrev heatKernel (d : ℕ) : ℕ → Site d → Site d → ℝ :=
  LatticeProb.LocalCLT.heatKernel d

/-- The finite-time Green kernel `g_t(x, y) = ∑_{k<t} p_k(x, y)`.
Reuses `LatticeProb.greenTime`. -/
abbrev greenTime (d : ℕ) (t : ℕ) (x y : Site d) : ℝ :=
  LatticeProb.greenTime d t x y

/-- The time window `\sum_{k=m}^{n-1}p_k(x,z)` of `eq:d4-window-l2` and
`eq:d4-window-linfty` (`sandpile.tex:1222-1232`), a finite sum over the steps
`k` with `m \leq k < n`. -/
def windowKernel (m n : ℕ) (x z : Site 4) : ℝ :=
  ∑ k ∈ Finset.Ico m n, heatKernel 4 k x z

/-- The covariance matrix `Σ` of the linear forms `Y_j = ∑_i a_i(j) ξ_i` when
the coordinates `ξ_i` are i.i.d. with one-site law `ν`:
`Σ_{jk} = \Var(ν)\sum_i a_i(j) a_i(k)`. -/
def gram {N m : ℕ} (ν : Measure ℝ) (a : Fin N → Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun j k => variance id ν * ∑ i, a i j * a i k

/-- `|a(i)|`, the Euclidean norm of the coefficient vector of the `i`-th
coordinate. -/
def coeffNorm {N m : ℕ} (a : Fin N → Fin m → ℝ) (i : Fin N) : ℝ :=
  Real.sqrt (∑ j, a i j ^ 2)

/-- The quadratic form `v ↦ ⟨Sv, v⟩` of a matrix, in which the paper's spectral
bound on `Σ` is transcribed. -/
def quadForm {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (v : Fin m → ℝ) : ℝ :=
  ∑ j, ∑ k, S j k * v j * v k

/-- The Berry--Esseen remainder of `eq:dlt4-green-lower-tail`: the factor that
multiplies `C` in the second summand, `(\log t)^{3/4}t^{-1/4}L^{a/4}` for
`d ∈ {1, 3}` and `(\log t)^{7/4}t^{-1/2}L^{a/2}` for `d = 2`. -/
def lowerTailRemainder (d : ℕ) (t : ℕ) (L a : ℝ) : ℝ :=
  if d = 2 then
    Real.log t ^ ((7 : ℝ) / 4) * (t : ℝ) ^ (-(1 : ℝ) / 2) * L ^ (a / 2)
  else
    Real.log t ^ ((3 : ℝ) / 4) * (t : ℝ) ^ (-(1 : ℝ) / 4) * L ^ (a / 4)

end Parking.CriticalScale

end
