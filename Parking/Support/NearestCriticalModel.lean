/-
The mass normalization used by the cited critical lower-tail theorem,
`sandpile.tex:1696-1720`, and its kernel and moment vocabulary.
The mass is σ = 1 + 2dη. The recursion divides by 2d, so its odometer
agrees with Parking.u η without rescaling the output.
-/
import Parking.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
noncomputable section
open MeasureTheory ProbabilityTheory LatticeProb Filter Topology
namespace Parking.CriticalScale

def relax {d : ℕ} (σ u : Site d → ℝ) (x : Site d) : ℝ :=
  max 0 ((σ x - 1 + nbrSum u x) / (2 * d))
def odometer {d : ℕ} (σ : Site d → ℝ) : ℕ → Site d → ℝ
  | 0 => fun _ => 0
  | t + 1 => relax σ (odometer σ t)
def centeredMassLaw (d : ℕ) (ν : Measure ℝ) : Measure (Site d → ℝ) :=
  LatticeProb.iidLaw d (ν.map fun z => 1 + 2 * (d : ℝ) * z)

/-- The `k`-step transition probability `p_k(x, y)` of simple random walk. -/
def heatKernel (d : ℕ) : ℕ → Site d → Site d → ℝ
  | 0 => fun x y => if x = y then 1 else 0
  | k + 1 => fun x y =>
      (∑ i : Fin d, (heatKernel d k (x + unit i) y + heatKernel d k (x - unit i) y)) / (2 * d)

/-- The finite-time Green kernel `g_t(x, y) = ∑_{k<t} p_k(x, y)`. -/
def greenTime (d : ℕ) (t : ℕ) (x y : Site d) : ℝ :=
  ∑ k ∈ Finset.range t, heatKernel d k x y


/-- The `d`-dependent rate on the right of `eq:Qt-table`
(`sandpile.tex:1186-1195`): `t^{3/2}` in dimension one, `t` in dimension two,
`t^{1/2}` in dimension three, `\log t` in dimension four, and `1` in dimensions
five and above.  The final branch is the paper's `d\geq5` case; the frozen
statement binds `1 \leq d`, so the branch is reached only there. -/
def varianceRate (d : ℕ) (t : ℕ) : ℝ :=
  if d = 1 then (t : ℝ) ^ ((3 : ℝ) / 2)
  else if d = 2 then (t : ℝ)
  else if d = 3 then (t : ℝ) ^ ((1 : ℝ) / 2)
  else if d = 4 then Real.log (t : ℝ)
  else 1

/-- The `d`-dependent rate on the right of `eq:corr-bound`
(`sandpile.tex:1206-1217`), with the constant `C` stripped off:
`(1+\log(n/m))\sqrt{m/n}` in dimension two, `\sqrt{(1+\log m)/(1+\log n)}` in
dimension four, and `(m/n)^{1/4}` in dimensions one and three, which the paper
gives the same case.  The final branch is that common case; the frozen
statement binds `1 \leq d` and `d \leq 4`, so it is reached only for
`d\in\{1,3\}`. -/
def corrRate (d : ℕ) (m n : ℕ) : ℝ :=
  if d = 2 then (1 + Real.log ((n : ℝ) / (m : ℝ))) * Real.sqrt ((m : ℝ) / (n : ℝ))
  else if d = 4 then Real.sqrt ((1 + Real.log (m : ℝ)) / (1 + Real.log (n : ℝ)))
  else ((m : ℝ) / (n : ℝ)) ^ ((1 : ℝ) / 4)

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
