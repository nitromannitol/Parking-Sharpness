/-
Coordinate Taylor identities for the continuum Laplacian. Each symmetric
second difference is the average of two second partial derivatives evaluated
between its endpoints. Compact support makes these derivatives uniformly
continuous, as required for the lattice approximation of the continuum operator.
-/
import Parking.Support.Continuum
import Parking.Support.ContOpRegularity
import Parking.Generic.TaylorSecondDiff

open Set
noncomputable section

namespace Parking

variable {d : ℕ}

open Parking.Generic.TaylorSecondDiff

/-- The `i`-th summand of `Parking.lap`: the second partial derivative of `φ` in direction `i`,
evaluated at `y`. Definitionally equal to `Parking.lap`'s own `i`-th term
(`Parking.lap_eq_sum_lapTerm`), separated out so it can be evaluated at a MOVED point (as
`exists_symm_second_diff_lapTerm` needs) without re-deriving the whole Laplacian. -/
def lapTerm (φ : (Fin d → ℝ) → ℝ) (i : Fin d) (y : Fin d → ℝ) : ℝ :=
  deriv (fun s => deriv (fun t => φ (Function.update y i t)) s) (y i)

/-- `Parking.lap` is exactly the sum of its `lapTerm` summands. -/
theorem lap_eq_sum_lapTerm (φ : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) :
    lap φ y = ∑ i, lapTerm φ i y := rfl

/-- `lapTerm` read at a point obtained from `z` by moving coordinate `i` to `ξ` is the second
derivative, at `ξ`, of `φ`'s one-variable restriction to the line through `z` in direction `i`
(the SAME restriction regardless of which value of `z i` was moved to `ξ`, since `Function.
update` at the same index overwrites: `Function.update_idem`). -/
theorem lapTerm_update (φ : (Fin d → ℝ) → ℝ) (i : Fin d) (z : Fin d → ℝ) (ξ : ℝ) :
    lapTerm φ i (Function.update z i ξ)
      = deriv (deriv (fun t => φ (Function.update z i t))) ξ := by
  unfold lapTerm
  have hupd : (Function.update z i ξ) i = ξ := Function.update_self i ξ z
  rw [hupd]
  congr 1
  funext s
  congr 1
  funext t
  rw [Function.update_idem]

/-- **The multivariate symmetric second difference, direction by direction.**  For `φ` twice
continuously differentiable, fixed `z`, direction `i`, and `h > 0`, the second difference of
`φ` at `z` along direction `i` equals `h²/2` times the sum of `lapTerm` at two points obtained
from `z` by moving coordinate `i` to an intermediate value within `h` on either side. This is
the exact content of the "Taylor expansion" the paper's Step 2 invokes, specialized to one of
the `2d` lattice directions entering `Parking.walkOp`. -/
theorem exists_symm_second_diff_lapTerm {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ (2 : ℕ) φ)
    (z : Fin d → ℝ) (i : Fin d) {h : ℝ} (hh : 0 < h) :
    ∃ ξ1 ∈ Ioo (z i) (z i + h), ∃ ξ2 ∈ Ioo (z i - h) (z i),
      φ (Function.update z i (z i + h)) + φ (Function.update z i (z i - h)) - 2 * φ z
        = h ^ 2 / 2 * (lapTerm φ i (Function.update z i ξ1)
          + lapTerm φ i (Function.update z i ξ2)) := by
  have hg : ContDiff ℝ (2 : ℕ) (fun t => φ (Function.update z i t)) :=
    hφ.comp (contDiff_update 2 z i)
  obtain ⟨ξ1, hξ1, ξ2, hξ2, heq⟩ := exists_symm_second_diff_eq hg (z i) hh
  refine ⟨ξ1, hξ1, ξ2, hξ2, ?_⟩
  rw [lapTerm_update, lapTerm_update]
  simpa using heq

/-- **`lapTerm` is `Parking.Support.ContOpRegularity`'s own second partial derivative.** Applying
`Parking.deriv_slice` twice (once for `φ` itself, once for its first partial derivative, both
already differentiable since `φ` is `C^∞`) identifies the nested nested-`deriv`
construction of `lapTerm` with the iterated Fréchet-derivative contraction
`partialDeriv (partialDeriv φ i) i`, whose continuity and compact support are ALREADY proved
(`Parking.Support.ContOpRegularity.contDiff_partialDeriv`/`hasCompactSupport_partialDeriv`), so
they need no separate argument here. -/
theorem lapTerm_eq_partialDeriv {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin d)
    (y : Fin d → ℝ) : lapTerm φ i y = partialDeriv (partialDeriv φ i) i y := by
  unfold lapTerm
  rw [funext (deriv_slice (hφ.differentiable (by simp)) y i)]
  have hP : Differentiable ℝ (partialDeriv φ i) :=
    (contDiff_partialDeriv hφ i).differentiable (by simp)
  rw [deriv_slice hP y i (y i), Function.update_eq_self]

/-- **`lapTerm φ i` is continuous** when `φ` is a test function: the concrete unlock for a
uniform-continuity argument bounding `exists_symm_second_diff_lapTerm`'s bracket, via the
identification with `partialDeriv (partialDeriv φ i) i`, already `C^∞` by
`Parking.Support.ContOpRegularity.contDiff_partialDeriv`. -/
theorem continuous_lapTerm {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) (i : Fin d) :
    Continuous (lapTerm φ i) := by
  have hcont : Continuous (partialDeriv (partialDeriv φ i) i) :=
    (contDiff_partialDeriv (contDiff_partialDeriv hφ.1 i) i).continuous
  exact hcont.congr (fun y => (lapTerm_eq_partialDeriv hφ.1 i y).symm)

end Parking

end
