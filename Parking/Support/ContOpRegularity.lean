/-
Regularity of the operator `L = (2d)^{-1}Δ` of `parking.tex:1730` on test
functions.

`lap` is written coordinatewise, as the sum over `i` of the second derivative of
the slice `t ↦ φ (Function.update x i t)` at `t = x i`.  The two facts the
continuum statements need are that `contOp d φ` is again continuous and again
compactly supported when `φ` is a test function, so that every integral
`∫ U(s,x) (Lφ)(x) dx` against a locally bounded field converges.  Both come from
the identification of the slice derivative with the Fréchet derivative in the
direction `Pi.single i 1`, which `hasDerivAt_update` supplies.
-/
import Parking.Support.Continuum
import Mathlib.Analysis.Calculus.Deriv.Pi

open MeasureTheory

noncomputable section

namespace Parking

variable {d : ℕ}

/-- The partial derivative of `φ` in the direction of the `i`-th axis. -/
def partialDeriv (φ : (Fin d → ℝ) → ℝ) (i : Fin d) (x : Fin d → ℝ) : ℝ :=
  fderiv ℝ φ x (Pi.single i 1)

/-- The derivative of a coordinate slice is the partial derivative. -/
theorem deriv_slice {φ : (Fin d → ℝ) → ℝ} (hφ : Differentiable ℝ φ)
    (x : Fin d → ℝ) (i : Fin d) (s : ℝ) :
    deriv (fun t => φ (Function.update x i t)) s
      = partialDeriv φ i (Function.update x i s) :=
  (((hφ (Function.update x i s)).hasFDerivAt).comp_hasDerivAt s
    (hasDerivAt_update x i s)).deriv

/-- `partialDeriv φ i` is smooth when `φ` is. -/
theorem contDiff_partialDeriv {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (partialDeriv φ i) :=
  (ContinuousLinearMap.apply ℝ ℝ (Pi.single i (1 : ℝ))).contDiff.comp
    (hφ.fderiv_right (by simp))

/-- `partialDeriv φ i` has compact support when `φ` does. -/
theorem hasCompactSupport_partialDeriv {φ : (Fin d → ℝ) → ℝ}
    (hφ : HasCompactSupport φ) (i : Fin d) :
    HasCompactSupport (partialDeriv φ i) :=
  HasCompactSupport.fderiv_apply (𝕜 := ℝ) hφ (Pi.single i 1)

/-- **The Laplacian as a sum of second Fréchet derivatives.** -/
theorem lap_eq_sum {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Fin d → ℝ) :
    lap φ x = ∑ i : Fin d, partialDeriv (partialDeriv φ i) i x := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have hslice : (fun s => deriv (fun t => φ (Function.update x i t)) s)
      = fun s => partialDeriv φ i (Function.update x i s) :=
    funext (deriv_slice (hφ.differentiable (by simp)) x i)
  rw [hslice]
  have hP : Differentiable ℝ (partialDeriv φ i) :=
    (contDiff_partialDeriv hφ i).differentiable (by simp)
  have := deriv_slice hP x i (x i)
  rw [this, Function.update_eq_self]

/-- The closed support of a partial derivative sits inside that of the function. -/
theorem tsupport_partialDeriv_subset (φ : (Fin d → ℝ) → ℝ) (i : Fin d) :
    tsupport (partialDeriv φ i) ⊆ tsupport φ :=
  tsupport_fderiv_apply_subset ℝ (Pi.single i 1)

/-- A partial derivative vanishes off the closed support. -/
theorem partialDeriv_eq_zero_of_notMem {φ : (Fin d → ℝ) → ℝ} {i : Fin d} {x : Fin d → ℝ}
    (hx : x ∉ tsupport φ) : partialDeriv φ i x = 0 := by
  have : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ hx
  simp [partialDeriv, this]

/-- **`contOp d φ` is continuous on a test function.** -/
theorem continuous_contOp {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) :
    Continuous (contOp d φ) := by
  have h : Continuous (fun x => ∑ i : Fin d, partialDeriv (partialDeriv φ i) i x) :=
    continuous_finsetSum _ fun i _ =>
      ((contDiff_partialDeriv (contDiff_partialDeriv hφ.1 i) i).continuous)
  have hlap : Continuous (lap φ) := by
    refine h.congr fun x => ?_
    exact (lap_eq_sum hφ.1 x).symm
  exact hlap.div_const _

/-- **`contOp d φ` has compact support on a test function.** -/
theorem hasCompactSupport_contOp {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) :
    HasCompactSupport (contOp d φ) := by
  refine HasCompactSupport.intro hφ.2 fun x hx => ?_
  have hz : ∀ i : Fin d, partialDeriv (partialDeriv φ i) i x = 0 := fun i =>
    partialDeriv_eq_zero_of_notMem (fun h => hx (tsupport_partialDeriv_subset φ i h))
  simp [contOp, lap_eq_sum hφ.1 x, hz]

/-- **`contOp` is homogeneous in the test function.** -/
theorem contOp_const_mul (c : ℝ) (φ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    contOp d (fun y => c * φ y) x = c * contOp d φ x := by
  have h : lap (fun y => c * φ y) x = c * lap φ x := by
    unfold lap
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (fun s => deriv (fun t => c * φ (Function.update x i t)) s)
        = fun s => c * deriv (fun t => φ (Function.update x i t)) s :=
      funext fun s => deriv_const_mul_field c
    rw [h1, deriv_const_mul_field]
  unfold contOp
  rw [h, mul_div_assoc]

end Parking

end
