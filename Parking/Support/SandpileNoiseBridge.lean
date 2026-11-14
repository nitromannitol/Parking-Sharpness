import Parking.External.LinearFieldScaling
import Sandpile.Continuum.Kernel

/-!
# Brownian Green kernels in coordinate and Euclidean form
-/

open MeasureTheory

namespace Parking

/-- The finite-time Green kernels agree under the Euclidean coordinate equivalence. -/
theorem contFiniteGreen_eq_greenTimeBM (d : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (x y : Fin d → ℝ) :
    External.contFiniteGreen d t x y =
      Sandpile.Continuum.greenTimeBM d t (WithLp.toLp 2 x) (WithLp.toLp 2 y) := by
  have hnorm : ‖(WithLp.toLp 2 x : Sandpile.Continuum.Space d) - WithLp.toLp 2 y‖ ^ 2 =
      ∑ i, (x i - y i) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  unfold External.contFiniteGreen Sandpile.Continuum.greenTimeBM
  rw [intervalIntegral.integral_of_le ht]
  congr 1
  funext s
  simp only [External.contHeatKernel, Sandpile.Continuum.heatKernelBM, hnorm]

/-- Extend prescribed test coordinates to an injectively indexed family disjoint from the tests. -/
theorem exists_noise_with_prescribed_coordinates {X Ω A : Type*}
    (test : (X → ℝ) → Prop) (kernel : A → X → ℝ)
    (hinj : Function.Injective kernel) (hdisjoint : ∀ a, ¬ test (kernel a))
    (W : (X → ℝ) → Ω → ℝ) (Y : A → Ω → ℝ) :
    ∃ W' : (X → ℝ) → Ω → ℝ,
      (∀ f, test f → W' f = W f) ∧ ∀ a, W' (kernel a) = Y a := by
  classical
  let W' : (X → ℝ) → Ω → ℝ := fun f =>
    if test f then W f
    else if h : ∃ a, kernel a = f then Y (Classical.choose h) else 0
  refine ⟨W', ?_, ?_⟩
  · intro f hf
    simp [W', hf]
  · intro a
    have h : ∃ b, kernel b = kernel a := ⟨a, rfl⟩
    have heq : Classical.choose h = a := hinj (Classical.choose_spec h)
    simp only [W', ite_eq_right (hdisjoint a), dite_eq_left h, heq]

end Parking
