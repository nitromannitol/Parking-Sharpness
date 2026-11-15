import Parking.Support.SandpileNoiseBridge
import Sandpile.Support.ContBMGreenIdentity

/-!
# The covariance of the finite-time Brownian Green kernel
-/

open MeasureTheory

namespace Parking

/-- The time-integrated heat kernels have the Brownian covariance. -/
theorem integral_contFiniteGreen_mul (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (x y : Fin d → ℝ) :
    (∫ z, External.contFiniteGreen d r x z * External.contFiniteGreen d s y z) =
      ∫ a in Set.Ioc (0 : ℝ) r, ∫ b in Set.Ioc (0 : ℝ) s,
        External.contHeatKernel d (a + b) x y := by
  have hheat (t : ℝ) : External.contHeatKernel d t x y =
      Sandpile.Continuum.heatKernelBM d t (WithLp.toLp 2 x) (WithLp.toLp 2 y) := by
    have hnorm : ‖(WithLp.toLp 2 x : Sandpile.Continuum.Space d) - WithLp.toLp 2 y‖ ^ 2 =
        ∑ i, (x i - y i) ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
    simp only [External.contHeatKernel, Sandpile.Continuum.heatKernelBM, hnorm]
  calc
    _ = ∫ z : Sandpile.Continuum.Space d,
        Sandpile.Continuum.greenTimeBM d r (WithLp.toLp 2 x) z *
          Sandpile.Continuum.greenTimeBM d s (WithLp.toLp 2 y) z := by
      rw [← (PiLp.volume_preserving_toLp (Fin d)).integral_comp
        (MeasurableEquiv.toLp 2 _).measurableEmbedding]
      simp only [← contFiniteGreen_eq_greenTimeBM d r hr,
        ← contFiniteGreen_eq_greenTimeBM d s hs]
    _ = ∫ a in Set.Ioo (0 : ℝ) r, ∫ b in Set.Ioo (0 : ℝ) s,
        Sandpile.Continuum.heatKernelBM d (a + b) (WithLp.toLp 2 x) (WithLp.toLp 2 y) :=
      Sandpile.Support.integral_greenTimeBM_mul_two hd hd3 hr hs _ _
    _ = _ := by
      simp_rw [← hheat, ← integral_Ioc_eq_integral_Ioo]

end Parking
