import Parking.Support.SceneryCovariance
import Parking.External.LinearFieldScaling
import Sandpile.Support.LimOccupationIdentity

/-!
# Limits of scenery covariances

The finite-time Brownian Green kernel represents integrated transition averages.
-/

open MeasureTheory ProbabilityTheory Filter Topology LatticeProb
open scoped NNReal

noncomputable section
namespace Parking

/-- The finite-time Green kernels agree under the Euclidean coordinate equivalence. -/
theorem scenery_contFiniteGreen_eq_greenTimeBM (d : ℕ) (t : ℝ) (ht : 0 ≤ t)
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

/-- A coordinate Green-kernel pairing is the time integral of Brownian averages. -/
theorem integral_mul_contFiniteGreen_eq_integral_brownian {d : ℕ} (hd : 1 ≤ d)
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hB : IsBrownianSpace d 0 B P)
    {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) {t : ℝ} (ht : 0 ≤ t)
    (x : Fin d → ℝ) :
    (∫ y, φ y * External.contFiniteGreen d t x y) =
      ∫ s in Set.Ioo (0 : ℝ) t, ∫ ω, φ (x + ofBrownianSpace B s.toNNReal ω) ∂P := by
  let f : Sandpile.Continuum.Space d → ℝ := fun y => φ (WithLp.ofLp y)
  obtain ⟨M, _, hM⟩ := LatticeProb.Walk.exists_norm_le_of_hasCompactSupport
    hφ.1.continuous hφ.2
  have hf : Measurable f := hφ.1.continuous.measurable.comp (PiLp.continuous_ofLp 2 _).measurable
  have hbound : ∀ y, |f y| ≤ M := fun y => by simpa [f, Real.norm_eq_abs] using hM (WithLp.ofLp y)
  have hBrown : Sandpile.Continuum.IsBrownian d 0 B P := ⟨hB.start, hB.coord, hB.indep⟩
  calc
    _ = ∫ y : Sandpile.Continuum.Space d,
        f y * Sandpile.Continuum.greenTimeBM d t (WithLp.toLp 2 x) y := by
      rw [← (PiLp.volume_preserving_toLp (Fin d)).integral_comp
        (MeasurableEquiv.toLp 2 _).measurableEmbedding]
      congr 1
      funext y
      simp [f, scenery_contFiniteGreen_eq_greenTimeBM d t ht]
    _ = ∫ s in Set.Ioo (0 : ℝ) t,
        Sandpile.Support.transAvg d f s (WithLp.toLp 2 x) :=
      Sandpile.Support.integral_mul_greenTimeBM hd ht _ f hf hbound
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro s hs
      dsimp only
      rw [Sandpile.Support.transAvg_eq_integral hd hBrown hs.1 _ f hf hbound]
      apply integral_congr_ae
      filter_upwards [hB.start] with ω hω
      simp [f, ofBrownianSpace, hω]
      congr 1

end Parking
