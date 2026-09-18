/-
The other half of the odometer-side Hölder combination: bounding the scenery-average of
`rNorm (walkLaw 2) 8 (orientedMax (orientedPotential η) n 0)` by the JOINT `L^8` norm
`Parking.exists_orientedMax_moment` controls.  The underlying inequality (a Fubini swap
identifying the iterated integral with the joint one, followed by Jensen's inequality for the
concave map `t ↦ t^{1/r}`) is the GENERIC fact `Parking.Generic.ProductMoment.
integral_rpow_root_le_prod_rpow_root`; this file only instantiates it at `μ := walkLaw 2`,
`ν := iidLaw 2 (realLaw ν)`, `F p η := orientedMax (orientedPotential η) n 0 p`, `r := 8`.
-/
import Parking.Support.TightHappHolder
import Parking.Support.OrientedMaxMoment
import Parking.Support.CriticalLawReal
import Parking.Support.TightMoment
import Parking.Generic.ProductMoment

open MeasureTheory Filter Topology LatticeProb

noncomputable section

namespace Parking

/-- **The scenery-average of the `L^8` norm of `Parking.orientedMax` is bounded by the joint
`L^8` norm**, uniform in the scale `n`, for any critical law, and is itself integrable in the
scenery. -/
theorem exists_integral_rNorm_orientedMax_le (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      Integrable (fun η => rNorm (walkLaw 2) 8 (orientedMax (orientedPotential η) n 0))
        (iidLaw 2 (realLaw ν)) ∧
      ∫ η, rNorm (walkLaw 2) 8 (orientedMax (orientedPotential η) n 0)
        ∂(iidLaw 2 (realLaw ν)) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  obtain ⟨C, hC, hmom⟩ := exists_orientedMax_moment (realLaw ν) 8 (by norm_num)
    (integrable_rpow_realLaw ν hν 8 (by norm_num)) (realLaw_mean ν hν)
  refine ⟨C, hC, fun n hn => ?_⟩
  haveI := stepLaw_isProbability (d := 2) (by norm_num)
  haveI : IsProbabilityMeasure (walkLaw 2) := by unfold walkLaw; infer_instance
  haveI : IsProbabilityMeasure (iidLaw 2 (realLaw ν)) := by unfold iidLaw; infer_instance
  set F : ((ℕ → Fin 2 × Bool) → (Site 2 → ℝ) → ℝ) :=
    fun p η => orientedMax (orientedPotential η) n 0 p with hFdef
  obtain ⟨hgi_joint, hrnorm⟩ := hmom n hn
  have hF0 : ∀ p η, 0 ≤ F p η := fun p η => orientedMax_nonneg _ n 0 p
  have hFi : Integrable (fun ω : (ℕ → Fin 2 × Bool) × (Site 2 → ℝ) => F ω.1 ω.2 ^ (8:ℝ))
      ((walkLaw 2).prod (iidLaw 2 (realLaw ν))) := by
    refine hgi_joint.congr (Filter.Eventually.of_forall fun ω => ?_)
    exact congrArg (· ^ (8:ℝ)) (abs_of_nonneg (hF0 ω.1 ω.2))
  obtain ⟨hjensen_int, hjensen_bound⟩ := Generic.ProductMoment.integral_rpow_root_le_prod_rpow_root
    (walkLaw 2) (iidLaw 2 (realLaw ν)) F hF0 (r := 8) (by norm_num) hFi
  have heqlhs : (fun η => (∫ p, F p η ^ (8:ℝ) ∂(walkLaw 2)) ^ ((1:ℝ)/8))
      = fun η => rNorm (walkLaw 2) 8 (orientedMax (orientedPotential η) n 0) := by
    funext η
    have heq : (fun p => F p η ^ (8:ℝ)) = fun p => |orientedMax (orientedPotential η) n 0 p| ^ (8:ℝ) := by
      funext p
      rw [abs_of_nonneg (orientedMax_nonneg (orientedPotential η) n 0 p)]
    unfold rNorm
    rw [heq]
  rw [heqlhs] at hjensen_int hjensen_bound
  have hrhseq : (∫ ω : (ℕ → Fin 2 × Bool) × (Site 2 → ℝ), F ω.1 ω.2 ^ (8:ℝ)
      ∂((walkLaw 2).prod (iidLaw 2 (realLaw ν)))) ^ ((1:ℝ)/8) = rNorm
      ((walkLaw 2).prod (iidLaw 2 (realLaw ν))) 8
      (fun ω => orientedMax (orientedPotential ω.2) n 0 ω.1) := by
    unfold rNorm
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    exact congrArg (· ^ (8:ℝ)) (abs_of_nonneg (hF0 ω.1 ω.2)).symm
  rw [hrhseq] at hjensen_bound
  exact ⟨hjensen_int, hjensen_bound.trans hrnorm⟩

end Parking

end
