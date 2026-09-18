/-
Hölder's inequality applied to the bad-event integral (task item (2)): for a FIXED scenery
`η`, `∫ p, indicator(walkBad) (orientedMax (orientedPotential η) n 0) p ∂walkLaw` is bounded by
`(walkLaw.real bad)^{7/8}` times the `L^8` norm of `orientedMax`.  The Hölder inequality itself
(a tail bound combined with a moment bound, at conjugate exponents `8/7` and `8`) is the
GENERIC fact `Parking.Generic.Holder.integral_indicator_le_measureReal_rpow_mul_rMoment`; this
file only instantiates it at `μ := walkLaw 2`, `S := Parking.walkBad n A`, `g := Parking.
orientedMax (orientedPotential η) n 0`.  `Parking.exists_orientedMax_moment` supplies the
`n`-uniform `L^8` bound afterward.
-/
import Parking.Support.TightHappTerminal
import Parking.Generic.Holder

open MeasureTheory Filter Topology LatticeProb

noncomputable section

namespace Parking

/-- **Hölder's inequality for the bad-event integral of `Parking.orientedMax`**, at the
conjugate pair `(8/7, 8)`. -/
theorem integral_indicator_orientedMax_le {A : ℝ} (_hA : 0 < A) (n : ℕ) (η : Site 2 → ℝ)
    (hgi : Integrable (fun p => |orientedMax (orientedPotential η) n 0 p| ^ (8 : ℝ))
      (walkLaw 2)) :
    ∫ p, Set.indicator (walkBad n A) (orientedMax (orientedPotential η) n 0) p ∂(walkLaw 2)
      ≤ ((walkLaw 2).real (walkBad n A)) ^ ((7 : ℝ) / 8) *
          rNorm (walkLaw 2) 8 (orientedMax (orientedPotential η) n 0) := by
  haveI := stepLaw_isProbability (d := 2) (by norm_num)
  haveI : IsProbabilityMeasure (walkLaw 2) := by unfold walkLaw; infer_instance
  have hg0 : 0 ≤ᵐ[walkLaw 2] orientedMax (orientedPotential η) n 0 :=
    Filter.Eventually.of_forall (fun p => orientedMax_nonneg _ n 0 p)
  have hgm : AEStronglyMeasurable (orientedMax (orientedPotential η) n 0) (walkLaw 2) :=
    (measurable_orientedMax (by norm_num) (orientedPotential η) n 0).aestronglyMeasurable
  have hmain := Generic.Holder.integral_indicator_le_measureReal_rpow_mul_rMoment (walkLaw 2)
    (walkBad n A) (measurableSet_walkBad n A) (orientedMax (orientedPotential η) n 0) hgm hg0
    (r := 8) (by norm_num) hgi
  have hexp : (1:ℝ) - 1/8 = (7:ℝ)/8 := by norm_num
  rw [hexp] at hmain
  have hrnorm_eq : Generic.Holder.rMoment (walkLaw 2) 8 (orientedMax (orientedPotential η) n 0)
      = rNorm (walkLaw 2) 8 (orientedMax (orientedPotential η) n 0) := rfl
  rwa [hrnorm_eq] at hmain

end Parking

end
