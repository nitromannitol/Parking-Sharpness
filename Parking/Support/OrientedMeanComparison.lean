/- The directed divisible mean is bounded by the actual particle mean. -/
import Parking.Support.OrientedGivenComparison
import Parking.Support.OrientedCountLaw
import Parking.Support.OrientedFinite

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

theorem meanuOriented_le_meanU (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν) (n : ℕ) :
    meanuOriented (orientedLaw d ν) n ≤ meanU (orientedLaw d ν) n := by
  haveI := hν.prob
  haveI := orientedStackLaw_isProbability hd
  haveI := LatticeProb.rankLaw_isProbability d
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  let f : (Site d → ℤ) → ℝ := fun η => uOriented (fun y => (η y : ℝ)) n 0
  have hm : Measurable f := (measurable_uOriented n 0).comp
    (measurable_pi_lambda _ fun y => measurable_intCastReal.comp (measurable_pi_apply y))
  have hI := (integrable_orientedOdometer_joint hd ν hν n 0).integral_prod_left
  have hfI : Integrable f (iidLaw d ν) := hI.mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun η => by
      rw [Real.norm_eq_abs, abs_of_nonneg (uOriented_nonneg _ n 0)]
      exact uOriented_le_mean_orientedOdometer hd η n 0)
  have hle := integral_mono hfI hI (fun η => uOriented_le_mean_orientedOdometer hd η n 0)
  rw [integral_orientedOdometer_given_mean hd ν hν n 0] at hle
  have he : meanuOriented (orientedLaw d ν) n = ∫ η, f η ∂(iidLaw d ν) := by
    have h := integral_map (μ := orientedLaw d ν) (φ := Prod.fst) (f := f)
      measurable_fst.aemeasurable hm.aestronglyMeasurable
    rw [orientedLaw_map_conf hd ν] at h
    exact h.symm
  rw [he]
  exact hle

end Parking
