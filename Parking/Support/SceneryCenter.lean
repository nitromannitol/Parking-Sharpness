import Parking.Support.SceneryLaw
import Parking.Support.TableLaw
import Parking.Support.WMomentProof

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The spatial odometer means coincide under the independent identically distributed field law. -/
theorem integral_U_shift (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (T : ℕ) (x : Site d) :
    ∫ ω, (U ω T x : ℝ) ∂(law d ν) = meanU (law d ν) T := by
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  have hm : AEStronglyMeasurable (fun ω : Data d => (U ω T x : ℝ)) (dataLaw d (iidLaw d ν)) :=
    ((measurable_from_countable' fun n : ℕ => (n : ℝ)).comp (measurable_U T x)).aestronglyMeasurable
  have h := integral_comp_shiftData (μ := iidLaw d ν) hd (fun y => iidLaw_map_shiftConf' ν y) (-x) hm
  have hlaw : law d ν = dataLaw d (iidLaw d ν) := rfl
  rw [← hlaw] at h
  simpa only [U_shiftData, add_neg_cancel, meanU] using h.symm

/-- The conditional table mean is centered at the paper's scalar odometer mean. -/
theorem integral_matchedMeanU_eq_meanU (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (T : ℕ) (x : Site d) :
    ∫ η, matchedMeanU η 0 T x ∂(iidLaw d ν) = meanU (law d ν) T := by
  rw [integral_matchedMeanU hd ν hint T x, integral_U_shift hd ν T x]
end Parking
