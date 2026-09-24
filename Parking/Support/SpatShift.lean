/-
The translation invariance of the i.i.d. scenery law, read as an invariance of
the integral: for a measurable `g`, integrating `g` against the pushforward of
the law by a spatial shift equals integrating `g` directly.

This is the integral form of `Parking.iidLaw_map_shiftConf`
(`Parking/Support/Invariance.lean`), the input the Kolmogorov route to the
equicontinuity clause of `prop:spatial-scaling` needs at every site.
-/
import Parking.Support.Invariance

noncomputable section
namespace Parking
open MeasureTheory LatticeProb

variable {d : ℕ}

/-- The integral of a measurable `g` is invariant under pushing the i.i.d. law
through a spatial shift of the scenery. -/
theorem integral_shift_iidLaw (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (v : Site d) {g : (Site d → ℝ) → ℝ} (hg : Measurable g) :
    ∫ η, g (fun x => η (x + v)) ∂(iidLaw d ν) = ∫ η, g η ∂(iidLaw d ν) := by
  have hmap : ((iidLaw d ν).map (fun η : Site d → ℝ => fun x => η (x + v))) = iidLaw d ν :=
    Parking.iidLaw_map_shiftConf ν v
  have hmeas : Measurable (fun η : Site d → ℝ => fun x => η (x + v)) := by fun_prop
  rw [← integral_map hmeas.aemeasurable hg.aestronglyMeasurable, hmap]

end Parking

end