/-
The mean of the directed particle odometer is bounded by the directed divisible
mean plus the two error terms (`parking.tex:3300-3312`).
-/
import Parking.Support.OrientedComparison
import Parking.Support.OrientedCountLaw
import Parking.Support.OrientedOdometer

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The directed particle mean is at most the directed divisible mean plus the
absolute error field and the maximal walk average, both integrated. -/
theorem meanU_oriented_le_meanu_add_errors (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (n : ℕ)
    (hU : Integrable (fun ω : Data d => (U ω n 0 : ℝ)) (orientedLaw d ν))
    (hu : Integrable (fun ω : Data d => uOriented (fun y => (ω.1 y : ℝ)) n 0)
      (orientedLaw d ν))
    (hw : Integrable (fun ω : Data d => |wErrOriented ω.1 ω.2.1 n 0|) (orientedLaw d ν))
    (hs : Integrable (fun ω : Data d => wStarOriented ω.1 ω.2.1 n 0) (orientedLaw d ν)) :
    meanU (orientedLaw d ν) n ≤ meanuOriented (orientedLaw d ν) n +
      (∫ ω : Data d, |wErrOriented ω.1 ω.2.1 n 0| ∂(orientedLaw d ν)) +
      (∫ ω : Data d, wStarOriented ω.1 ω.2.1 n 0 ∂(orientedLaw d ν)) := by
  have hae := orientedOdometer_ae_eq_U (d := d) hd ν n 0
  have hpt : ∀ᵐ ω ∂(orientedLaw d ν), (U ω n 0 : ℝ) ≤ uOriented (fun y => (ω.1 y : ℝ)) n 0 +
      |wErrOriented ω.1 ω.2.1 n 0| + wStarOriented ω.1 ω.2.1 n 0 := by
    filter_upwards [hae] with ω hω
    rw [← hω]
    exact orientedOdometer_le_u_add_abs_wErr_add_wStar hd ω.1 ω.2.1 n 0
  have hsum : Integrable (fun ω : Data d => uOriented (fun y => (ω.1 y : ℝ)) n 0 +
      |wErrOriented ω.1 ω.2.1 n 0| + wStarOriented ω.1 ω.2.1 n 0) (orientedLaw d ν) :=
    (hu.add hw).add hs
  have h := integral_mono_ae hU hsum hpt
  have hsplit : (∫ ω : Data d, uOriented (fun y => (ω.1 y : ℝ)) n 0 +
      |wErrOriented ω.1 ω.2.1 n 0| + wStarOriented ω.1 ω.2.1 n 0 ∂(orientedLaw d ν)) =
      (∫ ω : Data d, uOriented (fun y => (ω.1 y : ℝ)) n 0 ∂(orientedLaw d ν)) +
      (∫ ω : Data d, |wErrOriented ω.1 ω.2.1 n 0| ∂(orientedLaw d ν)) +
      (∫ ω : Data d, wStarOriented ω.1 ω.2.1 n 0 ∂(orientedLaw d ν)) := by
    have h1 := integral_add (hu.add hw) hs
    have h2 := integral_add hu hw
    simp only [Pi.add_apply] at h1 h2
    linarith [h1, h2]
  rw [hsplit] at h
  simpa only [meanU, meanuOriented] using h

end Parking
