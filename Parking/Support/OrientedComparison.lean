/-
The pointwise form of the directed pathwise comparison
(`parking.tex:3300-3306`): the directed particle odometer is at most the
divisible odometer plus the two error terms.
-/
import Parking.Support.OrientedError

noncomputable section

namespace Parking

open MeasureTheory LatticeProb

variable {d : ℕ}

/-- The directed particle odometer is at most the divisible odometer plus the two error
terms, the pointwise form of the pathwise comparison `parking.tex:3300-3306`. -/
theorem orientedOdometer_le_u_add_abs_wErr_add_wStar (hd : 1 ≤ d) (η : Site d → ℤ)
    (σ : Site d × ℕ → Site d) (n : ℕ) (x : Site d) :
    (orientedOdometer η σ n x : ℝ) ≤ uOriented (fun y => (η y : ℝ)) n x +
      |wErrOriented η σ n x| + wStarOriented η σ n x := by
  have h := Parking.abs_orientedOdometer_sub_wErr_sub_u_le hd η σ n x
  have h2 := abs_le.mp h
  have h3 : wErrOriented η σ n x ≤ |wErrOriented η σ n x| := le_abs_self _
  linarith [h2.1, h3]

end Parking

end
