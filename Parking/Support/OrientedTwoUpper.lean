/- Step 2 of the oriented walk theorem: the dimension-two upper bound on the
directed particle mean, from the eighth moment and Young's inequality. -/
import Parking.Support.OrientedMeanBound
import Parking.Support.OrientedYoung
import Parking.Support.OrientedMoments
import Parking.Support.UpperTarget

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Step 2 of `thm:oriented-walk` (`parking.tex:3282-3294`): the `r = 8` moment
inequality of the directed `prop:w-moment` and Young's inequality give the
`n^{1/4}` upper bound on the directed particle mean at `d = 2`. -/
theorem meanU_oriented_two_upper_of_moment (ν : Measure ℤ) (hν : CriticalLaw ν)
    (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ n : ℕ, 1 ≤ n →
      (∫ ω : Data 2, (U ω n 0 : ℝ) ^ (8 : ℝ) ∂(orientedLaw 2 ν)) ^ ((1 : ℝ) / 8) ≤
        C * (n : ℝ) ^ ((1 : ℝ) / 4) +
          C * (n : ℝ) ^ ((1 : ℝ) / 8) *
            ((∫ ω : Data 2, (U ω n 0 : ℝ) ^ (8 : ℝ) ∂(orientedLaw 2 ν)) ^ ((1 : ℝ) / 16) + 1)) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ n : ℕ, 1 ≤ n →
      meanU (orientedLaw 2 ν) n ≤ C' * (n : ℝ) ^ ((1 : ℝ) / 4) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (orientedLaw 2 ν) := orientedLaw_isProbability (by norm_num) ν
  obtain ⟨θ, hθ, he⟩ := hν.expMoment
  refine ⟨2 * C + C ^ 2 + 2 * C + 1, by positivity, fun n hn => ?_⟩
  set X : ℝ := (∫ ω : Data 2, (U ω n 0 : ℝ) ^ (8 : ℝ) ∂(orientedLaw 2 ν)) ^ ((1 : ℝ) / 8) with hXdef
  have hI0 : 0 ≤ ∫ ω : Data 2, (U ω n 0 : ℝ) ^ (8 : ℝ) ∂(orientedLaw 2 ν) :=
    integral_nonneg fun ω => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hX0 : 0 ≤ X := Real.rpow_nonneg hI0 _
  have hstep : X ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4) + C * (n : ℝ) ^ ((1 : ℝ) / 8) * (Real.sqrt X + 1) := by
    have h1 := h n hn
    rw [hXdef]
    rw [rpow_sixteenth_eq_sqrt_eighth hI0] at h1
    exact h1
  have habs := oriented_two_absorb hX0 hC hn hstep
  have hle : meanU (orientedLaw 2 ν) n ≤ X := by
    rw [meanU]
    have h1 := integral_le_rNorm (μ := orientedLaw 2 ν) (r := (8 : ℝ)) (f := fun ω : Data 2 => (U ω n 0 : ℝ))
      (fun ω => Nat.cast_nonneg _) (integrable_oriented_U (d := 2) (by norm_num) ν hν n 0)
      (by norm_num) (integrable_oriented_U_rpow (d := 2) (by norm_num) ν hθ
        (integrable_expMax_of_expAbs hθ he) (by norm_num) n 0)
    rw [hXdef]
    exact h1
  calc meanU (orientedLaw 2 ν) n ≤ X := hle
    _ ≤ (2 * C + C ^ 2 + 2 * C) * (n : ℝ) ^ ((1 : ℝ) / 4) := habs
    _ ≤ (2 * C + C ^ 2 + 2 * C + 1) * (n : ℝ) ^ ((1 : ℝ) / 4) := by
        have : (0 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        nlinarith

end Parking
end
