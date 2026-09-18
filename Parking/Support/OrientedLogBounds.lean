/- Step 4 of the oriented walk theorem, two-sided form: at `d ≥ 3` the directed
particle mean is bounded above and below by constant multiples of `log n`
(`parking.tex:363-380`). -/
import Parking.Support.OrientedLogUpper
import Parking.Support.OrientedParticleLogLower

noncomputable section
namespace Parking
open MeasureTheory LatticeProb

/-- The logarithmic two-sided bound of `thm:oriented-walk` at `d ≥ 3`
(`parking.tex:363-380`), given the Step 4 moment inequality: the directed
particle mean is bounded above and below by constant multiples of `log n`. -/
theorem exists_meanU_oriented_log_bounds (d : ℕ) (hd : 3 ≤ d) (ν : Measure ℤ)
    (hν : CriticalLaw ν) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ n : ℕ, 1 ≤ n →
      (∫ ω : Data d, (U ω n 0 : ℝ) ^ (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ) ∂(orientedLaw d ν)) ^
          ((1 : ℝ) / (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ)) ≤
        C * Real.log ((n : ℝ) + 1) +
          C * (Real.sqrt ((2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ) *
            (∫ ω : Data d, (U ω n 0 : ℝ) ^ (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ) ∂(orientedLaw d ν)) ^
              ((1 : ℝ) / (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ))) +
            (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ))) :
    ∃ c C' : ℝ, 0 < c ∧ c ≤ C' ∧ ∀ n : ℕ, 2 ≤ n →
      c * Real.log n ≤ meanU (orientedLaw d ν) n ∧
        meanU (orientedLaw d ν) n ≤ C' * Real.log n := by
  haveI := hν.prob
  obtain ⟨c, hc, hlo⟩ := exists_meanU_oriented_log_lower (d := d) (by omega) ν hν
  obtain ⟨C', hC', hhi⟩ := meanU_oriented_log_upper_of_moment hd ν hν C hC h
  refine ⟨c, c + 2 * C', hc, by linarith, fun n hn => ⟨?_, ?_⟩⟩
  · have h2 : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    calc c * Real.log n ≤ c * Real.log ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by linarith)) hc.le
      _ ≤ _ := hlo n
  · have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
    have hlog2 : Real.log ((n : ℝ) + 1) ≤ 2 * Real.log n := by
      have h1 : Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) * (n : ℝ)) :=
        Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_mul (by linarith) (by linarith)] at h1
      linarith
    calc meanU (orientedLaw d ν) n ≤ C' * Real.log ((n : ℝ) + 1) := hhi n (by omega)
      _ ≤ C' * (2 * Real.log n) := mul_le_mul_of_nonneg_left hlog2 hC'.le
      _ ≤ (c + 2 * C') * Real.log n := by nlinarith

end Parking
