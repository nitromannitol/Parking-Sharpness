/-
The variance and correlation estimates of sandpile.tex:1117-1240, cited
from Lawler-Limic, Propositions 2.4.1, 2.4.4, 2.4.6 and Theorem 4.3.1.
These are the explicit VarianceScale hypothesis of the sealed sibling
critical_toppling, used at parking.tex:1807-1833. Assumed here.
-/
import Parking.Support.NearestCriticalModel

open MeasureTheory ProbabilityTheory

-- FROZEN-STATEMENT-BEGIN
/-- The finite-time variance scale `eq:Qt-table`, the membrane correlation bound
`eq:corr-bound`, and the dimension-four window and tail bounds
`eq:d4-window-l2`, `eq:d4-window-linfty` and `eq:d4-full-window-bounds` of
`ssec:green-estimates`, all in their scenery-free Green-kernel form.  Assumed,
not proved. -/
def Parking.External.VarianceScale : Prop :=
  (∀ d : ℕ, 1 ≤ d →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ t : ℕ, 2 ≤ t →
          c * Parking.CriticalScale.varianceRate d t ≤
              ∑' y : Parking.Site d, Parking.CriticalScale.greenTime d t 0 y ^ 2 ∧
            (∑' y : Parking.Site d, Parking.CriticalScale.greenTime d t 0 y ^ 2) ≤
              C * Parking.CriticalScale.varianceRate d t) ∧
  (∀ d : ℕ, 1 ≤ d → d ≤ 4 →
      ∃ C : ℝ, 0 < C ∧
        ∀ m n : ℕ, 1 ≤ m → m ≤ n →
          (∑' x : Parking.Site d,
              Parking.CriticalScale.greenTime d m 0 x * Parking.CriticalScale.greenTime d n 0 x) ≤
            C * Parking.CriticalScale.corrRate d m n *
              Real.sqrt (∑' x : Parking.Site d, Parking.CriticalScale.greenTime d m 0 x ^ 2) *
              Real.sqrt (∑' x : Parking.Site d, Parking.CriticalScale.greenTime d n 0 x ^ 2)) ∧
  (∃ C : ℝ, 0 < C ∧
      (∀ m n : ℕ, 1 ≤ m → m < n → ∀ x : Parking.Site 4,
          (∑' z : Parking.Site 4,
              Parking.CriticalScale.windowKernel m n x z ^ 2) ≤
            C * (1 + Real.log (((n : ℝ) + 2) / ((m : ℝ) + 2))) ∧
          ∀ z : Parking.Site 4,
            Parking.CriticalScale.windowKernel m n x z ≤ C / (m : ℝ)) ∧
      (∀ n : ℕ, 2 ≤ n → ∀ x : Parking.Site 4,
          (∑' z : Parking.Site 4, Parking.CriticalScale.greenTime 4 n x z ^ 2) ≤
            C * Real.log ((n : ℝ) + 2) ∧
          ∀ z : Parking.Site 4, Parking.CriticalScale.greenTime 4 n x z ≤ C))
-- FROZEN-STATEMENT-END
