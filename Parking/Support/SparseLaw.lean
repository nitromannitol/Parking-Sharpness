/-
Integrability and the critical-law hypotheses for the symmetric three-point law.
-/
import Parking.Support.ClosePair
import Parking.Support.CriticalLawReal

noncomputable section
namespace Parking
open MeasureTheory

/-- Every function of the three-point count has a finite integral. -/
theorem integrable_threePointLaw (p : ℝ) (f : ℤ → ℝ) : Integrable f (threePointLaw p) := by
  unfold threePointLaw
  exact (((integrable_dirac (f := f) (by finiteness)).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((integrable_dirac (f := f) (by finiteness)).smul_measure ENNReal.ofReal_ne_top)).add_measure
      ((integrable_dirac (f := f) (by finiteness)).smul_measure ENNReal.ofReal_ne_top)

/-- The integral under the sparse symmetric count law. -/
theorem integral_threePointLaw {p : ℝ} (hp : 0 ≤ p) (hp2 : 2 * p ≤ 1) (f : ℤ → ℝ) :
    ∫ k, f k ∂(threePointLaw p) = p * f 1 + p * f (-1) + (1 - 2 * p) * f 0 := by
  have h1 : Integrable f (ENNReal.ofReal p • Measure.dirac (1 : ℤ)) :=
    (integrable_dirac (f := f) (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  have hm1 : Integrable f (ENNReal.ofReal p • Measure.dirac (-1 : ℤ)) :=
    (integrable_dirac (f := f) (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  have h0 : Integrable f (ENNReal.ofReal (1 - 2 * p) • Measure.dirac (0 : ℤ)) :=
    (integrable_dirac (f := f) (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  rw [threePointLaw, integral_add_measure (h1.add_measure hm1) h0, integral_add_measure h1 hm1]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hp,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - 2 * p), smul_eq_mul]

/-- The sparse symmetric law is a nonconstant critical law. -/
theorem criticalLaw_threePointLaw {p : ℝ} (hp : 0 < p) (hp2 : 2 * p ≤ 1) :
    CriticalLaw (threePointLaw p) := by
  refine ⟨threePointLaw_isProbability hp.le hp2, ?_, ?_, ⟨1, by norm_num,
    integrable_threePointLaw p _⟩⟩
  · intro k
    apply ne_of_lt
    by_cases hk1 : k = 1
    · subst k
      have heq : threePointLaw p {(1 : ℤ)} = ENNReal.ofReal p := by
        simp [threePointLaw]
      rw [heq]
      exact ENNReal.ofReal_lt_one.mpr (by linarith)
    · by_cases hkm : k = -1
      · subst k
        rw [threePointLaw_singleton_neg]
        exact ENNReal.ofReal_lt_one.mpr (by linarith)
      · by_cases hk0 : k = 0
        · subst k
          rw [threePointLaw_singleton_zero]
          exact ENNReal.ofReal_lt_one.mpr (by linarith)
        · have heq : threePointLaw p {k} = 0 := by
            simp [threePointLaw, Ne.symm hk1, Ne.symm hkm, Ne.symm hk0]
          rw [heq]; exact zero_lt_one
  · rw [integral_threePointLaw hp.le hp2]
    norm_num
end Parking
