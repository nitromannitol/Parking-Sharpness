/- Positive variance excludes a point mass for an integer law. -/
import Parking.Support.CriticalLawReal

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory

theorem nonconstant_of_evariance_pos (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hv : 0 < evariance (fun k : ℤ => (k : ℝ)) ν) : ∀ k : ℤ, ν {k} ≠ 1 := by
  intro k hk
  have ha : ∀ᵐ z : ℤ ∂ν, z ∈ ({k} : Set ℤ) :=
    (mem_ae_iff_prob_eq_one (measurableSet_singleton k)).mpr hk
  have he : (fun z : ℤ => (z : ℝ)) =ᵐ[ν] fun _ => (k : ℝ) :=
    ha.mono fun z hz => by rw [Set.mem_singleton_iff.mp hz]
  have hm : (∫ z : ℤ, (z : ℝ) ∂ν) = (k : ℝ) := by
    rw [integral_congr_ae he, integral_const, probReal_univ, one_smul]
  have hz : evariance (fun z : ℤ => (z : ℝ)) ν = 0 := by
    apply (evariance_eq_zero_iff measurable_intCastReal.aemeasurable).mpr
    simpa only [hm] using he
  exact hv.ne' hz

end Parking
