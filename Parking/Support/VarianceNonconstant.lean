import Parking.Support.CriticalLawReal

/-!
# Positive variance excludes a point mass

Positive variance excludes a point mass for an integer law.
-/

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory

/-- **A law with positive variance is not a point mass.**  If `ν {k} = 1` for some `k`, then
`ν`-almost every integer equals `k`, forcing the mean to be `k` and the variance to vanish,
contradicting `hv`. -/
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
