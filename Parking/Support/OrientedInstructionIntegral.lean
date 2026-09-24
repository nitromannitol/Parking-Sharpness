/- Integrals and atom masses for a directed particle instruction. -/
import Parking.Support.OrientedKernel
import Parking.Support.OrientedLaw

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

theorem integral_orientedInstructionLaw (f : Site d → ℝ) (y : Site d) :
    (∫ z, f z ∂(orientedInstructionLaw y)) = (∑ i : Fin d, f (y + unit i)) / d := by
  have hi : ∀ z : Site d, Integrable f (Measure.dirac z) := fun z => integrable_dirac (by simp)
  rw [orientedInstructionLaw, integral_smul_measure,
    integral_finsetSum_measure (fun i _ => hi (y + unit i))]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, div_eq_inv_mul]

theorem orientedInstructionLaw_forward_mass (y : Site d) (i : Fin d) :
    (orientedInstructionLaw y).real {y + unit i} = (d : ℝ)⁻¹ := by
  classical
  rw [← integral_indicator_one (μ := orientedInstructionLaw y) (measurableSet_singleton _),
    integral_orientedInstructionLaw]
  have hterm (j : Fin d) : Set.indicator {y + unit i} (fun _ => (1 : ℝ)) (y + unit j) =
      if j = i then 1 else 0 := by
    simp only [Set.indicator_apply, Set.mem_singleton_iff, add_right_inj, unit_injective.eq_iff]
  change (∑ j : Fin d, Set.indicator {y + unit i} (fun _ => (1 : ℝ)) (y + unit j)) / d = _
  simp only [hterm, sum_ite_eq', mem_univ, if_true, one_div]

theorem orientedInstructionLaw_miss_mass (hd : 1 ≤ d) (y : Site d) (i : Fin d) :
    (orientedInstructionLaw y).real {y + unit i}ᶜ = 1 - (d : ℝ)⁻¹ := by
  haveI := orientedInstructionLaw_isProbability hd y
  rw [probReal_compl_eq_one_sub (measurableSet_singleton _), orientedInstructionLaw_forward_mass]

end Parking
