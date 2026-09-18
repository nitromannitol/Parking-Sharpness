/- Probability and scenery marginals of the oriented parking law. -/
import Parking.Support.CriticalLawReal

noncomputable section
namespace Parking
open LatticeProb MeasureTheory Finset
variable {d : ℕ}

theorem orientedInstructionLaw_isProbability (hd : 1 ≤ d) (y : Site d) :
    IsProbabilityMeasure (orientedInstructionLaw y) := by
  constructor
  simp only [orientedInstructionLaw, Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply, Measure.dirac_apply, Set.indicator_of_mem, Set.mem_univ,
    Pi.one_apply, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast (show d ≠ 0 by omega)) (by simp)

theorem orientedStackLaw_isProbability (hd : 1 ≤ d) :
    IsProbabilityMeasure (orientedStackLaw d) := by
  haveI : ∀ p : Site d × ℕ, IsProbabilityMeasure (orientedInstructionLaw p.1) :=
    fun p => orientedInstructionLaw_isProbability hd p.1
  unfold orientedStackLaw
  infer_instance

theorem orientedLaw_isProbability (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (orientedLaw d ν) := by
  haveI := orientedStackLaw_isProbability hd
  haveI := LatticeProb.rankLaw_isProbability d
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  unfold orientedLaw
  infer_instance

theorem orientedLaw_map_confReal (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    (orientedLaw d ν).map (fun ω : Data d => confReal ω) = iidLaw d (realLaw ν) := by
  haveI := orientedStackLaw_isProbability hd
  haveI := LatticeProb.rankLaw_isProbability d
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  let f : (Site d → ℤ) → Site d → ℝ := fun η y => (η y : ℝ)
  have hf : Measurable f := measurable_pi_lambda _ fun y =>
    measurable_intCastReal.comp (measurable_pi_apply y)
  have hcomp : (fun ω : Data d => confReal ω) = f ∘ Prod.fst := rfl
  rw [hcomp, ← Measure.map_map hf measurable_fst, orientedLaw, Measure.map_fst_prod]
  simp only [measure_univ, one_smul, iidLaw, realLaw]
  exact Measure.infinitePi_map_pi _ (fun _ : Site d => measurable_intCastReal)

theorem integral_oriented_confReal (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {G : (Site d → ℝ) → ℝ} (hG : Measurable G) :
    (∫ ω, G (confReal ω) ∂(orientedLaw d ν)) = ∫ η, G η ∂(iidLaw d (realLaw ν)) := by
  have h := integral_map (μ := orientedLaw d ν) (φ := fun ω : Data d => confReal ω) (f := G)
    measurable_confReal.aemeasurable hG.aestronglyMeasurable
  rw [orientedLaw_map_confReal hd ν] at h
  exact h.symm

end Parking
