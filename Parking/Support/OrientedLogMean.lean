/- The logarithmic divisible mean bound under the oriented parking law. -/
import Parking.Support.OrientedMaxLog
import Parking.Support.OrientedFirstMoment
import Parking.Support.OrientedLaw

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

theorem exists_uOriented_log_mean (hd : 3 ≤ d)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (id : ℝ → ℝ) μ) (hm : ∫ z : ℝ, z ∂μ = 0)
    {θ : ℝ} (hθ : 0 < θ) (he : Integrable (fun z : ℝ => Real.exp (θ * |z|)) μ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (∫ η : Site d → ℝ, uOriented η n 0 ∂(iidLaw d μ)) ≤ C * Real.log ((n : ℝ) + 1) := by
  have hd1 : 1 ≤ d := by omega
  haveI := stepLaw_isProbability (d := d) hd1
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  haveI : IsProbabilityMeasure (iidLaw d μ) := by unfold iidLaw; infer_instance
  obtain ⟨C, hC, hb⟩ := exists_orientedMax_log_mean hd μ hi hm hθ he
  refine ⟨2 * C, by positivity, fun n hn => ?_⟩
  obtain ⟨hMi, hMb⟩ := hb n hn
  let M : ((ℕ → Fin d × Bool) × (Site d → ℝ)) → ℝ :=
    fun ω => orientedMax (orientedPotential ω.2) n 0 ω.1
  have hmeanI : Integrable (fun η : Site d → ℝ => orientedMaxMean (orientedPotential η) n 0)
      (iidLaw d μ) := hMi.integral_prod_right
  have hpt (η : Site d → ℝ) : uOriented η n 0 ≤ 2 * orientedMaxMean (orientedPotential η) n 0 := by
    have h := uOriented_le_potential_add_max hd1 η n 0
    have h' := abs_le_orientedMaxMean hd1 (orientedPotential η) n 0
    linarith [le_abs_self (orientedPotential η n 0)]
  have hraw := integral_mono (integrable_uOriented_iid μ hi n 0) (hmeanI.const_mul 2) hpt
  rw [integral_const_mul] at hraw
  have hF : (∫ η : Site d → ℝ, orientedMaxMean (orientedPotential η) n 0 ∂(iidLaw d μ)) =
      ∫ ω, M ω ∂((walkLaw d).prod (iidLaw d μ)) := (integral_prod_symm M hMi).symm
  rw [hF] at hraw
  have hmul := mul_le_mul_of_nonneg_left hMb (by norm_num : (0 : ℝ) ≤ 2)
  exact hraw.trans (by simpa only [mul_assoc] using hmul)

theorem exists_meanuOriented_log_upper (hd : 3 ≤ d)
    (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k : ℤ, (k : ℝ) ∂ν = 0) {θ : ℝ} (hθ : 0 < θ)
    (he : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      meanuOriented (orientedLaw d ν) n ≤ C * Real.log ((n : ℝ) + 1) := by
  have hμi : Integrable (id : ℝ → ℝ) (realLaw ν) := by
    apply (realLaw_integrable_iff ν measurable_id).mpr
    exact hint.mono' measurable_intCastReal.aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => by simp only [Real.norm_eq_abs]; rfl)
  have hμm : (∫ z : ℝ, z ∂(realLaw ν)) = 0 := (realLaw_integral ν measurable_id).trans hmean
  have hμe : Integrable (fun z : ℝ => Real.exp (θ * |z|)) (realLaw ν) :=
    (realLaw_integrable_iff ν (measurable_abs.const_mul θ).exp).mpr he
  obtain ⟨C, hC, hb⟩ := exists_uOriented_log_mean hd (realLaw ν) hμi hμm hθ hμe
  refine ⟨C, hC, fun n hn => ?_⟩
  have hbridge : meanuOriented (orientedLaw d ν) n =
      ∫ η : Site d → ℝ, uOriented η n 0 ∂(iidLaw d (realLaw ν)) :=
    integral_oriented_confReal (by omega) ν (measurable_uOriented n 0)
  rw [hbridge]
  exact hb n hn

end Parking
