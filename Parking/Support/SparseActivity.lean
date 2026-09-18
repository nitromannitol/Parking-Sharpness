import Parking.Support.ClippedTable
import Parking.Support.ClippedRoundMean
import Parking.Support.IndicatorIntegral

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
open scoped Classical
variable {d : ℕ}

theorem ae_sparse_H_le_one {p : ℝ} (hp : 0 < p) (hp4 : p ≤ 1 / 4)
    (t : ℕ) (x : Site d) : ∀ᵐ ω ∂(law d (threePointLaw p)), H ω t x ≤ 1 := by
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  haveI : IsProbabilityMeasure (iidLaw d (threePointLaw p)) := by unfold iidLaw; infer_instance
  have ha : ∀ᵐ ω ∂(law d (threePointLaw p)), clippedField ω.1 = ω.1 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_clippedField (threePointLaw p) (ae_clipSparse_threePointLaw p))
  filter_upwards [ha] with ω hω
  have hx := congrFun hω x
  have hlow : -1 ≤ ω.1 x := by
    rw [← hx]
    exact (clipSparse_bounds (ω.1 x)).1
  have h := holeCount_le_initial ω t x
  omega

theorem integral_sparse_H_eq_holeProb (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp4 : p ≤ 1 / 4)
    (t : ℕ) (x : Site d) :
    (∫ ω, (H ω t x : ℝ) ∂(law d (threePointLaw p))) = holeProb d (threePointLaw p) t := by
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  have he : (fun ω : Data d => (H ω t x : ℝ)) =ᵐ[law d (threePointLaw p)]
      (fun ω => if H ω t x = 1 then (1 : ℝ) else 0) := by
    filter_upwards [ae_sparse_H_le_one hp hp4 t x] with ω hω
    by_cases h : H ω t x = 1
    · simp only [h, if_true, Nat.cast_one]
    · have hz : H ω t x = 0 := by omega
      simp only [hz, zero_ne_one, if_false, Nat.cast_zero]
  have hS : MeasurableSet {ω : Data d | H ω t x = 1} := (measurable_H t x) (measurableSet_singleton 1)
  rw [integral_congr_ae he, integral_ite_one_zero _ (fun ω => H ω t x = 1) hS]
  exact holeProb_at_site hd _ t x

theorem sparse_activity_mean (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp4 : p ≤ 1 / 4) (t : ℕ) :
    Integrable (fun ω : Data d => (A ω t 0 : ℝ)) (law d (threePointLaw p)) ∧
      (∫ ω, (A ω t 0 : ℝ) ∂(law d (threePointLaw p))) = holeProb d (threePointLaw p) t := by
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  haveI : IsProbabilityMeasure (iidLaw d (threePointLaw p)) := by unfold iidLaw; infer_instance
  have hmp := measurePreserving_eval_infinitePi (fun _ : Site d => threePointLaw p) (0 : Site d)
  have hi : Integrable (fun η : Site d → ℤ => |(η 0 : ℝ)|) (iidLaw d (threePointLaw p)) :=
    by simpa only [iidLaw, Function.comp_def] using
      hmp.integrable_comp_of_integrable (integrable_threePointLaw p (fun k : ℤ => |(k : ℝ)|))
  have hti : TranslationInvariant (iidLaw d (threePointLaw p)) := fun v => iidLaw_map_shiftConf' _ v
  have hiA := integrable_A_data hd hti hi t 0
  have hbal := activity_holes_main hd hti hi t
  have hm : (∫ η : Site d → ℤ, (η 0 : ℝ) ∂(iidLaw d (threePointLaw p))) = 0 := by
    have hm : (iidLaw d (threePointLaw p)).map (fun η : Site d → ℤ => η 0) = threePointLaw p := hmp.map_eq
    have hf : AEStronglyMeasurable (fun k : ℤ => (k : ℝ))
        ((iidLaw d (threePointLaw p)).map (fun η : Site d → ℤ => η 0)) := by
      rw [hm]
      exact (measurable_from_countable' _).aestronglyMeasurable
    have h := integral_map (μ := iidLaw d (threePointLaw p)) (φ := fun η : Site d → ℤ => η 0)
      (measurable_pi_apply 0).aemeasurable hf
    rw [hm] at h
    exact h.symm.trans (criticalLaw_threePointLaw hp (by linarith)).mean
  have he : dataLaw d (iidLaw d (threePointLaw p)) = law d (threePointLaw p) := rfl
  rw [he] at hiA hbal
  rw [hm, integral_sparse_H_eq_holeProb hd hp hp4 t 0] at hbal
  exact ⟨hiA, sub_eq_zero.mp hbal⟩

end Parking
