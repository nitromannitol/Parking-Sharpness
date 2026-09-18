/- All polynomial moments of the directed divisible odometer.

The divisible odometer at a site is at most the absolute scenery of the box it
reads, and a critical scenery has an exponential moment, so every power of the
divisible odometer is integrable under the directed law.
-/
import Parking.Support.OrientedMoments
import Parking.Support.OrientedFirstMoment
import Parking.Support.ConfMoments
import Parking.Support.OrientedFinite

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

theorem orientedLaw_map_conf_eval (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (z : Site d) : (orientedLaw d ν).map (fun ω : Data d => ω.1 z) = ν := by
  have h1 : (fun ω : Data d => ω.1 z)
      = (fun η : Site d → ℤ => η z) ∘ (Prod.fst : Data d → (Site d → ℤ)) := rfl
  rw [h1, ← Measure.map_map (measurable_pi_apply z) measurable_fst,
    orientedLaw_map_conf hd ν]
  exact Measure.infinitePi_map_eval _ z

theorem integrable_oriented_abs_conf_rpow (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν)
    {r : ℝ} (hr : 0 ≤ r) (z : Site d) :
    Integrable (fun ω : Data d => |(ω.1 z : ℝ)| ^ r) (orientedLaw d ν) := by
  obtain ⟨C, hC, hbound⟩ := rpow_le_const_mul_exp hr hθ
  have hg : Integrable (fun k : ℤ => |(k : ℝ)| ^ r) ν := by
    refine Integrable.mono' (hexp.const_mul C)
      (measurable_from_countable' (fun k : ℤ => |(k : ℝ)| ^ r)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) r)]
    exact hbound _ (abs_nonneg _)
  have hmeas : AEMeasurable (fun ω : Data d => ω.1 z) (orientedLaw d ν) :=
    ((measurable_pi_apply z).comp measurable_fst).aemeasurable
  have hg2 : Integrable (fun k : ℤ => |(k : ℝ)| ^ r)
      ((orientedLaw d ν).map (fun ω : Data d => ω.1 z)) := by
    rw [orientedLaw_map_conf_eval hd ν z]; exact hg
  exact (integrable_map_measure
    (measurable_from_countable' (fun k : ℤ => |(k : ℝ)| ^ r)).aestronglyMeasurable hmeas).mp hg2

/-- The absolute scenery of a box: the sum of the absolute values of the
scenery over the box. -/
def absBox (ω : Data d) (x : Site d) (R : ℕ) : ℝ := ∑ z ∈ boxFinset x R, |(ω.1 z : ℝ)|

theorem absBox_nonneg (ω : Data d) (x : Site d) (R : ℕ) : 0 ≤ absBox ω x R :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem integrable_oriented_absBox_rpow (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν)
    {r : ℝ} (hr : 1 ≤ r) (x : Site d) (R : ℕ) :
    Integrable (fun ω : Data d => absBox ω x R ^ r) (orientedLaw d ν) := by
  classical
  have hne : (boxFinset x R).Nonempty := ⟨x, by rw [mem_boxFinset_iff]; intro i; simp⟩
  have hdom : Integrable (fun ω : Data d =>
      ((boxFinset x R).card : ℝ) ^ r * ∑ z ∈ boxFinset x R, |(ω.1 z : ℝ)| ^ r)
      (orientedLaw d ν) :=
    Integrable.const_mul (integrable_finsetSum _ fun z _ =>
      integrable_oriented_abs_conf_rpow hd ν hθ hexp (le_trans zero_le_one hr) z) _
  have hmeas : Measurable fun ω : Data d => absBox ω x R ^ r :=
    (measurable_rpow_const (le_trans zero_le_one hr)).comp
      (Finset.measurable_sum _ fun z _ =>
        ((measurable_intCastReal.comp ((measurable_pi_apply z).comp measurable_fst))).abs)
  refine hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (absBox_nonneg ω x R) r)]
  exact rpow_sum_le (boxFinset x R) (fun z => |(ω.1 z : ℝ)|) (fun z _ => abs_nonneg _) hne hr

/-- The directed divisible odometer reads only the scenery of the box of radius
`n`, and the directed Green function is at most one. -/
theorem uOriented_le_absBox (hd : 1 ≤ d) (ω : Data d) (n : ℕ) (x : Site d) :
    uOriented (fun y => (ω.1 y : ℝ)) n x ≤ absBox ω x n := by
  refine (uOriented_le_abs_potential (fun y => (ω.1 y : ℝ)) n x).trans ?_
  rw [orientedPotential_eq_box, absBox]
  refine Finset.sum_le_sum fun z _ => ?_
  calc orientedGreen d n (z - x) * |(ω.1 z : ℝ)|
      ≤ 1 * |(ω.1 z : ℝ)| :=
        mul_le_mul_of_nonneg_right (orientedGreen_le_one hd n (z - x)) (abs_nonneg _)
    _ = |(ω.1 z : ℝ)| := one_mul _

theorem integrable_oriented_uOriented_rpow (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    {r : ℝ} (hr : 1 ≤ r) (n : ℕ) (x : Site d) :
    Integrable (fun ω : Data d => |uOriented (fun y => (ω.1 y : ℝ)) n x| ^ r)
      (orientedLaw d ν) := by
  haveI := hν.prob
  obtain ⟨θ, hθ, hexp⟩ := hν.expMoment
  refine (integrable_oriented_absBox_rpow hd ν hθ hexp hr x n).mono'
    (((measurable_rpow_const (le_trans zero_le_one hr)).comp
      ((measurable_uOriented n x).comp measurable_confReal).abs).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) r),
    abs_of_nonneg (uOriented_nonneg _ n x)]
  exact Real.rpow_le_rpow (uOriented_nonneg _ n x) (uOriented_le_absBox hd ω n x)
    (le_trans zero_le_one hr)

end Parking
end
