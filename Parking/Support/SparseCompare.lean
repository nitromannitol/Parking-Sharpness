/-
The sparse-law convex comparison and the uniform dimension-four sandpile bound.
-/
import Parking.Support.Laplace
import Parking.Support.SparseLaw
import Parking.Support.ConvexProduct
import Parking.Support.UFinite
import LatticeProb.Prob.MapPi

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory LatticeProb
open scoped NNReal

/-- Multiplication by a real scalar is Lipschitz. -/
theorem lipschitzWith_mul_real (b : ℝ) : LipschitzWith ‖b‖₊ (fun x : ℝ => b * x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp [Real.dist_eq, ← mul_sub, abs_mul]

/-- The Laplace reference law at a chosen scale. -/
def scaledLaplaceLaw (b : ℝ) : Measure ℝ := laplaceLaw.map (fun x : ℝ => b * x)

instance scaledLaplaceLaw_isProbability (b : ℝ) : IsProbabilityMeasure (scaledLaplaceLaw b) :=
  Measure.isProbabilityMeasure_map (by fun_prop : Measurable (fun x : ℝ => b * x)).aemeasurable

theorem scaledLaplaceLaw_integrable_id (b : ℝ) :
    Integrable (id : ℝ → ℝ) (scaledLaplaceLaw b) := by
  rw [scaledLaplaceLaw]
  exact (integrable_map_measure measurable_id.aestronglyMeasurable
    (by fun_prop : Measurable (fun x : ℝ => b * x)).aemeasurable).mpr
      (laplaceLaw_integrable_id.const_mul b)

/-- The sparse symmetric law is dominated in convex order by a scaled Laplace law. -/
theorem sparse_convex_integral_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (f : ℝ → ℝ) {K : ℝ≥0} (hc : ConvexOn ℝ Set.univ f) (hf : LipschitzWith K f) :
    ∫ x, f x ∂(realLaw (threePointLaw (ε / 2))) ≤
      ∫ x, f x ∂(scaledLaplaceLaw (Real.log (Real.exp 1 / ε))⁻¹) := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  haveI : IsProbabilityMeasure (threePointLaw (ε / 2)) :=
    threePointLaw_isProbability (by positivity) (by linarith)
  have ht : 0 ≤ -Real.log ε := neg_nonneg.mpr (Real.log_nonpos hε.le (by linarith))
  have hb : (Real.log (Real.exp 1 / ε))⁻¹ = (-Real.log ε + 1)⁻¹ := by
    rw [Real.log_div (Real.exp_ne_zero 1) hε.ne', Real.log_exp]
    congr 1
    ring
  have hp : Integrable (fun x : ℝ => f ((-Real.log ε + 1)⁻¹ * x))
      (ProbabilityTheory.expMeasure 1) :=
    integrable_real_lipschitz (hf.comp (lipschitzWith_mul_real _)) integrable_id_expMeasure_one
  have hn : Integrable (fun x : ℝ => f (-((-Real.log ε + 1)⁻¹ * x)))
      (ProbabilityTheory.expMeasure 1) := by
    simpa only [neg_mul, Function.comp_def] using integrable_real_lipschitz
      (hf.comp (lipschitzWith_mul_real (-(-Real.log ε + 1)⁻¹))) integrable_id_expMeasure_one
  have h := convex_exp_tail_le hc hf.continuous ht hp hn
  simp only [neg_neg, Real.exp_log hε] at h
  rw [realLaw_integral _ hf.continuous.measurable,
    integral_threePointLaw (by positivity) (by linarith), hb, scaledLaplaceLaw,
    integral_map (by fun_prop : Measurable (fun x : ℝ => (-Real.log ε + 1)⁻¹ * x)).aemeasurable
      hf.continuous.measurable.aestronglyMeasurable,
    integral_laplaceLaw (f := fun x : ℝ => f ((-Real.log ε + 1)⁻¹ * x))
      (hf.continuous.measurable.comp (measurable_const.mul measurable_id))
      hp (by simpa only [mul_neg] using hn)]
  norm_num only [Int.cast_one, Int.cast_neg, Int.cast_zero]
  simpa only [mul_neg, show 2 * (ε / 2) = ε by ring] using h

/-- Scaling the initial law scales the expected sandpile odometer. -/
theorem meanSandpileReal_scaledLaplace (d : ℕ) {b : ℝ} (hb : 0 ≤ b) (n : ℕ) :
    Parking.External.meanSandpileReal d (scaledLaplaceLaw b) n =
      b * Parking.External.meanSandpileReal d laplaceLaw n := by
  rw [Parking.External.meanSandpileReal, scaledLaplaceLaw,
    ← iidLaw_map_pi d laplaceLaw (by fun_prop : Measurable (fun x : ℝ => b * x)),
    integral_map (by fun_prop : Measurable (fun η : Site d → ℝ => fun x => b * η x)).aemeasurable
      (measurable_u_eval n 0).aestronglyMeasurable]
  simp_rw [u_const_mul _ hb]
  exact integral_const_mul _ _
end Parking

namespace Parking
open MeasureTheory ProbabilityTheory LatticeProb
open scoped NNReal

/-- The logarithmic scale in the sparse comparison is positive. -/
theorem log_exp_div_pos {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < Real.log (Real.exp 1 / ε) := by
  rw [Real.log_div (Real.exp_ne_zero 1) hε.ne', Real.log_exp]
  have := Real.log_nonpos hε.le hε1
  linarith

/-- Convex comparison and homogeneity bound the sparse mean by the fixed reference mean. -/
theorem meanu_sparse_le_laplace (d : ℕ) (hd : 1 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (n : ℕ) :
    meanu (law d (threePointLaw (ε / 2))) n ≤
      (Real.log (Real.exp 1 / ε))⁻¹ * Parking.External.meanSandpileReal d laplaceLaw n := by
  haveI : IsProbabilityMeasure (threePointLaw (ε / 2)) :=
    threePointLaw_isProbability (by positivity) (by linarith)
  have hi : Integrable (id : ℝ → ℝ) (realLaw (threePointLaw (ε / 2))) := by
    rw [realLaw_integrable_iff _ measurable_id]
    exact integrable_threePointLaw _ _
  rw [meanu_eq_meanSandpileReal hd]
  have h := integral_u_iid_le hd hi
    (scaledLaplaceLaw_integrable_id (Real.log (Real.exp 1 / ε))⁻¹)
    (fun f K hc hf => sparse_convex_integral_le hε hε1 f hc hf) n 0
  change Parking.External.meanSandpileReal d (realLaw (threePointLaw (ε / 2))) n ≤
    Parking.External.meanSandpileReal d (scaledLaplaceLaw (Real.log (Real.exp 1 / ε))⁻¹) n at h
  rw [meanSandpileReal_scaledLaplace d (inv_nonneg.mpr (log_exp_div_pos hε (by linarith)).le)] at h
  exact h

/-- A uniform logarithmic upper bound for the four-dimensional sparse sandpile. -/
theorem exists_meanu_sparse_upper (hGrowth : Parking.External.SandpileGrowth) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∀ n : ℕ, 2 ≤ n →
      meanu (law 4 (threePointLaw (ε / 2))) n ≤
        C * Real.log n / Real.log (Real.exp 1 / ε) := by
  have hBP := hGrowth 4 (by norm_num) laplaceLaw inferInstance laplaceLaw_mean
    laplaceLaw_evariance_pos laplaceLaw_evariance_lt_top
    ⟨1 / 2, by norm_num, laplaceLaw_expMoment (by norm_num)⟩
  obtain ⟨c, C, _hc, hC, hb⟩ := hBP.2.1 rfl
  refine ⟨C, hC, fun ε hε hε1 n hn => ?_⟩
  have hL := log_exp_div_pos hε (by linarith : ε ≤ 1)
  calc meanu (law 4 (threePointLaw (ε / 2))) n ≤
      (Real.log (Real.exp 1 / ε))⁻¹ * Parking.External.meanSandpileReal 4 laplaceLaw n :=
        meanu_sparse_le_laplace 4 (by norm_num) hε hε1 n
    _ ≤ (Real.log (Real.exp 1 / ε))⁻¹ * (C * Real.log n) :=
      mul_le_mul_of_nonneg_left (hb n hn).2 (inv_nonneg.mpr hL.le)
    _ = _ := by ring
end Parking
