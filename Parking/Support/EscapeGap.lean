import Parking.Support.EscapePotential
import LatticeProb.Walk.GreenIdentity
import LatticeProb.Walk.Decomp

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The lazy transition kernel attains its maximum at the origin. -/
theorem lazyKernel_le_origin (hd : 1 ≤ d) (n : ℕ) (x : Site d) :
    Q^[n] (delta0 : Site d → ℝ) x ≤ Q^[n] (delta0 : Site d → ℝ) 0 := by
  rw [iterate_delta0_eq (by omega) n x, iterate_delta0_eq (by omega) n 0]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro c _
  apply Finset.prod_le_prod (fun i _ => P1_nonneg _ _)
  intro i _
  exact P1_le_max _ _

/-- The zero-time term of the lazy Green series gives a uniform gap off the origin. -/
theorem fullGreen_gap (hd : 3 ≤ d) {x : Site d} (hx : x ≠ 0) :
    fullGreen d x + 1 / 2 ≤ escapeConst d := by
  have hsum := (summable_iterate_delta0 hd (0 : Site d)).sub (summable_iterate_delta0 hd x)
  have hnn (n : ℕ) : 0 ≤ Q^[n] (delta0 : Site d → ℝ) 0 - Q^[n] (delta0 : Site d → ℝ) x :=
    sub_nonneg.mpr (lazyKernel_le_origin (by omega) n x)
  have h := hsum.le_tsum 0 (fun n _ => hnn n)
  rw [(summable_iterate_delta0 hd (0 : Site d)).tsum_sub (summable_iterate_delta0 hd x)] at h
  rw [tsum_iterate_delta0_eq hd 0, tsum_iterate_delta0_eq hd x] at h
  simp only [Function.iterate_zero_apply, delta0, if_neg hx, ite_true, sub_zero] at h
  change 1 ≤ 2 * srwGreenInf d 0 - 2 * srwGreenInf d x at h
  rw [← fullGreen_eq_srwGreenInf, ← fullGreen_eq_srwGreenInf] at h
  change 1 ≤ 2 * escapeConst d - 2 * fullGreen d x at h
  linarith

/-- A dimension-only lower bound on the escape probability away from its target. -/
theorem escapePotential_gap (hd : 3 ≤ d) {x y : Site d} (hxy : y ≠ x) :
    1 / (2 * escapeConst d) ≤ escapePotential d x y := by
  have hg : 0 < escapeConst d := zero_lt_one.trans_le (one_le_escapeConst hd)
  have h := fullGreen_gap hd (sub_ne_zero.mpr hxy)
  unfold escapePotential
  apply (mul_le_mul_iff_of_pos_right hg).mp
  rw [sub_mul, one_mul, div_mul_cancel₀ _ hg.ne']
  have he : 1 / (2 * escapeConst d) * escapeConst d = (1 : ℝ) / 2 := by field_simp
  rw [he]
  linarith

/-- Every instruction has a positive average chance of escaping a fixed target. -/
theorem integral_step_escapePotential_gap (hd : 3 ≤ d) (x y : Site d) :
    1 / (2 * escapeConst d) ≤ ∫ a, escapePotential d x (y + stepVec a) ∂(stepLaw d) := by
  by_cases hy : y = x
  · subst y
    have hd1 : 1 ≤ d := by omega
    haveI := stepLaw_isProbability hd1
    have hg : 0 < escapeConst d := zero_lt_one.trans_le (one_le_escapeConst hd)
    have hi : Integrable (fun a : Fin d × Bool => fullGreen d (x + stepVec a - x)) (stepLaw d) :=
      Integrable.of_bound (measurable_from_countable' _).aestronglyMeasurable (escapeConst d)
        (ae_of_all _ fun a => by
          rw [Real.norm_eq_abs, abs_of_nonneg (fullGreen_nonneg d _)]
          exact fullGreen_le_escapeConst hd _)
    simp only [escapePotential]
    rw [integral_sub (integrable_const _) (hi.div_const _), integral_div, integral_const,
      probReal_univ, one_smul, integral_step_green hd, if_pos rfl, sub_self]
    change 1 / (2 * escapeConst d) ≤ 1 - (escapeConst d - 1) / escapeConst d
    apply (mul_le_mul_iff_of_pos_right hg).mp
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hg.ne']
    have he : 1 / (2 * escapeConst d) * escapeConst d = (1 : ℝ) / 2 := by field_simp
    rw [he]
    linarith
  · exact (escapePotential_gap hd hy).trans (integral_step_escapePotential_ge hd x y)
end Parking
