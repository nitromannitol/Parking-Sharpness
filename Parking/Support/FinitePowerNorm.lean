import Parking.Support.UpperStep
import LatticeProb.Prob.LpSmooth

/-!
# Finite power norms

Finite power norms and their moment estimates.
-/

open LatticeProb.MomentNorm (rNorm rNorm_nonneg)

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset

/-- The `r`-th power norm `(∑_{i ∈ S} |f i| ^ r) ^ (1 / r)` of `f` over the finite
index set `S`. -/
def finitePowerNorm {ι : Type*} (r : ℝ) (S : Finset ι) (f : ι → ℝ) : ℝ :=
  (∑ i ∈ S, |f i| ^ r) ^ (1 / r)

/-- `finitePowerNorm r S f ≥ 0`. -/
theorem finitePowerNorm_nonneg {ι : Type*} (r : ℝ) (S : Finset ι) (f : ι → ℝ) :
    0 ≤ finitePowerNorm r S f :=
  Real.rpow_nonneg (sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg (f i)) _) _

/-- `finitePowerNorm r S f ^ r = ∑_{i ∈ S} |f i| ^ r` for `r > 0`, undoing the outer
`(1 / r)`-power. -/
theorem finitePowerNorm_rpow {ι : Type*} {r : ℝ} (hr : 0 < r)
    (S : Finset ι) (f : ι → ℝ) :
    finitePowerNorm r S f ^ r = ∑ i ∈ S, |f i| ^ r := by
  rw [finitePowerNorm, ← Real.rpow_mul
    (sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _),
    one_div, inv_mul_cancel₀ hr.ne', Real.rpow_one]

/-- Each term `|f i|` for `i ∈ S` is at most `finitePowerNorm r S f`, obtained from
`finitePowerNorm_rpow` and `single_le_sum` after taking `r`-th roots. -/
theorem abs_le_finitePowerNorm {ι : Type*} {r : ℝ} (hr : 0 < r)
    (S : Finset ι) (f : ι → ℝ) {i : ι} (hi : i ∈ S) :
    |f i| ≤ finitePowerNorm r S f := by
  apply (Real.rpow_le_rpow_iff (abs_nonneg _) (finitePowerNorm_nonneg _ _ _) hr).mp
  rw [finitePowerNorm_rpow hr]
  exact single_le_sum (fun j _ => Real.rpow_nonneg (abs_nonneg (f j)) r) hi

variable {Ω : Type} [MeasurableSpace Ω]

/-- `ω ↦ finitePowerNorm r S (fun i => f i ω)` is measurable whenever each `f i`,
`i ∈ S`, is. -/
theorem measurable_finitePowerNorm {ι : Type*} (r : ℝ) (S : Finset ι)
    (f : ι → Ω → ℝ) (hm : ∀ i ∈ S, Measurable (f i)) :
    Measurable fun ω => finitePowerNorm r S (fun i => f i ω) :=
  (Finset.measurable_sum S (fun i hi => (hm i hi).abs.pow_const r)).pow_const (1 / r)

/-- If each `f i`, `i ∈ S`, has `r`-th moment integrable with `rNorm μ r (f i) ≤ B`,
then `finitePowerNorm r S (f · ω)` has `r`-th moment integrable with
`rNorm μ r ≤ S.card ^ (1 / r) * B`, by summing the `r`-th powers over `S` and taking
`(1 / r)`-th roots. -/
theorem finitePowerNorm_moment {ι : Type*} (μ : Measure Ω) {r : ℝ} (hr : 0 < r)
    (S : Finset ι) (f : ι → Ω → ℝ)
    (hi : ∀ i ∈ S, Integrable (fun ω => |f i ω| ^ r) μ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i ∈ S, rNorm μ r (f i) ≤ B) :
    Integrable (fun ω => |finitePowerNorm r S (fun i => f i ω)| ^ r) μ ∧
      rNorm μ r (fun ω => finitePowerNorm r S (fun i => f i ω)) ≤
        (S.card : ℝ) ^ (1 / r) * B := by
  have he (ω : Ω) : |finitePowerNorm r S (fun i => f i ω)| ^ r = ∑ i ∈ S, |f i ω| ^ r := by
    rw [abs_of_nonneg (finitePowerNorm_nonneg _ _ _), finitePowerNorm_rpow hr]
  have hI : Integrable (fun ω => |finitePowerNorm r S (fun i => f i ω)| ^ r) μ := by
    simp only [he]
    exact integrable_finsetSum S hi
  refine ⟨hI, ?_⟩
  have hraw (i : ι) (h : i ∈ S) : (∫ ω, |f i ω| ^ r ∂μ) ≤ B ^ r := by
    have hh := Real.rpow_le_rpow (rNorm_nonneg μ r _) (hb i h) hr.le
    rw [rNorm, ← Real.rpow_mul (integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) r),
      one_div, inv_mul_cancel₀ hr.ne', Real.rpow_one] at hh
    exact hh
  rw [rNorm]
  simp only [he]
  rw [integral_finsetSum S hi]
  have hsum : (∑ i ∈ S, ∫ ω, |f i ω| ^ r ∂μ) ≤ (S.card : ℝ) * B ^ r := by
    calc _ ≤ ∑ _i ∈ S, B ^ r := sum_le_sum hraw
      _ = _ := by simp
  have hh := Real.rpow_le_rpow
    (sum_nonneg fun i _ => integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) r)
    hsum (by positivity : (0 : ℝ) ≤ 1 / r)
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hB _),
    ← Real.rpow_mul hB, mul_one_div, div_self hr.ne', Real.rpow_one] at hh
  exact hh

/-- `|f + g| ^ r` is integrable whenever `|f| ^ r` and `|g| ^ r` are, for `r ≥ 1`,
reducing `f + g` to `f - (-g)` and applying `LatticeProb.integrable_rpow_sub`. -/
theorem integrable_rpow_add (μ : Measure Ω) {r : ℝ} (hr : 1 ≤ r)
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable (fun ω => |f ω| ^ r) μ) (hgi : Integrable (fun ω => |g ω| ^ r) μ) :
    Integrable (fun ω => |f ω + g ω| ^ r) μ := by
  have hn : Integrable (fun ω => |-g ω| ^ r) μ := by simpa only [abs_neg] using hgi
  have hs := LatticeProb.integrable_rpow_sub μ hr f (fun ω => -g ω)
    (((hf.sub hg.neg).abs.pow_const r).aestronglyMeasurable) hfi hn
  simpa only [sub_neg_eq_add] using hs

end Parking
