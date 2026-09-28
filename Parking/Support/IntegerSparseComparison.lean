import LatticeProb.Prob.IntegerConvexMinorant
import LatticeProb.Prob.ConvexProduct
import Parking.Support.UConvex
import Parking.Support.SparseLaw

/-!
# A sparse three-point law is a convex-order minorant

A centered integer law dominates a sufficiently sparse symmetric three-point law in
convex order: `threePoint_convex_integral_le` shows that any convex Lipschitz function
has smaller expectation against `threePointLaw p` than against a centered integer law
`ν` whose upper tail at `1` is at least `p`, using the affine-plus-gap convex minorant
`LatticeProb.ConvexOrder.convex_integer_minorant`.
-/

open LatticeProb.ConvexOrder (convex_integer_gap_nonneg convex_integer_minorant
  integrable_real_lipschitz)

noncomputable section
namespace Parking
open MeasureTheory
open scoped NNReal

/-- A convex Lipschitz function has smaller expectation under the sparse three-point
law at parameter `p` than under any centered integer law `ν` whose upper tail at `1`
is at least `p`, by comparing both to the affine-plus-gap minorant of
`convex_integer_minorant`. -/
theorem threePoint_convex_integral_le (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k : ℤ, (k : ℝ) ∂ν = 0)
    {p : ℝ} (hp : 0 ≤ p) (hp2 : 2 * p ≤ 1) (hpν : p ≤ ν.real {k : ℤ | 1 ≤ k})
    (f : ℝ → ℝ) {K : ℝ≥0} (hc : ConvexOn ℝ Set.univ f) (hf : LipschitzWith K f) :
    (∫ z, f z ∂(realLaw (threePointLaw p))) ≤ ∫ z, f z ∂(realLaw ν) := by
  haveI := threePointLaw_isProbability hp hp2
  have hX : Integrable (fun k : ℤ => (k : ℝ)) ν := by
    exact hint.mono' measurable_intCastReal.aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => by simp only [Real.norm_eq_abs]; rfl)
  have hreal : Integrable (id : ℝ → ℝ) (realLaw ν) :=
    (realLaw_integrable_iff ν measurable_id).mpr hX
  have hfi : Integrable (fun k : ℤ => f (k : ℝ)) ν :=
    (realLaw_integrable_iff ν hf.continuous.measurable).mp (integrable_real_lipschitz hf hreal)
  let gap := f 1 + f (-1) - 2 * f 0
  let b := f 0 - f (-1)
  let S : Set ℤ := {k | 1 ≤ k}
  have hS : MeasurableSet S := Set.to_countable _ |>.measurableSet
  have hI : Integrable (S.indicator (fun _ => gap)) ν := (integrable_const gap).indicator hS
  have hlin : Integrable (fun k : ℤ => f 0 + (k : ℝ) * b) ν :=
    (integrable_const (f 0)).add (hX.mul_const b)
  have hbound := integral_mono (hlin.add hI) hfi (fun k => by
    simpa only [Pi.add_apply, S, Set.indicator_apply, Set.mem_setOf_eq, gap, b] using
      convex_integer_minorant f hc k)
  simp only [Pi.add_apply, integral_add hlin hI,
    integral_add (integrable_const (f 0)) (hX.mul_const b), integral_mul_const,
    hmean, zero_mul, integral_const, probReal_univ, smul_eq_mul, one_mul, add_zero,
    integral_indicator_const _ hS] at hbound
  rw [realLaw_integral _ hf.continuous.measurable, realLaw_integral _ hf.continuous.measurable,
    integral_threePointLaw hp hp2]
  norm_num only [Int.cast_one, Int.cast_neg, Int.cast_zero]
  have hg := mul_le_mul_of_nonneg_right hpν (convex_integer_gap_nonneg f hc)
  change f 0 + ν.real S * gap ≤ ∫ k : ℤ, f (k : ℝ) ∂ν at hbound
  dsimp only [gap, S] at hbound
  nlinarith

end Parking
