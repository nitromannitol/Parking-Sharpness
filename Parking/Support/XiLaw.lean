/-
The law of the recentred scenery `ξ_δ = η_δ + δ` of `parking.tex:2729-2732`.

Under `iidLaw d (ν δ)` the field `η` is an independent family of integers with
one-site law `ν δ`, and `xi δ η` adds the constant `δ` in every coordinate, so
`xi δ` pushes that law forward to the i.i.d. real field whose one-site law is
`shiftLaw δ (ν δ)`, the image of `ν δ` under `k ↦ k + δ`.

The hypotheses of `Parking.NearFamily` say exactly that this one-site law has
mean zero and an exponential moment bounded UNIFORMLY in `δ`: the family's mean
is `-δ`, so the shift recentres it, and `|k + δ| ≤ |k| + |δ|` costs only the
factor `e^{θ|δ|} ≤ e^{θδ₀}`.  Those two facts are what the convex comparison of
`Parking/Support/ConvexOrder.lean` consumes, and they are the source of the
uniformity in `δ` of Step 1 of `lem:mean-horizon`.
-/
import Parking.Support.Near
import Parking.Support.ConvexOrder
import LatticeProb.Prob.MapPi

noncomputable section

namespace Parking

open MeasureTheory LatticeProb

variable {d : ℕ}

/-- The one-site law of the recentred scenery: the image of `ν` under `k ↦ k + δ`. -/
def shiftLaw (δ : ℝ) (ν : Measure ℤ) : Measure ℝ := ν.map (fun k : ℤ => (k : ℝ) + δ)

theorem measurable_intShift (δ : ℝ) : Measurable (fun k : ℤ => (k : ℝ) + δ) :=
  measurable_intCastReal.add_const δ

instance isProbabilityMeasure_shiftLaw (δ : ℝ) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (shiftLaw δ ν) :=
  Measure.isProbabilityMeasure_map (measurable_intShift δ).aemeasurable

/-- The shift moves the mean by `δ`. -/
theorem integral_shiftLaw_id (δ : ℝ) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => ((k : ℝ))) ν) :
    ∫ z, z ∂(shiftLaw δ ν) = (∫ k, ((k : ℝ)) ∂ν) + δ := by
  rw [shiftLaw, integral_map (f := fun z : ℝ => z) (measurable_intShift δ).aemeasurable
    (measurable_id : Measurable (fun z : ℝ => z)).aestronglyMeasurable]
  rw [integral_add hint (integrable_const δ), integral_const]
  simp

theorem integrable_id_shiftLaw (δ : ℝ) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => ((k : ℝ))) ν) :
    Integrable (id : ℝ → ℝ) (shiftLaw δ ν) := by
  rw [shiftLaw]
  rw [integrable_map_measure (measurable_id : Measurable (id : ℝ → ℝ)).aestronglyMeasurable
    (measurable_intShift δ).aemeasurable]
  exact (hint.add (integrable_const δ)).congr (Filter.Eventually.of_forall fun _ => rfl)

theorem exp_abs_shift_le (θ δ : ℝ) (hθ : 0 ≤ θ) (k : ℤ) :
    Real.exp (θ * |(k : ℝ) + δ|) ≤ Real.exp (θ * |δ|) * Real.exp (θ * |(k : ℝ)|) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h : |(k : ℝ) + δ| ≤ |(k : ℝ)| + |δ| := abs_add_le _ _
  nlinarith [h, hθ, abs_nonneg ((k : ℝ)), abs_nonneg δ]

theorem aesm_exp_abs (μ : Measure ℝ) (θ : ℝ) :
    AEStronglyMeasurable (fun z : ℝ => Real.exp (θ * |z|)) μ :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).aestronglyMeasurable

theorem integrable_exp_abs_shiftLaw (θ δ : ℝ) (hθ : 0 ≤ θ) (ν : Measure ℤ)
    [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) :
    Integrable (fun z : ℝ => Real.exp (θ * |z|)) (shiftLaw δ ν) := by
  rw [shiftLaw, integrable_map_measure (aesm_exp_abs _ θ) (measurable_intShift δ).aemeasurable]
  refine Integrable.mono' (hint.const_mul (Real.exp (θ * |δ|)))
    (measurable_of_countable _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => ?_)
  rw [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  exact exp_abs_shift_le θ δ hθ k

/-- The exponential moment of the shifted law, uniformly in `δ` through `e^{θ|δ|}`. -/
theorem integral_exp_abs_shiftLaw_le (θ δ M : ℝ) (hθ : 0 ≤ θ) (ν : Measure ℤ)
    [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν)
    (hM : ∫ k, Real.exp (θ * |(k : ℝ)|) ∂ν ≤ M) :
    ∫ z, Real.exp (θ * |z|) ∂(shiftLaw δ ν) ≤ Real.exp (θ * |δ|) * M := by
  have hmap : ∫ z, Real.exp (θ * |z|) ∂(shiftLaw δ ν)
      = ∫ k, Real.exp (θ * |(k : ℝ) + δ|) ∂ν := by
    rw [shiftLaw, integral_map (measurable_intShift δ).aemeasurable (aesm_exp_abs _ θ)]
  rw [hmap]
  calc ∫ k, Real.exp (θ * |(k : ℝ) + δ|) ∂ν
      ≤ ∫ k, Real.exp (θ * |δ|) * Real.exp (θ * |(k : ℝ)|) ∂ν := by
        refine integral_mono ?_ (hint.const_mul _) (fun k => exp_abs_shift_le θ δ hθ k)
        refine Integrable.mono' (hint.const_mul (Real.exp (θ * |δ|)))
          (measurable_of_countable _).aestronglyMeasurable
          (Filter.Eventually.of_forall fun k => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
        exact exp_abs_shift_le θ δ hθ k
    _ = Real.exp (θ * |δ|) * ∫ k, Real.exp (θ * |(k : ℝ)|) ∂ν := integral_const_mul _ _
    _ ≤ Real.exp (θ * |δ|) * M := mul_le_mul_of_nonneg_left hM (Real.exp_nonneg _)

/-- **The law of the recentred scenery.**  The recentred scenery pushes the i.i.d.
integer field forward to the i.i.d. real field with one-site law `shiftLaw δ ν`. -/
theorem law_map_xi (δ : ℝ) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    (LatticeProb.iidLaw d ν).map (fun η : Site d → ℤ => Parking.xi δ η)
      = LatticeProb.iidLaw d (shiftLaw δ ν) :=
  LatticeProb.iidLaw_map_pi d ν (measurable_intShift δ)

end Parking

end
