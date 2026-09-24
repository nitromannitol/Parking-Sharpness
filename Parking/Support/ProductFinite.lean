import Parking.Support.BoundedProduct

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory

/-- Bounded-difference concentration with any finite coordinate set. -/
theorem mgf_bounded_differences_finite {ι X : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : (ι → X) → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀ ω, |f ω| ≤ B) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hosc : ∀ ω i a, |f ω - f (Function.update ω i a)| ≤ c i) (t : ℝ) :
    ∫ ω, Real.exp (t * (f ω - ∫ w, f w ∂(Measure.pi (fun _ : ι => μ))))
      ∂(Measure.pi (fun _ : ι => μ)) ≤ Real.exp ((∑ i, c i ^ 2) * t ^ 2 / 2) := by
  classical
  let e := (Fintype.equivFin ι).symm
  let r : (Fin (Fintype.card ι) → X) → ι → X := fun w i => w (e.symm i)
  have hr : Measurable r := measurable_pi_lambda _ fun i => measurable_pi_apply (e.symm i)
  have he (w : Fin (Fintype.card ι) → X) (i : Fin (Fintype.card ι)) (a : X) :
      r (Function.update w i a) = Function.update (r w) (e i) a := by
    funext j
    by_cases hj : j = e i
    · subst j
      simp [r]
    · have hji : e.symm j ≠ i := fun h => hj (e.symm_apply_eq.mp h)
      simp [r, hj, hji]
  have h := mgf_bounded_differences μ (Fintype.card ι) (f ∘ r) (hf.comp hr) B
    (fun w => hB (r w)) (c ∘ e) (fun i => hc (e i))
    (fun w i a => by simpa only [Function.comp_def, he] using hosc (r w) (e i) a) t
  have hsum : (∑ i : Fin (Fintype.card ι), c (e i) ^ 2) = ∑ j : ι, c j ^ 2 := e.sum_comp (fun j => c j ^ 2)
  have hmp := measurePreserving_piCongrLeft (fun _ : ι => μ) e
  have her : (Equiv.piCongrLeft (fun _ : ι => X) e) = r := by
    funext w i
    obtain ⟨j, rfl⟩ := e.surjective i
    simp [r]
  have hmean : ∫ w, f (r w) ∂(Measure.pi (fun _ : Fin (Fintype.card ι) => μ)) =
      ∫ w, f w ∂(Measure.pi (fun _ : ι => μ)) := by
    simpa only [MeasurableEquiv.coe_piCongrLeft, her] using hmp.integral_comp' f
  have hemean := hmp.integral_comp' (fun w => Real.exp
    (t * (f w - ∫ v, f v ∂(Measure.pi (fun _ : ι => μ)))))
  simp only [MeasurableEquiv.coe_piCongrLeft, her] at hemean
  simpa only [Function.comp_def, hmean, hsum, hemean] using h
end Parking
