import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
namespace Parking
open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

theorem integrable_ite_one_zero (P : Ω → Prop) [DecidablePred P]
    (hP : MeasurableSet {ω | P ω}) : Integrable (fun ω => if P ω then (1 : ℝ) else 0) μ := by
  apply Integrable.of_bound (Measurable.ite hP measurable_const measurable_const).aestronglyMeasurable 1
  apply ae_of_all
  intro ω
  split_ifs <;> norm_num

omit [IsFiniteMeasure μ] in

theorem integral_ite_one_zero (P : Ω → Prop) [DecidablePred P]
    (hP : MeasurableSet {ω | P ω}) :
    (∫ ω, if P ω then (1 : ℝ) else 0 ∂μ) = (μ {ω | P ω}).toReal := by
  have h := integral_indicator_const (μ := μ) (1 : ℝ) hP
  simpa only [Set.indicator, Set.mem_setOf_eq, smul_eq_mul, mul_one, measureReal_def] using h

end Parking
