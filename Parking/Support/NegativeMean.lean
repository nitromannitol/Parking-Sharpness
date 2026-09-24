/- A nonconstant centered integer law has a positive mean negative part. -/
import Parking.Support.MeanPos
import Parking.Support.LinearFirstMoment

noncomputable section
namespace Parking
open MeasureTheory

theorem CriticalLaw.integrable_negativePart {ν : Measure ℤ} (hν : CriticalLaw ν) :
    Integrable (fun k : ℤ => max (-(k : ℝ)) 0) ν := by
  haveI := hν.prob
  have hi : Integrable (fun k : ℤ => (k : ℝ)) ν :=
    (integrable_norm_iff (measurable_of_countable _).aestronglyMeasurable).mp
      (by simpa only [Real.norm_eq_abs] using hν.integrable_abs)
  exact hi.neg.sup (integrable_const 0)

theorem CriticalLaw.negativePart_mean_pos {ν : Measure ℤ} (hν : CriticalLaw ν) :
    0 < ∫ k : ℤ, max (-(k : ℝ)) 0 ∂ν := by
  haveI := hν.prob
  have hi : Integrable (fun k : ℤ => (k : ℝ)) ν :=
    (integrable_norm_iff (measurable_of_countable _).aestronglyMeasurable).mp
      (by simpa only [Real.norm_eq_abs] using hν.integrable_abs)
  have hpos := integral_toNat_pos ν hν.nonconst hν.integrable_abs hν.mean
  simp only [toNat_cast_eq_max] at hpos
  have hp := integral_max_zero_eq_half_abs ν hi hν.mean
  have hn := integral_max_zero_eq_half_abs ν hi.neg (by
    simp only [Pi.neg_apply, integral_neg, hν.mean, neg_zero])
  simp only [Pi.neg_apply, abs_neg, max_comm (0 : ℝ)] at hp hn
  linarith

end Parking
