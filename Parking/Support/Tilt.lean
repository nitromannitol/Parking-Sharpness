/-
The tilted one-site law as a density.

Section 9 of `parking.tex` (`parking.tex:2303-2320`) tilts the law of the count
at a site by `e^{λ k}`.  The tilt is a normalized density, so an integral
against it is an integral against `ν` of the observable times `e^{λ k}`, divided
by the normalization; this is the form in which the derivative of
`parking.tex:2409-2412` is computed.
-/
import Parking.Support.Range
import Parking.Support.Cov

open MeasureTheory

noncomputable section

namespace Parking

/-- **The exponential moment exists below the threshold.** -/
theorem integrable_exp_tilt {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ : ℝ}
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν) {s : ℝ} (hs0 : 0 ≤ s)
    (hsθ : s ≤ θ) : Integrable (fun k : ℤ => Real.exp (s * k)) ν := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add hexp)
    (measurable_int_fun _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => ?_)
  have hpos : (0 : ℝ) < Real.exp (s * (k : ℝ)) := Real.exp_pos _
  have hθ : (0 : ℝ) < Real.exp (θ * (k : ℝ)) := Real.exp_pos _
  rw [Real.norm_eq_abs, abs_of_pos hpos]
  rcases le_or_gt 0 (k : ℝ) with hk | hk
  · have h1 : s * (k : ℝ) ≤ θ * (k : ℝ) := mul_le_mul_of_nonneg_right hsθ hk
    have h2 : Real.exp (s * (k : ℝ)) ≤ Real.exp (θ * (k : ℝ)) := Real.exp_le_exp.mpr h1
    simp only [Pi.add_apply]
    linarith
  · have h1 : s * (k : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs0 (le_of_lt hk)
    have h2 : Real.exp (s * (k : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr h1
    simp only [Pi.add_apply]
    linarith

/-- The normalization of the tilt as a lower integral. -/
theorem lintegral_ofReal_exp {ν : Measure ℤ} (s : ℝ)
    (h : Integrable (fun k : ℤ => Real.exp (s * k)) ν) :
    ∫⁻ k, ENNReal.ofReal (Real.exp (s * k)) ∂ν
      = ENNReal.ofReal (∫ k, Real.exp (s * k) ∂ν) :=
  (ofReal_integral_eq_lintegral_ofReal h
    (Filter.Eventually.of_forall fun _k => Real.exp_nonneg _)).symm

/-- **The tilted law is a probability measure.** -/
theorem tiltLaw_isProbability {ν : Measure ℤ} [IsProbabilityMeasure ν] {s : ℝ}
    (h : Integrable (fun k : ℤ => Real.exp (s * k)) ν) :
    IsProbabilityMeasure (tiltLaw ν s) := by
  constructor
  have hpos : 0 < ∫ k, Real.exp (s * k) ∂ν := integral_exp_pos h
  have hl : ∫⁻ k, ENNReal.ofReal (Real.exp (s * k)) ∂ν
      = ENNReal.ofReal (∫ k, Real.exp (s * k) ∂ν) := lintegral_ofReal_exp s h
  unfold tiltLaw
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    hl, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hpos)) ENNReal.ofReal_ne_top

/-- **An integral against the tilted law is a normalized integral against `ν`.** -/
theorem integral_tiltLaw {ν : Measure ℤ} [IsProbabilityMeasure ν] (s : ℝ) (f : ℤ → ℝ)
    (hexps : Integrable (fun k : ℤ => Real.exp (s * k)) ν) :
    ∫ k, f k ∂(tiltLaw ν s)
      = (∫ k, Real.exp (s * k) ∂ν)⁻¹ * ∫ k, Real.exp (s * k) * f k ∂ν := by
  have hpos : 0 < ∫ k, Real.exp (s * k) ∂ν := integral_exp_pos hexps
  have hmeas : Measurable fun k : ℤ => ENNReal.ofReal (Real.exp (s * k)) :=
    (measurable_int_fun (fun k : ℤ => Real.exp (s * k))).ennreal_ofReal
  unfold tiltLaw
  rw [integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hmeas
      (Filter.Eventually.of_forall fun k => ENNReal.ofReal_lt_top),
    lintegral_ofReal_exp s hexps, ← ENNReal.ofReal_inv_of_pos hpos,
    ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr hpos))]
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)]

end Parking

end
