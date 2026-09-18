/-
The heat-kernel overlap integral behind the covariance of the continuum
directed field (`parking.tex:3175-3203`).

The covariance of two test-function pairings of the space-time white noise is
the plain integral of the product of the test functions.  This module
computes that integral: the product of two Gaussian densities is, after
completing the square, a Gaussian density times the density of the summed
variance at the displacement, so the spatial integral collapses by the heat
semigroup, and the remaining time integral is the overlap.

- `Parking.gaussianPDFReal_mul`: the pointwise completing-the-square
  identity.
- `Parking.integral_gaussianPDFReal_mul`: the Gaussian semigroup,
  `∫ p_v(x,·) p_w(x',·) = p_{v+w}(x,x')`.
- `Parking.integral_contHeat_mul`: the same for the Brownian transition
  density `contHeat` with `Var = t/4`.
- `Parking.integral_contNoiseTest_mul`: the overlap of two truncated test
  functions is the time integral of `contHeat` of the total elapsed time.
-/
import Parking.Support.ContOrientedNoise

open MeasureTheory ProbabilityTheory

noncomputable section
namespace Parking

/-- A sum of nonnegative reals with a nonzero first summand is nonzero. -/
theorem add_ne_zero_of_ne_zero_left {v w : NNReal} (hv : v ≠ 0) : v + w ≠ 0 := by
  intro h
  have h0 : ((v + w : NNReal) : ℝ) = 0 := by rw [h]; exact NNReal.coe_zero
  rw [NNReal.coe_add] at h0
  have hv0 : (v : ℝ) = 0 := by linarith [v.coe_nonneg, w.coe_nonneg]
  exact hv (NNReal.eq hv0)

/-- **Completing the square**: the product of two Gaussian densities is the
density of the summed variance at the displacement times the density of the
harmonic mean of the variances at the weighted midpoint. -/
theorem gaussianPDFReal_mul (x x' : ℝ) {v w : NNReal} (hv : v ≠ 0) (hw : w ≠ 0)
    (y : ℝ) :
    gaussianPDFReal x v y * gaussianPDFReal x' w y
      = gaussianPDFReal x (v + w) x' *
        gaussianPDFReal (((w : ℝ) * x + (v : ℝ) * x') / ((v : ℝ) + (w : ℝ)))
          (v * w / (v + w)) y := by
  have hvpos : (0 : ℝ) < (v : ℝ) := by
    rcases v.coe_nonneg.lt_or_eq with h | h
    · exact h
    · exact absurd (by exact_mod_cast h.symm : v = 0) hv
  have hwpos : (0 : ℝ) < (w : ℝ) := by
    rcases w.coe_nonneg.lt_or_eq with h | h
    · exact h
    · exact absurd (by exact_mod_cast h.symm : w = 0) hw
  have hvw : (0 : ℝ) < (v : ℝ) + (w : ℝ) := by linarith
  have hvne : (v : ℝ) ≠ 0 := ne_of_gt hvpos
  have hwne : (w : ℝ) ≠ 0 := ne_of_gt hwpos
  have hvwne : ((v : ℝ) + (w : ℝ)) ≠ 0 := ne_of_gt hvw
  simp only [gaussianPDFReal]
  rw [NNReal.coe_add, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_add]
  have e1 : (√(2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-(y - x) ^ 2 / (2 * (v : ℝ))) *
        ((√(2 * Real.pi * (w : ℝ)))⁻¹ * Real.exp (-(y - x') ^ 2 / (2 * (w : ℝ))))
      = ((√(2 * Real.pi * (v : ℝ)))⁻¹ * (√(2 * Real.pi * (w : ℝ)))⁻¹) *
        (Real.exp (-(y - x) ^ 2 / (2 * (v : ℝ))) * Real.exp (-(y - x') ^ 2 / (2 * (w : ℝ)))) :=
    by ring
  have e2 : (√(2 * Real.pi * ((v : ℝ) + (w : ℝ))))⁻¹ *
        Real.exp (-(x' - x) ^ 2 / (2 * ((v : ℝ) + (w : ℝ)))) *
        ((√(2 * Real.pi * ((v : ℝ) * (w : ℝ) / ((v : ℝ) + (w : ℝ)))))⁻¹ *
        Real.exp (-(y - ((w : ℝ) * x + (v : ℝ) * x') / ((v : ℝ) + (w : ℝ))) ^ 2 /
          (2 * ((v : ℝ) * (w : ℝ) / ((v : ℝ) + (w : ℝ))))))
      = ((√(2 * Real.pi * ((v : ℝ) + (w : ℝ))))⁻¹ *
          (√(2 * Real.pi * ((v : ℝ) * (w : ℝ) / ((v : ℝ) + (w : ℝ)))))⁻¹) *
        (Real.exp (-(x' - x) ^ 2 / (2 * ((v : ℝ) + (w : ℝ)))) *
          Real.exp (-(y - ((w : ℝ) * x + (v : ℝ) * x') / ((v : ℝ) + (w : ℝ))) ^ 2 /
            (2 * ((v : ℝ) * (w : ℝ) / ((v : ℝ) + (w : ℝ)))))) := by
    ring
  rw [e1, e2, ← Real.exp_add, ← Real.exp_add]
  have hconst : (√(2 * Real.pi * (v : ℝ)))⁻¹ * (√(2 * Real.pi * (w : ℝ)))⁻¹
      = (√(2 * Real.pi * ((v : ℝ) + (w : ℝ))))⁻¹ *
        (√(2 * Real.pi * ((v : ℝ) * (w : ℝ) / ((v : ℝ) + (w : ℝ)))))⁻¹ := by
    rw [← mul_inv, ← mul_inv]
    congr 1
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi * (v : ℝ)),
      ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi * ((v : ℝ) + (w : ℝ)))]
    congr 1
    field_simp [hvwne]
  have hexp : -(y - x) ^ 2 / (2 * (v : ℝ)) + -(y - x') ^ 2 / (2 * (w : ℝ))
      = -(x' - x) ^ 2 / (2 * ((v : ℝ) + (w : ℝ))) +
        -(y - ((w : ℝ) * x + (v : ℝ) * x') / ((v : ℝ) + (w : ℝ))) ^ 2 /
          (2 * ((v : ℝ) * (w : ℝ) / ((v : ℝ) + (w : ℝ)))) := by
    field_simp [hvne, hwne, hvwne]
    ring
  rw [hconst, hexp]

/-- **The Gaussian semigroup in density form**: the product of two Gaussian
densities integrates to the density of the summed variance at the
displacement. -/
theorem integral_gaussianPDFReal_mul (x x' : ℝ) {v w : NNReal} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∫ y : ℝ, gaussianPDFReal x v y * gaussianPDFReal x' w y
      = gaussianPDFReal x (v + w) x' := by
  have hvwne : (v + w : NNReal) ≠ 0 := add_ne_zero_of_ne_zero_left hv
  have hpt : (fun y : ℝ => gaussianPDFReal x v y * gaussianPDFReal x' w y)
      = fun y => gaussianPDFReal x (v + w) x' *
        gaussianPDFReal (((w : ℝ) * x + (v : ℝ) * x') / ((v : ℝ) + (w : ℝ)))
          (v * w / (v + w)) y :=
    funext fun y => gaussianPDFReal_mul x x' hv hw y
  rw [hpt, integral_const_mul,
    integral_gaussianPDFReal_eq_one _ (div_ne_zero (mul_ne_zero hv hw) hvwne), mul_one]

/-- **The heat semigroup for the directed walk's continuum kernel**: the
product of two transition densities integrates to the density of the summed
time at the displacement. -/
theorem integral_contHeat_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x x' : ℝ) :
    ∫ y : ℝ, contHeat a x y * contHeat b x' y = contHeat (a + b) x x' := by
  have hsum : Real.toNNReal ((a + b) / 4)
      = Real.toNNReal (a / 4) + Real.toNNReal (b / 4) := by
    apply NNReal.eq
    rw [NNReal.coe_add, Real.coe_toNNReal _ (by linarith : (0 : ℝ) ≤ (a + b) / 4),
      Real.coe_toNNReal _ (by linarith : (0 : ℝ) ≤ a / 4),
      Real.coe_toNNReal _ (by linarith : (0 : ℝ) ≤ b / 4)]
    ring
  unfold contHeat
  rw [hsum]
  exact integral_gaussianPDFReal_mul x x' (toNNReal_ne_zero_of_pos ha)
    (toNNReal_ne_zero_of_pos hb)

/-- **The overlap integral of two test functions**: the plain integral of the
product of two truncated heat-kernel test functions is the time integral of
`contHeat` of the total elapsed time over the common window. -/
theorem integral_contNoiseTest_mul (T s s' x x' : ℝ) :
    ∫ p : ℝ × ℝ, contNoiseTest T s x p * contNoiseTest T s' x' p
      = ∫ t : ℝ, Set.indicator (Set.Ioo (max s s') T)
        (fun t => contHeat (2 * t - s - s') x x') t := by
  have hint : Integrable (fun p : ℝ × ℝ => contNoiseTest T s x p * contNoiseTest T s' x' p)
      ((volume : Measure ℝ).prod volume) := by
    have h1 := integrable_contNoiseTest_sq T s x
    have h2 := integrable_contNoiseTest_sq T s' x'
    rw [MeasureTheory.Measure.volume_eq_prod] at h1 h2
    refine Integrable.mono' ((h1.add h2).div_const 2)
      ((measurable_contNoiseTest T s x).mul
        (measurable_contNoiseTest T s' x')).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    show ‖contNoiseTest T s x p * contNoiseTest T s' x' p‖
      ≤ ((contNoiseTest T s x p) ^ 2 + (contNoiseTest T s' x' p) ^ 2) / 2
    rw [Real.norm_eq_abs, abs_mul]
    have h := sq_nonneg (|contNoiseTest T s x p| - |contNoiseTest T s' x' p|)
    have e1 : |contNoiseTest T s x p| ^ 2 = (contNoiseTest T s x p) ^ 2 := sq_abs _
    have e2 : |contNoiseTest T s' x' p| ^ 2 = (contNoiseTest T s' x' p) ^ 2 := sq_abs _
    nlinarith [abs_nonneg (contNoiseTest T s x p), abs_nonneg (contNoiseTest T s' x' p),
      h, e1, e2]
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  by_cases hc : max s s' < t ∧ t < T
  · rw [Set.indicator_of_mem (Set.mem_Ioo.mpr hc)]
    have h1 : s < t := lt_of_le_of_lt (le_max_left _ _) hc.1
    have h2 : s' < t := lt_of_le_of_lt (le_max_right _ _) hc.1
    have hpt : (fun y : ℝ => contNoiseTest T s x (t, y) * contNoiseTest T s' x' (t, y))
        = fun y => contHeat (t - s) x y * contHeat (t - s') x' y := by
      funext y
      simp only [contNoiseTest]
      rw [if_pos ⟨h1, hc.2⟩, if_pos ⟨h2, hc.2⟩]
    show ∫ y : ℝ, contNoiseTest T s x (t, y) * contNoiseTest T s' x' (t, y)
      = contHeat (2 * t - s - s') x x'
    rw [hpt, show 2 * t - s - s' = (t - s) + (t - s') by ring]
    exact integral_contHeat_mul (by linarith) (by linarith) x x'
  · rw [Set.indicator_of_notMem (fun h => hc (Set.mem_Ioo.mp h))]
    have hpt : (fun y : ℝ => contNoiseTest T s x (t, y) * contNoiseTest T s' x' (t, y))
        = fun _ => 0 := by
      funext y
      simp only [contNoiseTest]
      by_cases h1 : s < t ∧ t < T
      · have h2 : ¬ (s' < t ∧ t < T) := fun h2 => hc ⟨max_lt h1.1 h2.1, h1.2⟩
        rw [if_neg h2]
        ring
      · rw [if_neg h1]
        ring
    show ∫ y : ℝ, contNoiseTest T s x (t, y) * contNoiseTest T s' x' (t, y) = 0
    rw [hpt]
    exact integral_zero _ _

end Parking
end
