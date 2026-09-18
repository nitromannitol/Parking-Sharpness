/-
The absolute `p`-th moment of a centred real Gaussian, scaling as `σ ^ p` times a
universal (finite, unnamed) constant.

This is the tool that repairs the `hbound` route of `TightNoiseHolder.lean`'s module
docstring: the plain `L²` (`p = 2`) second moment of the noise field's increment cannot
satisfy a single-exponent Kolmogorov condition on the whole plane, but a HIGHER absolute
moment of the SAME (exactly Gaussian) increment can, because the Gaussian absolute moment
scales as `σ ^ p` for every `p`, trading moment order for Hölder order. Only the
FINITENESS of the moment is needed here, not its closed form (no Wick/Gamma-function
computation), via the pushforward-scaling identity for `gaussianReal`.
-/
import Mathlib

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Parking

/-- **The absolute `p`-th moment of the standard Gaussian is finite.** -/
theorem lintegral_enorm_rpow_gaussianReal_one_lt_top (p : ℝ≥0) (hp : p ≠ 0) :
    (∫⁻ x : ℝ, ‖x‖ₑ ^ (p : ℝ) ∂(gaussianReal (0 : ℝ) 1)) < ⊤ := by
  have hmem : MemLp id p (gaussianReal (0 : ℝ) 1) := memLp_id_gaussianReal p
  have h2 := hmem.2
  rw [eLpNorm_nnreal_eq_lintegral hp] at h2
  simp only [id] at h2
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hp
  have hp1 : (0 : ℝ) < 1 / (p : ℝ) := div_pos one_pos hppos
  rw [lt_top_iff_ne_top]
  intro hcon
  rw [hcon, ENNReal.top_rpow_of_pos hp1] at h2
  exact absurd h2 (lt_irrefl ⊤)

/-- **The universal constant of the absolute `p`-th moment of the standard Gaussian**,
as a finite real number. -/
def gaussianAbsMoment (p : ℝ≥0) : ℝ :=
  (∫⁻ x : ℝ, ‖x‖ₑ ^ (p : ℝ) ∂(gaussianReal (0 : ℝ) 1)).toReal

theorem ofReal_gaussianAbsMoment (p : ℝ≥0) (hp : p ≠ 0) :
    ENNReal.ofReal (gaussianAbsMoment p)
      = ∫⁻ x : ℝ, ‖x‖ₑ ^ (p : ℝ) ∂(gaussianReal (0 : ℝ) 1) :=
  ENNReal.ofReal_toReal (lintegral_enorm_rpow_gaussianReal_one_lt_top p hp).ne

/-- **The absolute `p`-th moment of a centred Gaussian of variance `σ ^ 2`** is
`gaussianAbsMoment p` times `σ ^ p` (as a lower Lebesgue integral, so no integrability
hypothesis is needed). -/
theorem lintegral_enorm_rpow_gaussianReal (p : ℝ≥0) (hp : p ≠ 0) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∫⁻ x : ℝ, ‖x‖ₑ ^ (p : ℝ) ∂(gaussianReal (0 : ℝ) (σ ^ 2).toNNReal))
      = ENNReal.ofReal (σ ^ (p : ℝ)) * ENNReal.ofReal (gaussianAbsMoment p) := by
  have hmap : (gaussianReal (0 : ℝ) 1).map (σ * ·)
      = gaussianReal (0 : ℝ) (σ ^ 2).toNNReal := by
    rw [gaussianReal_map_const_mul σ, mul_zero]
    congr 1
    apply NNReal.coe_injective
    rw [NNReal.coe_mul, NNReal.coe_one, mul_one]
    simp [Real.coe_toNNReal _ (sq_nonneg σ)]
  rw [← hmap]
  have hmeas : Measurable (fun x : ℝ => σ * x) := measurable_const.mul measurable_id
  rw [lintegral_map (by fun_prop) hmeas]
  have hpt : ∀ x : ℝ, ‖σ * x‖ₑ ^ (p : ℝ) = ENNReal.ofReal (σ ^ (p : ℝ)) * ‖x‖ₑ ^ (p : ℝ) := by
    intro x
    rw [show ‖σ * x‖ₑ = ENNReal.ofReal σ * ‖x‖ₑ from by
      rw [← ofReal_norm, ← ofReal_norm, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_mul, abs_of_nonneg hσ, ENNReal.ofReal_mul hσ]]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by exact_mod_cast p.coe_nonneg),
      ← ENNReal.ofReal_rpow_of_nonneg hσ (by exact_mod_cast p.coe_nonneg)]
  simp_rw [hpt]
  rw [lintegral_const_mul _ (by fun_prop), ofReal_gaussianAbsMoment p hp]

end Parking

end
