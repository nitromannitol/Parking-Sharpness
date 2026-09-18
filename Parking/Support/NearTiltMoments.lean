/-
The one-site moment estimates of `lem:near-tilt` (`parking.tex:2591-2622`).

Step 1 of the paper's proof studies `\psi_\delta(\lambda)=\log\E e^{\lambda\eta_\delta(0)}`
through its second derivative.  What the bound of Step 2 actually needs is one
side of that: the first-order expansion `\E\eta e^{s\eta}\leq\E\eta+sA` with a
constant `A` read off the exponential moment, which both keeps the tilted mean
nonpositive on an interval of length of order `\delta` and keeps the drift there
of order `\delta`.  The quadratic and linear factors are dominated by the
exponential at half the rate, which is what `A` is made of.
-/
import Parking.Support.Near
import Parking.Support.TiltInterval
import Parking.Support.SubcriticalJointBound

open MeasureTheory

noncomputable section

namespace Parking

theorem sq_mul_exp_half_le {θ : ℝ} (hθ : 0 < θ) (x : ℝ) :
    x ^ 2 * Real.exp (θ * |x| / 2) ≤ (16 / θ ^ 2) * Real.exp (θ * |x|) := by
  have hax : (0 : ℝ) ≤ |x| := abs_nonneg x
  have hq : (0 : ℝ) ≤ θ * |x| / 4 := by positivity
  have h1 : 1 + θ * |x| / 4 ≤ Real.exp (θ * |x| / 4) := by
    have h := Real.add_one_le_exp (θ * |x| / 4)
    linarith
  have h2 : Real.exp (θ * |x| / 4) * Real.exp (θ * |x| / 4) = Real.exp (θ * |x| / 2) := by
    rw [← Real.exp_add]
    ring_nf
  have h3 : θ ^ 2 * |x| ^ 2 / 16 ≤ Real.exp (θ * |x| / 2) := by
    rw [← h2]
    nlinarith [h1, hq]
  have h6 : Real.exp (θ * |x| / 2) * Real.exp (θ * |x| / 2) = Real.exp (θ * |x|) := by
    rw [← Real.exp_add]
    ring_nf
  have hθ2 : (0 : ℝ) < θ ^ 2 := by positivity
  rw [sq_abs x] at h3
  have h5 : x ^ 2 ≤ (16 / θ ^ 2) * Real.exp (θ * |x| / 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hθ2]
    nlinarith [h3]
  calc x ^ 2 * Real.exp (θ * |x| / 2)
      ≤ ((16 / θ ^ 2) * Real.exp (θ * |x| / 2)) * Real.exp (θ * |x| / 2) :=
        mul_le_mul_of_nonneg_right h5 (Real.exp_nonneg _)
    _ = (16 / θ ^ 2) * Real.exp (θ * |x|) := by rw [mul_assoc, h6]

theorem abs_mul_exp_half_le {θ : ℝ} (hθ : 0 < θ) (x : ℝ) :
    |x| * Real.exp (θ * |x| / 2) ≤ (2 / θ) * Real.exp (θ * |x|) := by
  have hax : (0 : ℝ) ≤ |x| := abs_nonneg x
  have h1 : 1 + θ * |x| / 2 ≤ Real.exp (θ * |x| / 2) := by
    have h := Real.add_one_le_exp (θ * |x| / 2)
    linarith
  have h2 : Real.exp (θ * |x| / 2) * Real.exp (θ * |x| / 2) = Real.exp (θ * |x|) := by
    rw [← Real.exp_add]
    ring_nf
  have h5 : |x| ≤ (2 / θ) * Real.exp (θ * |x| / 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hθ]
    nlinarith [h1, hax]
  calc |x| * Real.exp (θ * |x| / 2)
      ≤ ((2 / θ) * Real.exp (θ * |x| / 2)) * Real.exp (θ * |x| / 2) :=
        mul_le_mul_of_nonneg_right h5 (Real.exp_nonneg _)
    _ = (2 / θ) * Real.exp (θ * |x|) := by rw [mul_assoc, h2]

theorem mul_exp_sub_one_le {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    x * (Real.exp (s * x) - 1) ≤ s * x ^ 2 * Real.exp (s * |x|) := by
  rcases le_or_gt 0 x with hx | hx
  · have habs : |x| = x := abs_of_nonneg hx
    have h2 : 1 - s * x ≤ Real.exp (-(s * x)) := by
      have h := Real.add_one_le_exp (-(s * x))
      linarith
    have h3 : Real.exp (s * x) * Real.exp (-(s * x)) = 1 := by
      rw [← Real.exp_add]
      simp
    have h4 : Real.exp (s * x) * (1 - s * x) ≤ Real.exp (s * x) * Real.exp (-(s * x)) :=
      mul_le_mul_of_nonneg_left h2 (Real.exp_pos (s * x)).le
    have h1 : Real.exp (s * x) - 1 ≤ s * x * Real.exp (s * x) := by
      rw [h3] at h4
      nlinarith [h4]
    rw [habs]
    nlinarith [h1, hx, Real.exp_pos (s * x)]
  · have habs : |x| = -x := abs_of_neg hx
    have h4 : 1 + s * x ≤ Real.exp (s * x) := by
      have h := Real.add_one_le_exp (s * x)
      linarith
    have h5 : (1 : ℝ) ≤ Real.exp (s * |x|) := by
      rw [habs]
      exact Real.one_le_exp (by nlinarith [hs, hx])
    have h6 : (0 : ℝ) ≤ (-x) * (Real.exp (s * x) - 1 - s * x) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [h6, h5, mul_nonneg hs (sq_nonneg x)]

variable {ν : Measure ℤ} {θ : ℝ}

theorem exp_le_absMoment {s : ℝ} (hs0 : 0 ≤ s) (hsθ : s ≤ θ) (k : ℤ) :
    Real.exp (s * (k : ℝ)) ≤ Real.exp (θ * |(k : ℝ)|) := by
  refine Real.exp_le_exp.2 ?_
  have h1 : (k : ℝ) ≤ |(k : ℝ)| := le_abs_self _
  nlinarith [mul_le_mul_of_nonneg_left h1 hs0,
    mul_le_mul_of_nonneg_right hsθ (abs_nonneg ((k : ℝ)))]

theorem integrable_exp_of_absMoment
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) (hθ : 0 ≤ θ) :
    Integrable (fun k : ℤ => Real.exp (θ * (k : ℝ))) ν := by
  refine hexp.mono' (measurable_int_fun _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_le_absMoment hθ le_rfl k

theorem integral_exp_le_absMoment [IsProbabilityMeasure ν]
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν)
    {s : ℝ} (hs0 : 0 ≤ s) (hsθ : s ≤ θ) :
    ∫ k, Real.exp (s * (k : ℝ)) ∂ν ≤ ∫ k, Real.exp (θ * |(k : ℝ)|) ∂ν := by
  have hint : Integrable (fun k : ℤ => Real.exp (s * (k : ℝ))) ν := by
    refine hexp.mono' (measurable_int_fun _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact exp_le_absMoment hs0 hsθ k
  exact integral_mono hint hexp (fun k => exp_le_absMoment hs0 hsθ k)

theorem integrable_id_mul_exp (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) {s : ℝ} (hs0 : 0 ≤ s)
    (hsθ : s ≤ θ / 2) :
    Integrable (fun k : ℤ => (k : ℝ) * Real.exp (s * (k : ℝ))) ν := by
  refine (hexp.const_mul (2 / θ)).mono' (measurable_int_fun _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => ?_)
  have h1 : (k : ℝ) ≤ |(k : ℝ)| := le_abs_self _
  have hk : s * (k : ℝ) ≤ θ * |(k : ℝ)| / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hs0,
      mul_le_mul_of_nonneg_right hsθ (abs_nonneg ((k : ℝ)))]
  have h2 : Real.exp (s * (k : ℝ)) ≤ Real.exp (θ * |(k : ℝ)| / 2) := Real.exp_le_exp.2 hk
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |(k : ℝ)| * Real.exp (s * (k : ℝ))
      ≤ |(k : ℝ)| * Real.exp (θ * |(k : ℝ)| / 2) :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ ≤ (2 / θ) * Real.exp (θ * |(k : ℝ)|) := abs_mul_exp_half_le hθ ((k : ℝ))

theorem integrable_abs_mul_exp (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) {s : ℝ} (hs0 : 0 ≤ s)
    (hsθ : s ≤ θ / 2) :
    Integrable (fun k : ℤ => |(k : ℝ)| * Real.exp (s * (k : ℝ))) ν := by
  refine (hexp.const_mul (2 / θ)).mono' (measurable_int_fun _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => ?_)
  have h1 : (k : ℝ) ≤ |(k : ℝ)| := le_abs_self _
  have hk : s * (k : ℝ) ≤ θ * |(k : ℝ)| / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hs0,
      mul_le_mul_of_nonneg_right hsθ (abs_nonneg ((k : ℝ)))]
  have h2 : Real.exp (s * (k : ℝ)) ≤ Real.exp (θ * |(k : ℝ)| / 2) := Real.exp_le_exp.2 hk
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_abs]
  calc |(k : ℝ)| * Real.exp (s * (k : ℝ))
      ≤ |(k : ℝ)| * Real.exp (θ * |(k : ℝ)| / 2) :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ ≤ (2 / θ) * Real.exp (θ * |(k : ℝ)|) := abs_mul_exp_half_le hθ ((k : ℝ))

theorem integral_abs_mul_exp_le [IsProbabilityMeasure ν] (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) {s : ℝ} (hs0 : 0 ≤ s)
    (hsθ : s ≤ θ / 2) :
    ∫ k, |(k : ℝ)| * Real.exp (s * (k : ℝ)) ∂ν
      ≤ (2 / θ) * ∫ k, Real.exp (θ * |(k : ℝ)|) ∂ν := by
  have hb : ∀ k : ℤ, |(k : ℝ)| * Real.exp (s * (k : ℝ))
      ≤ (2 / θ) * Real.exp (θ * |(k : ℝ)|) := by
    intro k
    have h1 : (k : ℝ) ≤ |(k : ℝ)| := le_abs_self _
    have hk : s * (k : ℝ) ≤ θ * |(k : ℝ)| / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left h1 hs0,
        mul_le_mul_of_nonneg_right hsθ (abs_nonneg ((k : ℝ)))]
    calc |(k : ℝ)| * Real.exp (s * (k : ℝ))
        ≤ |(k : ℝ)| * Real.exp (θ * |(k : ℝ)| / 2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hk) (abs_nonneg _)
      _ ≤ (2 / θ) * Real.exp (θ * |(k : ℝ)|) := abs_mul_exp_half_le hθ ((k : ℝ))
  have h := integral_mono (integrable_abs_mul_exp hθ hexp hs0 hsθ) (hexp.const_mul (2 / θ)) hb
  rwa [integral_const_mul] at h

theorem integral_exp_mul_id_le [IsProbabilityMeasure ν] (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    {s : ℝ} (hs0 : 0 ≤ s) (hsθ : s ≤ θ / 2) :
    ∫ k, Real.exp (s * (k : ℝ)) * (k : ℝ) ∂ν
      ≤ (∫ k, (k : ℝ) ∂ν) + s * ((16 / θ ^ 2) * ∫ k, Real.exp (θ * |(k : ℝ)|) ∂ν) := by
  have hk : Integrable (fun k : ℤ => (k : ℝ)) ν := integrable_cast hint
  have hke : Integrable (fun k : ℤ => (k : ℝ) * Real.exp (s * (k : ℝ))) ν :=
    integrable_id_mul_exp hθ hexp hs0 hsθ
  have hdiff : Integrable (fun k : ℤ => (k : ℝ) * (Real.exp (s * (k : ℝ)) - 1)) ν := by
    refine (hke.sub hk).congr (Filter.Eventually.of_forall fun k => ?_)
    simp only [Pi.sub_apply]
    ring
  have hb : ∀ k : ℤ, (k : ℝ) * (Real.exp (s * (k : ℝ)) - 1)
      ≤ s * ((16 / θ ^ 2) * Real.exp (θ * |(k : ℝ)|)) := by
    intro k
    have h1 := mul_exp_sub_one_le hs0 ((k : ℝ))
    have h2 : Real.exp (s * |(k : ℝ)|) ≤ Real.exp (θ * |(k : ℝ)| / 2) := by
      refine Real.exp_le_exp.2 ?_
      nlinarith [abs_nonneg ((k : ℝ)), hsθ]
    have h3 : (k : ℝ) ^ 2 * Real.exp (s * |(k : ℝ)|)
        ≤ (k : ℝ) ^ 2 * Real.exp (θ * |(k : ℝ)| / 2) :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    have h4 := sq_mul_exp_half_le hθ ((k : ℝ))
    nlinarith [h1, h3, h4, hs0]
  have hmaj : Integrable (fun k : ℤ => s * ((16 / θ ^ 2) * Real.exp (θ * |(k : ℝ)|))) ν :=
    (hexp.const_mul (16 / θ ^ 2)).const_mul s
  have hstep := integral_mono hdiff hmaj hb
  rw [integral_const_mul, integral_const_mul] at hstep
  have hsplit : ∫ k, Real.exp (s * (k : ℝ)) * (k : ℝ) ∂ν
      = (∫ k, (k : ℝ) ∂ν) + ∫ k, (k : ℝ) * (Real.exp (s * (k : ℝ)) - 1) ∂ν := by
    rw [← integral_add hk hdiff]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    ring
  rw [hsplit]
  linarith [hstep]

theorem integral_exp_pos_of_absMoment [IsProbabilityMeasure ν]
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) {s : ℝ} (hs0 : 0 ≤ s)
    (hsθ : s ≤ θ) : 0 < ∫ k, Real.exp (s * (k : ℝ)) ∂ν := by
  have hint : Integrable (fun k : ℤ => Real.exp (s * (k : ℝ))) ν := by
    refine hexp.mono' (measurable_int_fun _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact exp_le_absMoment hs0 hsθ k
  exact integral_exp_pos hint

end Parking

end
