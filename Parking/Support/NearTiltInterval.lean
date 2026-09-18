/-
Step 1 and Step 2 of `lem:near-tilt` (`parking.tex:2591-2622`).

The paper takes `\lambda_1` in `thm:subcritical` to be the positive zero
`\lambda_\delta` of `\psi_\delta'`, which is of order `\delta`, and reads off
`a_\delta=-\tfrac13\psi_\delta(\lambda_\delta)\asymp\delta^2`.  What the bound
needs of that choice is one-sided: an interval `[0,\lambda_1]` of length of order
`\delta` on which the tilted mean is nonpositive and the drift is of order
`\delta`.  The first-order expansion of `\E\eta e^{s\eta}` gives both at once with
`\lambda_1=\delta/(2A)`, `A` read off the exponential moment, and then
`a\geq\delta^2/(12AM)`.  The prefactor of `thm:subcritical` is bounded by the same
moment, uniformly in `\delta`, which is the last sentence of Step 2.
-/
import Parking.Support.TailRange
import Parking.Support.TiltContinuity
import Parking.Support.SubcriticalInterval
import Parking.Support.NearTiltMoments

open MeasureTheory

noncomputable section

namespace Parking

variable {ν : Measure ℤ} {θ : ℝ}

/-- **The exponential moment is at least one**, so a bound on it is positive. -/
theorem one_le_integral_absMoment [IsProbabilityMeasure ν] (hθ : 0 ≤ θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) :
    1 ≤ ∫ k, Real.exp (θ * |(k : ℝ)|) ∂ν := by
  have hle : ∀ k : ℤ, (1 : ℝ) ≤ Real.exp (θ * |(k : ℝ)|) := fun k =>
    Real.one_le_exp (mul_nonneg hθ (abs_nonneg _))
  have h := integral_mono (integrable_const (1 : ℝ)) hexp hle
  simpa using h

/-- **The normalization of the tilt is above `1+s\E\eta(0)`.** -/
theorem one_add_smul_mean_le_integral_exp [IsProbabilityMeasure ν]
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * (k : ℝ))) ν)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) {s : ℝ} (hs0 : 0 ≤ s) (hsθ : s ≤ θ) :
    1 + s * ∫ k, (k : ℝ) ∂ν ≤ ∫ k, Real.exp (s * (k : ℝ)) ∂ν := by
  have hexps : Integrable (fun k : ℤ => Real.exp (s * (k : ℝ))) ν :=
    Parking.integrable_exp_tilt hexp hs0 hsθ
  have hk : Integrable (fun k : ℤ => (k : ℝ)) ν := Parking.integrable_cast hint
  have hsum : Integrable (fun k : ℤ => 1 + s * (k : ℝ)) ν :=
    (integrable_const (1 : ℝ)).add (hk.const_mul s)
  have hle : ∀ k : ℤ, 1 + s * (k : ℝ) ≤ Real.exp (s * (k : ℝ)) := by
    intro k
    have h := Real.add_one_le_exp (s * (k : ℝ))
    linarith
  have h2 := integral_mono hsum hexps hle
  rw [integral_add (integrable_const (1 : ℝ)) (hk.const_mul s)] at h2
  simpa [integral_const, integral_const_mul] using h2

/-- **The tilted mean stays nonpositive, and the drift stays of order `δ`, on an
interval of length of order `δ`.**  This is Step 1 of `lem:near-tilt` in the
form Step 2 uses it. -/
theorem near_drift_bounds [IsProbabilityMeasure ν] (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    {δ M : ℝ} (hmean : ∫ k, (k : ℝ) ∂ν = -δ)
    (hM : ∫ k, Real.exp (θ * |(k : ℝ)|) ∂ν ≤ M)
    {s : ℝ} (hs0 : 0 ≤ s) (hsθ : s ≤ θ / 2)
    (hsmall : s * ((16 / θ ^ 2) * M) ≤ δ / 2) :
    ∫ k, (k : ℝ) ∂(tiltLaw ν s) ≤ 0 ∧ δ / (2 * M) ≤ drift ν s := by
  have hM1 : (1 : ℝ) ≤ M := le_trans (one_le_integral_absMoment hθ.le hexp) hM
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM1
  have hsnn : 0 ≤ s * ((16 / θ ^ 2) * M) := by positivity
  have hδ : 0 ≤ δ := by linarith
  have hsθ' : s ≤ θ := by linarith
  have hexps : Integrable (fun k : ℤ => Real.exp (s * (k : ℝ))) ν :=
    integrable_exp_tilt (integrable_exp_of_absMoment hexp hθ.le) hs0 hsθ'
  have hZpos : 0 < ∫ k, Real.exp (s * (k : ℝ)) ∂ν :=
    integral_exp_pos_of_absMoment hexp hs0 hsθ'
  have hZM : ∫ k, Real.exp (s * (k : ℝ)) ∂ν ≤ M :=
    le_trans (integral_exp_le_absMoment hexp hs0 hsθ') hM
  have hE : ∫ k, Real.exp (s * (k : ℝ)) * (k : ℝ) ∂ν ≤ -(δ / 2) := by
    have h := integral_exp_mul_id_le hθ hexp hint hs0 hsθ
    rw [hmean] at h
    have h2 : s * ((16 / θ ^ 2) * ∫ k, Real.exp (θ * |(k : ℝ)|) ∂ν)
        ≤ s * ((16 / θ ^ 2) * M) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM (by positivity)) hs0
    linarith
  have hid : ∫ k, (k : ℝ) ∂(tiltLaw ν s)
      = (∫ k, Real.exp (s * (k : ℝ)) ∂ν)⁻¹ * ∫ k, Real.exp (s * (k : ℝ)) * (k : ℝ) ∂ν :=
    integral_tiltLaw s (fun k : ℤ => (k : ℝ)) hexps
  have hEnp : ∫ k, Real.exp (s * (k : ℝ)) * (k : ℝ) ∂ν ≤ 0 := by linarith
  have hnonpos : ∫ k, (k : ℝ) ∂(tiltLaw ν s) ≤ 0 := by
    rw [hid]
    have := mul_le_mul_of_nonneg_left hEnp (inv_nonneg.2 hZpos.le)
    simpa using this
  refine ⟨hnonpos, ?_⟩
  have hinvle : M⁻¹ ≤ (∫ k, Real.exp (s * (k : ℝ)) ∂ν)⁻¹ := inv_anti₀ hZpos hZM
  have hstep : M⁻¹ * (δ / 2)
      ≤ (∫ k, Real.exp (s * (k : ℝ)) ∂ν)⁻¹ * (-(∫ k, Real.exp (s * (k : ℝ)) * (k : ℝ) ∂ν)) :=
    mul_le_mul hinvle (by linarith) (by linarith) (le_of_lt (inv_pos.2 hZpos))
  have hdrift : drift ν s
      = (∫ k, Real.exp (s * (k : ℝ)) ∂ν)⁻¹ * (-(∫ k, Real.exp (s * (k : ℝ)) * (k : ℝ) ∂ν)) := by
    unfold drift
    rw [hid]
    ring
  rw [hdrift]
  have heq : M⁻¹ * (δ / 2) = δ / (2 * M) := by
    field_simp
  linarith [hstep, heq.ge, heq.le]

/-- **The tilted absolute first moment is bounded** once the normalization is
bounded below. -/
theorem integral_abs_tiltLaw_le [IsProbabilityMeasure ν] (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν)
    {M : ℝ} (hM : ∫ k, Real.exp (θ * |(k : ℝ)|) ∂ν ≤ M)
    {s : ℝ} (hs0 : 0 ≤ s) (hsθ : s ≤ θ / 2)
    {z : ℝ} (hz : 0 < z) (hZ : z ≤ ∫ k, Real.exp (s * (k : ℝ)) ∂ν) :
    ∫ j, |(j : ℝ)| ∂(tiltLaw ν s) ≤ ((2 / θ) * M) / z := by
  have hsθ' : s ≤ θ := by linarith
  have hexps : Integrable (fun k : ℤ => Real.exp (s * (k : ℝ))) ν :=
    integrable_exp_tilt (integrable_exp_of_absMoment hexp hθ.le) hs0 hsθ'
  have hZpos : 0 < ∫ k, Real.exp (s * (k : ℝ)) ∂ν :=
    integral_exp_pos_of_absMoment hexp hs0 hsθ'
  have hid : ∫ j, |(j : ℝ)| ∂(tiltLaw ν s)
      = (∫ k, Real.exp (s * (k : ℝ)) ∂ν)⁻¹ * ∫ k, Real.exp (s * (k : ℝ)) * |(k : ℝ)| ∂ν :=
    integral_tiltLaw s (fun k : ℤ => |(k : ℝ)|) hexps
  have hnum : ∫ k, Real.exp (s * (k : ℝ)) * |(k : ℝ)| ∂ν ≤ (2 / θ) * M := by
    have hcomm : ∫ k, Real.exp (s * (k : ℝ)) * |(k : ℝ)| ∂ν
        = ∫ k, |(k : ℝ)| * Real.exp (s * (k : ℝ)) ∂ν :=
      integral_congr_ae (Filter.Eventually.of_forall fun k => by ring)
    rw [hcomm]
    have h := integral_abs_mul_exp_le hθ hexp hs0 hsθ
    have h2 : (2 / θ) * ∫ k, Real.exp (θ * |(k : ℝ)|) ∂ν ≤ (2 / θ) * M :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    linarith
  have hinvle : (∫ k, Real.exp (s * (k : ℝ)) ∂ν)⁻¹ ≤ z⁻¹ := inv_anti₀ hz hZ
  have hnumnn : 0 ≤ ∫ k, Real.exp (s * (k : ℝ)) * |(k : ℝ)| ∂ν :=
    integral_nonneg fun k => mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  rw [hid, div_eq_inv_mul]
  exact mul_le_mul hinvle hnum hnumnn (le_of_lt (inv_pos.2 hz))

/-- **The first absolute moment is finite** when an exponential moment is. -/
theorem integrable_abs_of_absMoment [IsProbabilityMeasure ν] (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) :
    Integrable (fun k : ℤ => |(k : ℝ)|) ν := by
  refine (hexp.const_mul (1 / θ)).mono' (measurable_int_fun _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => ?_)
  have h1 : 1 + θ * |(k : ℝ)| ≤ Real.exp (θ * |(k : ℝ)|) := by
    have h := Real.add_one_le_exp (θ * |(k : ℝ)|)
    linarith
  rw [Real.norm_eq_abs, abs_abs, one_div, inv_mul_eq_div, le_div_iff₀ hθ]
  nlinarith [h1, abs_nonneg ((k : ℝ))]

/-- The geometric-type sum of `subcriticalConst_le` increases in its ratio. -/
theorem tsum_succ_mul_geom_mono {r r₀ : ℝ} (hr0 : 0 ≤ r) (hrr : r ≤ r₀) (hr₀ : r₀ < 1) :
    ∑' m : ℕ, ((m : ℝ) + 1) * r ^ m ≤ ∑' m : ℕ, ((m : ℝ) + 1) * r₀ ^ m := by
  have hr0' : 0 ≤ r₀ := le_trans hr0 hrr
  have hnr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    linarith
  have hnr₀ : ‖r₀‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0']
    linarith
  have hs : Summable (fun m : ℕ => ((m : ℝ) + 1) * r ^ m) := by
    have h1 : Summable (fun m : ℕ => (m : ℝ) ^ 1 * r ^ m) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 hnr
    have h2 : Summable (fun m : ℕ => r ^ m) := summable_geometric_of_norm_lt_one hnr
    refine (h1.add h2).congr fun m => ?_
    ring
  have hs₀ : Summable (fun m : ℕ => ((m : ℝ) + 1) * r₀ ^ m) := by
    have h1 : Summable (fun m : ℕ => (m : ℝ) ^ 1 * r₀ ^ m) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 hnr₀
    have h2 : Summable (fun m : ℕ => r₀ ^ m) := summable_geometric_of_norm_lt_one hnr₀
    refine (h1.add h2).congr fun m => ?_
    ring
  refine Summable.tsum_le_tsum (fun m => ?_) hs hs₀
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hrr m) (by positivity)

/-- The geometric-type sum of `subcriticalConst_le` is at least one. -/
theorem one_le_tsum_succ_mul_geom {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    1 ≤ ∑' m : ℕ, ((m : ℝ) + 1) * r ^ m := by
  have hnr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    linarith
  have hs : Summable (fun m : ℕ => ((m : ℝ) + 1) * r ^ m) := by
    have h1 : Summable (fun m : ℕ => (m : ℝ) ^ 1 * r ^ m) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 hnr
    have h2 : Summable (fun m : ℕ => r ^ m) := summable_geometric_of_norm_lt_one hnr
    refine (h1.add h2).congr fun m => ?_
    ring
  have h := hs.le_tsum 0 (fun i _ => by positivity)
  simpa using h

/-- A lower bound on the drift over `[0,λ₁]` integrates to one on `a`. -/
theorem mul_le_intervalIntegral_drift [IsProbabilityMeasure ν]
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * (k : ℝ))) ν)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    {lam₁ c₀ : ℝ} (hlam0 : 0 ≤ lam₁) (hlamθ : lam₁ < θ)
    (hlow : ∀ s ∈ Set.Icc (0 : ℝ) lam₁, c₀ ≤ drift ν s) :
    lam₁ * c₀ ≤ ∫ s in (0 : ℝ)..lam₁, drift ν s := by
  have hcont : ContinuousOn (drift ν) (Set.Icc 0 lam₁) := continuousOn_drift hexp hint hlamθ
  have hii : IntervalIntegrable (drift ν) MeasureTheory.volume 0 lam₁ :=
    hcont.intervalIntegrable_of_Icc hlam0
  have h := intervalIntegral.integral_mono_on (f := fun _ : ℝ => c₀) (g := drift ν)
    hlam0 intervalIntegrable_const hii hlow
  rw [intervalIntegral.integral_const] at h
  simpa using h

/-- An upper bound on the tilted absolute first moment over `[0,λ₁]` integrates to
one on the prefactor of `thm:subcritical`. -/
theorem intervalIntegral_tiltAbsMean_le [IsProbabilityMeasure ν]
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * (k : ℝ))) ν)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    {lam₁ c₀ : ℝ} (hlam0 : 0 ≤ lam₁) (hlamθ : lam₁ < θ)
    (hup : ∀ s ∈ Set.Icc (0 : ℝ) lam₁, (∫ j, |(j : ℝ)| ∂(tiltLaw ν s)) ≤ c₀) :
    (∫ s in (0 : ℝ)..lam₁, ∫ j, |(j : ℝ)| ∂(tiltLaw ν s)) ≤ lam₁ * c₀ := by
  have hcont : ContinuousOn (fun s => ∫ k, |(k : ℝ)| ∂(tiltLaw ν s)) (Set.Icc 0 lam₁) :=
    continuousOn_tiltAbsMean hexp hint hlamθ
  have hii : IntervalIntegrable (fun s => ∫ k, |(k : ℝ)| ∂(tiltLaw ν s))
      MeasureTheory.volume 0 lam₁ := hcont.intervalIntegrable_of_Icc hlam0
  have h := intervalIntegral.integral_mono_on
    (f := fun s : ℝ => ∫ k, |(k : ℝ)| ∂(tiltLaw ν s)) (g := fun _ : ℝ => c₀)
    hlam0 hii intervalIntegrable_const hup
  rw [intervalIntegral.integral_const] at h
  simpa using h

/-- The constant of `lem:near-tilt`, read off the exponential moment bound alone. -/
def nearTiltConst (θ M : ℝ) : ℝ :=
  Real.exp (2 * M / 3) * (M * ∑' m : ℕ, ((m : ℝ) + 1) * Real.exp (-(5 * θ / 6)) ^ m)

theorem nearTiltConst_pos {θ M : ℝ} (hθ : 0 < θ) (hM : 0 < M) : 0 < nearTiltConst θ M := by
  have hr : Real.exp (-(5 * θ / 6)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hT : (1 : ℝ) ≤ ∑' m : ℕ, ((m : ℝ) + 1) * Real.exp (-(5 * θ / 6)) ^ m :=
    one_le_tsum_succ_mul_geom (Real.exp_nonneg _) hr
  have h1 : 0 < M * ∑' m : ℕ, ((m : ℝ) + 1) * Real.exp (-(5 * θ / 6)) ^ m := by
    nlinarith [hM, hT]
  exact mul_pos (Real.exp_pos _) h1

/-- **The constant of `thm:subcritical` is bounded uniformly over the family of
`thm:near`.**  This is the last assertion of Step 2 of `lem:near-tilt`. -/
theorem subcriticalConst_le_nearTiltConst [IsProbabilityMeasure ν] (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    {δ M : ℝ} (hmean : ∫ k, (k : ℝ) ∂ν = -δ) (hδ : 0 ≤ δ)
    (hM : ∫ k, Real.exp (θ * |(k : ℝ)|) ∂ν ≤ M)
    {lam₁ : ℝ} (hlam0 : 0 < lam₁) (hlamθ : lam₁ ≤ θ / 2) (hlamδ : lam₁ * δ ≤ 1 / 2) :
    subcriticalConst ν lam₁ ≤ nearTiltConst θ M := by
  have hM1 : (1 : ℝ) ≤ M := le_trans (one_le_integral_absMoment hθ.le hexp) hM
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM1
  have hexp' : Integrable (fun j : ℤ => Real.exp (θ * j)) ν := integrable_exp_of_absMoment hexp hθ.le
  have hlamθ' : lam₁ < θ := by linarith
  have hbase := subcriticalConst_le ν hlam0 hlamθ' hexp'
  have hZ : ∀ s ∈ Set.Icc (0 : ℝ) lam₁, (1 : ℝ) / 2 ≤ ∫ k, Real.exp (s * (k : ℝ)) ∂ν := by
    intro s hs
    have h := one_add_smul_mean_le_integral_exp hexp' hint hs.1 (le_trans hs.2 hlamθ'.le)
    rw [hmean] at h
    have hsδ : s * δ ≤ lam₁ * δ := mul_le_mul_of_nonneg_right hs.2 hδ
    nlinarith [h, hsδ, hlamδ]
  have hAbs : ∀ s ∈ Set.Icc (0 : ℝ) lam₁,
      (∫ j, |(j : ℝ)| ∂(tiltLaw ν s)) ≤ 2 * ((2 / θ) * M) := by
    intro s hs
    have h := integral_abs_tiltLaw_le hθ hexp hM hs.1 (le_trans hs.2 hlamθ)
      (by norm_num : (0 : ℝ) < 1 / 2) (hZ s hs)
    have hd : ((2 / θ) * M) / (1 / 2) = 2 * ((2 / θ) * M) := by ring
    rw [hd] at h
    linarith
  have hI := intervalIntegral_tiltAbsMean_le hexp' hint hlam0.le hlamθ' hAbs
  have hfac1 : Real.exp ((1 / 3) * ∫ s in (0 : ℝ)..lam₁, ∫ j, |(j : ℝ)| ∂(tiltLaw ν s))
      ≤ Real.exp (2 * M / 3) := by
    refine Real.exp_le_exp.2 ?_
    have h2 : lam₁ * (2 * ((2 / θ) * M)) ≤ (θ / 2) * (2 * ((2 / θ) * M)) :=
      mul_le_mul_of_nonneg_right hlamθ (by positivity)
    have h3 : (θ / 2) * (2 * ((2 / θ) * M)) = 2 * M := by
      field_simp
    linarith [hI, h2, h3.le, h3.ge]
  have hmom : ∫ j, Real.exp (θ * j) ∂ν ≤ M :=
    le_trans (integral_exp_le_absMoment hexp hθ.le le_rfl) hM
  have hmomnn : (0 : ℝ) ≤ ∫ j, Real.exp (θ * j) ∂ν :=
    integral_nonneg fun j => (Real.exp_pos _).le
  have hr : Real.exp (-(θ - lam₁ / 3)) ≤ Real.exp (-(5 * θ / 6)) :=
    Real.exp_le_exp.2 (by linarith)
  have hr1 : Real.exp (-(5 * θ / 6)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have htsum := tsum_succ_mul_geom_mono (Real.exp_nonneg (-(θ - lam₁ / 3))) hr hr1
  have hTnn : (0 : ℝ) ≤ ∑' m : ℕ, ((m : ℝ) + 1) * Real.exp (-(θ - lam₁ / 3)) ^ m :=
    tsum_nonneg fun m => by positivity
  have hT₀nn : (0 : ℝ) ≤ ∑' m : ℕ, ((m : ℝ) + 1) * Real.exp (-(5 * θ / 6)) ^ m :=
    tsum_nonneg fun m => by positivity
  have hfac2 : (∫ j, Real.exp (θ * j) ∂ν) * Real.exp (-θ)
        * ∑' m : ℕ, ((m : ℝ) + 1) * Real.exp (-(θ - lam₁ / 3)) ^ m
      ≤ M * ∑' m : ℕ, ((m : ℝ) + 1) * Real.exp (-(5 * θ / 6)) ^ m := by
    have he : Real.exp (-θ) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hen : (0 : ℝ) ≤ Real.exp (-θ) := (Real.exp_pos _).le
    have h1 : (∫ j, Real.exp (θ * j) ∂ν) * Real.exp (-θ) ≤ M :=
      le_trans (by nlinarith [hmom, hmomnn, he, hen]) le_rfl
    have h1nn : (0 : ℝ) ≤ (∫ j, Real.exp (θ * j) ∂ν) * Real.exp (-θ) :=
      mul_nonneg hmomnn hen
    exact mul_le_mul h1 htsum hTnn hMpos.le
  have hfac2nn : (0 : ℝ) ≤ (∫ j, Real.exp (θ * j) ∂ν) * Real.exp (-θ)
      * ∑' m : ℕ, ((m : ℝ) + 1) * Real.exp (-(θ - lam₁ / 3)) ^ m :=
    mul_nonneg (mul_nonneg hmomnn (Real.exp_pos _).le) hTnn
  refine le_trans hbase ?_
  rw [nearTiltConst]
  exact mul_le_mul hfac1 hfac2 hfac2nn (Real.exp_pos _).le

/-- **`lem:near-tilt`.**  Taking `λ₁` of order `δ` in `thm:subcritical` makes the
exponent `a` of order `δ²`, and the exponential moment bounds the prefactor
uniformly in `δ`. -/
theorem exists_near_tilt_bound {d : ℕ} (hd : 1 ≤ d) {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ}
    (hfam : NearFamily δ₀ ν θ M K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ δ₀ ∧
      ∀ δ ∈ Set.Ioc (0 : ℝ) δ₁, ∀ t : ℕ,
        Integrable (fun ω => (LatticeProb.survivorsFrom (toDriver ω) t 0 : ℝ)) (law d (ν δ)) ∧
          S (law d (ν δ)) t ≤ C * rangeExp d (c * δ ^ 2) t := by
  obtain ⟨hδ₀, hθ, hprob, hmeanδ, -, hmom, -⟩ := hfam
  haveI : IsProbabilityMeasure (ν 0) := hprob 0 ⟨le_rfl, hδ₀.le⟩
  have hM1 : (1 : ℝ) ≤ M :=
    le_trans (one_le_integral_absMoment hθ.le (hmom 0 ⟨le_rfl, hδ₀.le⟩).1)
      (hmom 0 ⟨le_rfl, hδ₀.le⟩).2
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM1
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = (16 / θ ^ 2) * M := ⟨_, rfl⟩
  have hApos : 0 < A := by
    rw [hAdef]
    positivity
  refine ⟨1 / (12 * A * M), nearTiltConst θ M, by positivity, nearTiltConst_pos hθ hMpos,
    min δ₀ (min 1 (min A (A * θ))),
    lt_min hδ₀ (lt_min zero_lt_one (lt_min hApos (mul_pos hApos hθ))), min_le_left _ _, ?_⟩
  intro δ hδ t
  have hδ0 : 0 < δ := hδ.1
  have hδ1 : δ ≤ min δ₀ (min 1 (min A (A * θ))) := hδ.2
  have hδδ₀ : δ ≤ δ₀ := le_trans hδ1 (min_le_left _ _)
  have hδ_1 : δ ≤ 1 := le_trans hδ1 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδA : δ ≤ A :=
    le_trans hδ1 (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hδAθ : δ ≤ A * θ :=
    le_trans hδ1 (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  haveI : IsProbabilityMeasure (ν δ) := hprob δ ⟨hδ0.le, hδδ₀⟩
  have hexpδ := (hmom δ ⟨hδ0.le, hδδ₀⟩).1
  have hMδ := (hmom δ ⟨hδ0.le, hδδ₀⟩).2
  have hmeanδ' : ∫ k, (k : ℝ) ∂(ν δ) = -δ := hmeanδ δ ⟨hδ0.le, hδδ₀⟩
  have hint : Integrable (fun k : ℤ => |(k : ℝ)|) (ν δ) := integrable_abs_of_absMoment hθ hexpδ
  have hexp' : Integrable (fun k : ℤ => Real.exp (θ * k)) (ν δ) :=
    integrable_exp_of_absMoment hexpδ hθ.le
  obtain ⟨lam₁, hlamdef⟩ : ∃ l : ℝ, l = δ / (2 * A) := ⟨_, rfl⟩
  have hlam0 : 0 < lam₁ := by
    rw [hlamdef]
    positivity
  have hlamA : lam₁ * A = δ / 2 := by
    rw [hlamdef]
    field_simp
  have hlamθ : lam₁ ≤ θ / 2 := by
    rw [hlamdef, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hδAθ, hApos, hθ]
  have hlamθ' : lam₁ < θ := by linarith
  have hlamδ : lam₁ * δ ≤ 1 / 2 := by
    rw [hlamdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hδA, hδ_1, hδ0, hApos]
  have hdrift : ∀ s ∈ Set.Icc (0 : ℝ) lam₁,
      (∫ k, (k : ℝ) ∂(tiltLaw (ν δ) s) ≤ 0) ∧ δ / (2 * M) ≤ drift (ν δ) s := by
    intro s hs
    have hsmall : s * ((16 / θ ^ 2) * M) ≤ δ / 2 := by
      rw [← hAdef]
      have h := mul_le_mul_of_nonneg_right hs.2 hApos.le
      linarith [hlamA]
    exact near_drift_bounds hθ hexpδ hint hmeanδ' hMδ hs.1 (le_trans hs.2 hlamθ) hsmall
  have hnonpos : ∀ s ∈ Set.Icc (0 : ℝ) lam₁,
      Integrable (fun k : ℤ => (k : ℝ)) (tiltLaw (ν δ) s) ∧
      ∫ k, (k : ℝ) ∂(tiltLaw (ν δ) s) ≤ 0 := fun s hs =>
    ⟨integrable_id_tiltLaw hexp' hint hs.1 (lt_of_le_of_lt hs.2 hlamθ'), (hdrift s hs).1⟩
  refine ⟨integrable_survivorsFrom_law hd hint t, ?_⟩
  have hbound := S_le_subcriticalConst hd hint hexp' hlam0 hlamθ' hnonpos t
  have hI : lam₁ * (δ / (2 * M)) ≤ ∫ s in (0 : ℝ)..lam₁, drift (ν δ) s :=
    mul_le_intervalIntegral_drift hexp' hint hlam0.le hlamθ' (fun s hs => (hdrift s hs).2)
  have heq : lam₁ * (δ / (2 * M)) = 3 * (1 / (12 * A * M) * δ ^ 2) := by
    rw [hlamdef]
    field_simp
    ring
  have ha : 1 / (12 * A * M) * δ ^ 2 ≤ (1 / 3) * ∫ s in (0 : ℝ)..lam₁, drift (ν δ) s := by
    linarith [hI, heq.le, heq.ge]
  have hanonneg : (0 : ℝ) ≤ 1 / (12 * A * M) * δ ^ 2 := by positivity
  have hmono : rangeExp d ((1 / 3) * ∫ s in (0 : ℝ)..lam₁, drift (ν δ) s) t
      ≤ rangeExp d (1 / (12 * A * M) * δ ^ 2) t := rangeExp_anti hd hanonneg ha t
  have hconst := subcriticalConst_le_nearTiltConst hθ hexpδ hint hmeanδ' hδ0.le hMδ hlam0 hlamθ hlamδ
  calc S (law d (ν δ)) t
      ≤ subcriticalConst (ν δ) lam₁
          * rangeExp d ((1 / 3) * ∫ s in (0 : ℝ)..lam₁, drift (ν δ) s) t := hbound
    _ ≤ nearTiltConst θ M * rangeExp d (1 / (12 * A * M) * δ ^ 2) t :=
        mul_le_mul hconst hmono (le_of_lt (rangeExp_pos hd (le_trans hanonneg ha) t))
          (le_of_lt (nearTiltConst_pos hθ hMpos))

end Parking

end
