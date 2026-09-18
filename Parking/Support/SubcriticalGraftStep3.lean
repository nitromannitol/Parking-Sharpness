/-
Steps 2 and 3 of `thm:subcritical` with the particles at the origin prescribed
(`parking.tex:2464-2496`).

With the origin prescribed, `lem:product` applies to the pair
`(graftSurvivalObs, graftHoleObs)` over the sites of the box OTHER than the
origin, and `FZ = 0` turns the covariance into minus the product of the means.
Step 1 with its correction (`Support/SubcriticalGraftStep1.lean`) then gives the
differential inequality

  `3 φ'(λ) ≥ (δ(λ)|R_t| - E_λ|η(0)| - (k-1)) φ(λ)`,

whose integration over `[0, λ₁]` is `Support/DiffIneq.lean`.  The correction
terms are continuous in the tilt (`Support/TiltContinuity.lean`), which is what
the integration needs of them.
-/
import Parking.Support.GraftRankAe
import Parking.Support.SubcriticalStep3

open MeasureTheory Set

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- **Step 2 of `thm:subcritical` with the origin prescribed.** -/
theorem graft_mean_mul_mean_le_covSum (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k, (k : ℝ) ∂ν ≤ 0)
    (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) {ω₁ : PData d} (hc : 0 ≤ ω₁.1 (0 : Site d)) (t : ℕ)
    {N : Finset (Site d)} (hN : puncturedBox d t ⊆ N) (ω₀ : PData d)
    (hFZ : ∀ᵐ ω ∂(pDataLaw d ν),
      graftSurvivalObs w r ω₁ t ω * graftHoleObs w ω₁ t ω = 0) :
    (∫ ω, graftSurvivalObs w r ω₁ t ω ∂(restrictLaw d N ν ω₀))
        * ∫ ω, graftHoleObs w ω₁ t ω ∂(restrictLaw d N ν ω₀)
      ≤ 3 * ∑ x ∈ N, cov (pDataLaw d ν) (graftSurvivalObs w r ω₁ t)
          (fun ω => ((ω.1 x : ℤ) : ℝ)) := by
  have hbound := abs_cov_restrictLaw_le (ν := ν) (ω₀ := ω₀) hd
    ((dependsOn_graftSurvivalObs w r ω₁ t).mono hN)
    (relabelInvariant_graftSurvivalObs w r ω₁ t).1
    (relabelInvariant_graftSurvivalObs w r ω₁ t).2
    ((dependsOn_graftHoleObs w ω₁ t).mono hN) (relabelInvariant_graftHoleObs w ω₁ t).1
    (relabelInvariant_graftHoleObs w ω₁ t).2
    (measurable_graftSurvivalObs w r ω₁ t) (measurable_graftHoleObs w ω₁ t)
    (graftSurvivalObs_mem_Icc w r ω₁ t) (fun x₀ ω => graftSurvivalObs_mono hd w r ω₁ t x₀ ω)
    (fun x₀ ω => graftHoleObs_anti hd w ω₁ t x₀ ω)
    (fun x₀ ω => graftHoleObs_add_lip hd w ω₁ t x₀ ω)
    (fun x₀ ω => graftHoleObs_del_lip hd w ω₁ t x₀ ω) hint hmean
    ((integrable_restrictLaw_iff ((dependsOn_graftHoleObs w ω₁ t).mono hN)
      (measurable_graftHoleObs w ω₁ t)).mpr (integrable_graftHoleObs hd hint w t hc))
  have hFZ' : ∀ᵐ ω ∂(restrictLaw d N ν ω₀),
      graftSurvivalObs w r ω₁ t ω * graftHoleObs w ω₁ t ω = 0 :=
    ae_eq_zero_restrictLaw
      (((dependsOn_graftSurvivalObs w r ω₁ t).mul (dependsOn_graftHoleObs w ω₁ t)).mono hN)
      ((measurable_graftSurvivalObs w r ω₁ t).mul (measurable_graftHoleObs w ω₁ t))
      hFZ
  have hcov := cov_of_mul_ae_zero (restrictLaw d N ν ω₀) hFZ'
  have habs := hbound.2
  rw [hcov, abs_neg] at habs
  exact le_trans (le_abs_self _) habs

/-- The tilted mean of the survival indicator with the origin prescribed is at
most one. -/
theorem integral_graftSurvivalObs_le_one (hd : 1 ≤ d) {ν : Measure ℤ}
    [IsProbabilityMeasure ν] (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) (ω₁ : PData d) (t : ℕ) :
    ∫ ω, graftSurvivalObs w r ω₁ t ω ∂(pDataLaw d ν) ≤ 1 := by
  haveI := noiseLaw_isProbability hd
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI : IsProbabilityMeasure (pDataLaw d ν) := by rw [pDataLaw_eq_prod]; infer_instance
  have hle : ∀ ω : PData d, graftSurvivalObs w r ω₁ t ω ≤ 1 := fun ω =>
    (graftSurvivalObs_mem_Icc w r ω₁ t ω).2
  have hI : Integrable (graftSurvivalObs (d := d) w r ω₁ t) (pDataLaw d ν) := by
    refine (integrable_const (1 : ℝ)).mono'
      (measurable_graftSurvivalObs w r ω₁ t).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (graftSurvivalObs_mem_Icc w r ω₁ t ω).1]
    exact hle ω
  calc ∫ ω, graftSurvivalObs w r ω₁ t ω ∂(pDataLaw d ν)
      ≤ ∫ _ω : PData d, (1 : ℝ) ∂(pDataLaw d ν) := integral_mono hI (integrable_const 1) hle
    _ = 1 := by simp

/-- **Step 3 of `thm:subcritical`, with the `k` particles at the origin
prescribed**: the survival probability of the tagged particle is at most
`exp{(1/3)∫₀^{λ₁} E_λ|η(0)|} e^{λ₁(k-1)/3 - a|R_t|}`. -/
theorem integral_graftSurvivalObs_le_exp (hd : 1 ≤ d) {ν : Measure ℤ}
    [IsProbabilityMeasure ν] (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    {θ : ℝ} (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    {lam₁ : ℝ} (hlam₁ : 0 < lam₁) (hlam₁θ : lam₁ < θ)
    (hnonpos : ∀ s ∈ Set.Icc (0 : ℝ) lam₁,
      Integrable (fun k : ℤ => (k : ℝ)) (tiltLaw ν s) ∧
      ∫ k, (k : ℝ) ∂(tiltLaw ν s) ≤ 0)
    (w : ℕ → Fin d × Bool) {r : ℕ → ℝ} {ω₁ : PData d}
    (hP : Function.Injective (originRank r ω₁)) (hc : 0 ≤ ω₁.1 (0 : Site d)) (t : ℕ) :
    ∫ ω, graftSurvivalObs w r ω₁ t ω ∂(pDataLaw d ν)
      ≤ Real.exp ((1 / 3) * ∫ s in (0 : ℝ)..lam₁, ∫ j, |(j : ℝ)| ∂(tiltLaw ν s))
        * Real.exp (lam₁ * ((ω₁.1 (0 : Site d)).toNat : ℝ) / 3
          - ((1 / 3) * ∫ s in (0 : ℝ)..lam₁, drift ν s)
            * (rangeCard (0 : Site d) w t : ℝ)) := by
  classical
  have hprob : ∀ s ∈ Set.Icc (0 : ℝ) lam₁, IsProbabilityMeasure (tiltLaw ν s) := fun s hs =>
    tiltLaw_isProbability (integrable_exp_tilt hexp hs.1
      (le_of_lt (lt_of_le_of_lt hs.2 hlam₁θ)))
  have hderiv : ∀ s ∈ Set.Icc (0 : ℝ) lam₁,
      HasDerivWithinAt
        (fun u => ∫ ω, graftSurvivalObs w r ω₁ t ω
          ∂(restrictLaw d (puncturedBox d t) (tiltLaw ν u) (baseData hd)))
        (∑ x ∈ puncturedBox d t, cov (pDataLaw d (tiltLaw ν s))
          (graftSurvivalObs w r ω₁ t) (fun ω => ((ω.1 x : ℤ) : ℝ)))
        (Set.Icc 0 lam₁) s := by
    intro s hs
    haveI := hprob s hs
    exact (hasDerivWithinAt_integral_restrictLaw hd hint hexp hs.1
      (lt_of_le_of_lt hs.2 hlam₁θ) (hnonpos s hs).1 (puncturedBox d t) (baseData hd)
      (dependsOn_graftSurvivalObs w r ω₁ t) (measurable_graftSurvivalObs w r ω₁ t)
      (graftSurvivalObs_mem_Icc w r ω₁ t)).mono
      (Set.Icc_subset_Icc le_rfl (le_of_lt hlam₁θ))
  have hineq : ∀ s ∈ Set.Icc (0 : ℝ) lam₁,
      ((rangeCard (0 : Site d) w t : ℝ) * drift ν s - (∫ j, |(j : ℝ)| ∂(tiltLaw ν s))
          - ((ω₁.1 (0 : Site d)).toNat : ℝ))
        * (∫ ω, graftSurvivalObs w r ω₁ t ω
            ∂(restrictLaw d (puncturedBox d t) (tiltLaw ν s) (baseData hd)))
      ≤ 3 * ∑ x ∈ puncturedBox d t, cov (pDataLaw d (tiltLaw ν s))
          (graftSurvivalObs w r ω₁ t) (fun ω => ((ω.1 x : ℤ) : ℝ)) := by
    intro s hs
    haveI := hprob s hs
    have hmain := graft_mean_mul_mean_le_covSum (ν := tiltLaw ν s) hd (hnonpos s hs).1.abs
      (hnonpos s hs).2 w r hc t (subset_refl (puncturedBox d t)) (baseData hd)
      (ae_graftSurvivalObs_mul_graftHoleObs hd (tiltLaw ν s) w hP t)
    have hZ : (rangeCard (0 : Site d) w t : ℝ) * drift ν s
          - (∫ j, |(j : ℝ)| ∂(tiltLaw ν s)) - ((ω₁.1 (0 : Site d)).toNat : ℝ)
        ≤ ∫ ω, graftHoleObs w ω₁ t ω
            ∂(restrictLaw d (puncturedBox d t) (tiltLaw ν s) (baseData hd)) := by
      have hrw : (∫ ω, graftHoleObs w ω₁ t ω
            ∂(restrictLaw d (puncturedBox d t) (tiltLaw ν s) (baseData hd)))
          = ∫ ω, graftHoleObs w ω₁ t ω ∂(pDataLaw d (tiltLaw ν s)) :=
        integral_restrictLaw (dependsOn_graftHoleObs w ω₁ t) (measurable_graftHoleObs w ω₁ t)
      rw [hrw]
      exact rangeCard_mul_sub_le_integral_graftHoleObs hd (hnonpos s hs).1.abs w t hc
    have hFnn : 0 ≤ ∫ ω, graftSurvivalObs w r ω₁ t ω
        ∂(restrictLaw d (puncturedBox d t) (tiltLaw ν s) (baseData hd)) :=
      integral_nonneg fun ω => (graftSurvivalObs_mem_Icc w r ω₁ t ω).1
    nlinarith [hmain, hZ, hFnn]
  have hcd : ContinuousOn (drift ν) (Set.Icc 0 lam₁) := continuousOn_drift hexp hint hlam₁θ
  have hca : ContinuousOn (fun s => ∫ j, |(j : ℝ)| ∂(tiltLaw ν s)) (Set.Icc 0 lam₁) :=
    continuousOn_tiltAbsMean hexp hint hlam₁θ
  have hgc : ContinuousOn (fun s => (rangeCard (0 : Site d) w t : ℝ) * drift ν s
      - (∫ j, |(j : ℝ)| ∂(tiltLaw ν s)) - ((ω₁.1 (0 : Site d)).toNat : ℝ))
      (Set.Icc 0 lam₁) := ((continuousOn_const.mul hcd).sub hca).sub continuousOn_const
  have hmain := le_mul_exp_intervalIntegral
    (φ := fun u => ∫ ω, graftSurvivalObs w r ω₁ t ω
      ∂(restrictLaw d (puncturedBox d t) (tiltLaw ν u) (baseData hd)))
    (dφ := fun s => ∑ x ∈ puncturedBox d t, cov (pDataLaw d (tiltLaw ν s))
      (graftSurvivalObs w r ω₁ t) (fun ω => ((ω.1 x : ℤ) : ℝ)))
    (g := fun s => (rangeCard (0 : Site d) w t : ℝ) * drift ν s
      - (∫ j, |(j : ℝ)| ∂(tiltLaw ν s)) - ((ω₁.1 (0 : Site d)).toNat : ℝ))
    (le_of_lt hlam₁) hgc hderiv hineq
  have h0 : (∫ ω, graftSurvivalObs w r ω₁ t ω
      ∂(restrictLaw d (puncturedBox d t) (tiltLaw ν 0) (baseData hd)))
      = ∫ ω, graftSurvivalObs w r ω₁ t ω ∂(pDataLaw d ν) := by
    rw [tiltLaw_zero]
    exact (integral_restrictLaw (N := puncturedBox d t) (ν := ν) (ω₀ := baseData hd)
      (dependsOn_graftSurvivalObs w r ω₁ t) (measurable_graftSurvivalObs w r ω₁ t) :
      (∫ ω, graftSurvivalObs w r ω₁ t ω
          ∂(restrictLaw d (puncturedBox d t) ν (baseData hd)))
        = ∫ ω, graftSurvivalObs w r ω₁ t ω ∂(pDataLaw d ν))
  have h1 : (∫ ω, graftSurvivalObs w r ω₁ t ω
      ∂(restrictLaw d (puncturedBox d t) (tiltLaw ν lam₁) (baseData hd))) ≤ 1 := by
    haveI := hprob lam₁ (Set.right_mem_Icc.mpr (le_of_lt hlam₁))
    have hrw : (∫ ω, graftSurvivalObs w r ω₁ t ω
          ∂(restrictLaw d (puncturedBox d t) (tiltLaw ν lam₁) (baseData hd)))
        = ∫ ω, graftSurvivalObs w r ω₁ t ω ∂(pDataLaw d (tiltLaw ν lam₁)) :=
      integral_restrictLaw (dependsOn_graftSurvivalObs w r ω₁ t)
        (measurable_graftSurvivalObs w r ω₁ t)
    rw [hrw]
    exact integral_graftSurvivalObs_le_one hd w r ω₁ t
  have hid : IntervalIntegrable (drift ν) MeasureTheory.volume 0 lam₁ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (le_of_lt hlam₁)]
    exact hcd
  have hia : IntervalIntegrable (fun s => ∫ j, |(j : ℝ)| ∂(tiltLaw ν s))
      MeasureTheory.volume 0 lam₁ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (le_of_lt hlam₁)]
    exact hca
  have hgint : (∫ s in (0 : ℝ)..lam₁, ((rangeCard (0 : Site d) w t : ℝ) * drift ν s
        - (∫ j, |(j : ℝ)| ∂(tiltLaw ν s)) - ((ω₁.1 (0 : Site d)).toNat : ℝ)))
      = (rangeCard (0 : Site d) w t : ℝ) * (∫ s in (0 : ℝ)..lam₁, drift ν s)
        - (∫ s in (0 : ℝ)..lam₁, ∫ j, |(j : ℝ)| ∂(tiltLaw ν s))
        - lam₁ * ((ω₁.1 (0 : Site d)).toNat : ℝ) := by
    rw [intervalIntegral.integral_sub ((hid.const_mul _).sub hia) intervalIntegrable_const,
      intervalIntegral.integral_sub (hid.const_mul _) hia,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp
  rw [h0, hgint] at hmain
  refine le_trans hmain ?_
  have hfact : Real.exp (-(((rangeCard (0 : Site d) w t : ℝ)
        * (∫ s in (0 : ℝ)..lam₁, drift ν s)
        - (∫ s in (0 : ℝ)..lam₁, ∫ j, |(j : ℝ)| ∂(tiltLaw ν s))
        - lam₁ * ((ω₁.1 (0 : Site d)).toNat : ℝ)) / 3))
      = Real.exp ((1 / 3) * ∫ s in (0 : ℝ)..lam₁, ∫ j, |(j : ℝ)| ∂(tiltLaw ν s))
        * Real.exp (lam₁ * ((ω₁.1 (0 : Site d)).toNat : ℝ) / 3
          - ((1 / 3) * ∫ s in (0 : ℝ)..lam₁, drift ν s)
            * (rangeCard (0 : Site d) w t : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfact]
  have hpos : (0 : ℝ) < Real.exp ((1 / 3) * ∫ s in (0 : ℝ)..lam₁,
        ∫ j, |(j : ℝ)| ∂(tiltLaw ν s))
      * Real.exp (lam₁ * ((ω₁.1 (0 : Site d)).toNat : ℝ) / 3
        - ((1 / 3) * ∫ s in (0 : ℝ)..lam₁, drift ν s)
          * (rangeCard (0 : Site d) w t : ℝ)) :=
    mul_pos (Real.exp_pos _) (Real.exp_pos _)
  nlinarith [h1, hpos]

end Parking

end
