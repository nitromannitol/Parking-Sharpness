/-
Step 3 of `thm:subcritical` (`parking.tex:2484-2496`): integrating the
differential inequality of Step 2 over `[0, λ₁]`.

"If `φ(0) = 0`, then eq:range-upper is immediate.  Otherwise, integrate the
logarithmic derivative in eq:survival-differential over `[0, λ₁]` and use
`φ(λ₁) ≤ 1`."

The integration is `Support/DiffIneq.lean`, which does not divide by `φ` and so
does not split on `φ(0) = 0`.  What is assembled here is its three hypotheses
for `φ(λ) = E_λ F`:

- the derivative is the sum of the covariances of `F` with the counts at the
  tilted sites (`Support/TiltCov.lean`), a derivative WITHIN `[0, θ]` and hence
  within `[0, λ₁]`, which is what makes the endpoint `λ = 0` available;
- the differential inequality `g φ ≤ 3 φ'` with `g(λ) = δ(λ)|R_t|`, from Step 2
  (`Support/SubcriticalStep2.lean`) and Step 1 (`Support/SubcriticalStep1.lean`);
- the continuity of `g`, which is `Support/TiltContinuity.lean`.

The tilt acts on every site of the box, the origin included, so the correction
`-E_λ|η(0)| - (k-1)` of the paper's Step 1, which measures the cost of holding
the origin at its prescribed configuration, does not appear: `g` is exactly
`δ(λ)|R_t|`.
-/
import Parking.Support.TaggedRankAe
import Parking.Support.SubcriticalStep1
import Parking.Support.TiltContinuity
import Parking.Support.DiffIneq

open MeasureTheory Set LatticeProb

noncomputable section

namespace Parking

variable {d : ℕ}

/-- A fixed background realization.  `restrictLaw` needs one and no statement
depends on which. -/
def baseData (hd : 1 ≤ d) : PData d :=
  ((fun _ => (0 : ℤ)), (fun _ => ((⟨0, hd⟩ : Fin d), true)), (fun _ => (0 : ℝ)))

/-- An almost sure identity for a functional of the tilted sites transfers from
the full product law to the conditioned law, because the latter is the image of
the former under a map that does not change the value of such a functional. -/
theorem ae_eq_zero_restrictLaw {N : Finset (Site d)} {ν : Measure ℤ}
    [IsProbabilityMeasure ν] {ω₀ : PData d} {G : PData d → ℝ} (hG : DependsOn N G)
    (hGm : Measurable G) (h : ∀ᵐ ω ∂(pDataLaw d ν), G ω = 0) :
    ∀ᵐ ω ∂(restrictLaw d N ν ω₀), G ω = 0 := by
  rw [restrictLaw_eq_map]
  refine (ae_map_iff (p := fun ω : PData d => G ω = 0)
    (measurable_keepAt N ω₀).aemeasurable (hGm (measurableSet_singleton (0 : ℝ)))).mpr ?_
  filter_upwards [h] with ω hω
  show G (keepAt N ω₀ ω) = 0
  rw [hG.keepAt ω₀ ω]
  exact hω

/-- **Step 2 of `thm:subcritical`, with the covariance sum in place of the
derivative.**  The derivative of `lem:product` is identified with this sum only
at an interior tilt; the integration of Step 3 runs over the closed interval, so
the endpoint `λ = 0` is needed and the sum is carried instead. -/
theorem mean_mul_mean_le_covSum (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k, (k : ℝ) ∂ν ≤ 0)
    (w : ℕ → Fin d × Bool) {r : ℕ → ℝ} (hr : Function.Injective r) (t : ℕ)
    {N : Finset (Site d)} (hN : subcriticalBox d t ⊆ N) (ω₀ : PData d) :
    (∫ ω, survivalObs w r t ω ∂(restrictLaw d N ν ω₀))
        * ∫ ω, holeObs w t ω ∂(restrictLaw d N ν ω₀)
      ≤ 3 * ∑ x ∈ N, cov (pDataLaw d ν) (survivalObs w r t)
          (fun ω => ((ω.1 x : ℤ) : ℝ)) := by
  have hrange : rangeFinset (0 : Site d) w t ⊆ N := fun x hx =>
    hN (boxFinset_mono (by omega) (rangeFinset_subset_box w t hx))
  have hbound := abs_cov_restrictLaw_le (ν := ν) (ω₀ := ω₀) hd
    ((dependsOn_survivalObs w r t).mono hN) (relabelInvariant_survivalObs w r t).1
    (relabelInvariant_survivalObs w r t).2
    ((dependsOn_holeObs w t).mono hN) (relabelInvariant_holeObs w t).1
    (relabelInvariant_holeObs w t).2
    (measurable_survivalObs w r t) (measurable_holeObs w t)
    (survivalObs_mem_Icc w r t) (fun x₀ ω => survivalObs_mono hd w r t x₀ ω)
    (fun x₀ ω => holeObs_anti hd w t x₀ ω) (fun x₀ ω => holeObs_add_lip hd w t x₀ ω)
    (fun x₀ ω => holeObs_del_lip hd w t x₀ ω) hint hmean
    (integrable_holeObs hd hint w t hrange ω₀)
  have hFZ : ∀ᵐ ω ∂(restrictLaw d N ν ω₀), survivalObs w r t ω * holeObs w t ω = 0 :=
    ae_eq_zero_restrictLaw
      (((dependsOn_survivalObs w r t).mul (dependsOn_holeObs w t)).mono hN)
      ((measurable_survivalObs w r t).mul (measurable_holeObs w t))
      (ae_survivalObs_mul_holeObs hd ν w hr t)
  have hcov := cov_of_mul_ae_zero (restrictLaw d N ν ω₀) hFZ
  have habs := hbound.2
  rw [hcov, abs_neg] at habs
  exact le_trans (le_abs_self _) habs

/-- The tilted mean of the survival indicator is at most one. -/
theorem integral_survivalObs_le_one (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) (t : ℕ) :
    ∫ ω, survivalObs w r t ω ∂(pDataLaw d ν) ≤ 1 := by
  haveI := noiseLaw_isProbability hd
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI : IsProbabilityMeasure (pDataLaw d ν) := by rw [pDataLaw_eq_prod]; infer_instance
  have hle : ∀ ω : PData d, survivalObs w r t ω ≤ 1 := fun ω => (survivalObs_mem_Icc w r t ω).2
  have hI : Integrable (survivalObs (d := d) w r t) (pDataLaw d ν) := by
    refine (integrable_const (1 : ℝ)).mono' (measurable_survivalObs w r t).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (survivalObs_mem_Icc w r t ω).1]
    exact hle ω
  calc ∫ ω, survivalObs w r t ω ∂(pDataLaw d ν)
      ≤ ∫ _ω : PData d, (1 : ℝ) ∂(pDataLaw d ν) := integral_mono hI (integrable_const 1) hle
    _ = 1 := by simp

/-- **Step 3 of `thm:subcritical`.**  The survival probability of the tagged
particle, averaged over the counts at every site, is at most `e^{-a|R_t|}`. -/
theorem integral_survivalObs_le_exp (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    {θ : ℝ} (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    {lam₁ : ℝ} (hlam₁ : 0 < lam₁) (hlam₁θ : lam₁ < θ)
    (hnonpos : ∀ s ∈ Set.Icc (0 : ℝ) lam₁,
      Integrable (fun k : ℤ => (k : ℝ)) (tiltLaw ν s) ∧
      ∫ k, (k : ℝ) ∂(tiltLaw ν s) ≤ 0)
    (w : ℕ → Fin d × Bool) {r : ℕ → ℝ} (hr : Function.Injective r) (t : ℕ) :
    ∫ ω, survivalObs w r t ω ∂(pDataLaw d ν)
      ≤ Real.exp (-((rangeCard (0 : Site d) w t : ℝ)
          * (∫ s in (0 : ℝ)..lam₁, drift ν s) / 3)) := by
  classical
  have hprob : ∀ s ∈ Set.Icc (0 : ℝ) lam₁, IsProbabilityMeasure (tiltLaw ν s) := fun s hs =>
    tiltLaw_isProbability (integrable_exp_tilt hexp hs.1
      (le_of_lt (lt_of_le_of_lt hs.2 hlam₁θ)))
  have hderiv : ∀ s ∈ Set.Icc (0 : ℝ) lam₁,
      HasDerivWithinAt
        (fun u => ∫ ω, survivalObs w r t ω
          ∂(restrictLaw d (subcriticalBox d t) (tiltLaw ν u) (baseData hd)))
        (∑ x ∈ subcriticalBox d t, cov (pDataLaw d (tiltLaw ν s)) (survivalObs w r t)
          (fun ω => ((ω.1 x : ℤ) : ℝ))) (Set.Icc 0 lam₁) s := by
    intro s hs
    haveI := hprob s hs
    exact (hasDerivWithinAt_integral_restrictLaw hd hint hexp hs.1
      (lt_of_le_of_lt hs.2 hlam₁θ) (hnonpos s hs).1 (subcriticalBox d t) (baseData hd)
      (dependsOn_survivalObs w r t) (measurable_survivalObs w r t)
      (survivalObs_mem_Icc w r t)).mono (Set.Icc_subset_Icc le_rfl (le_of_lt hlam₁θ))
  have hineq : ∀ s ∈ Set.Icc (0 : ℝ) lam₁,
      ((rangeCard (0 : Site d) w t : ℝ) * drift ν s)
        * (∫ ω, survivalObs w r t ω
            ∂(restrictLaw d (subcriticalBox d t) (tiltLaw ν s) (baseData hd)))
      ≤ 3 * ∑ x ∈ subcriticalBox d t, cov (pDataLaw d (tiltLaw ν s)) (survivalObs w r t)
          (fun ω => ((ω.1 x : ℤ) : ℝ)) := by
    intro s hs
    haveI := hprob s hs
    have hmain := mean_mul_mean_le_covSum (ν := tiltLaw ν s) hd (hnonpos s hs).1.abs
      (hnonpos s hs).2 w hr t (subset_refl (subcriticalBox d t)) (baseData hd)
    have hZ : (rangeCard (0 : Site d) w t : ℝ) * drift ν s
        ≤ ∫ ω, holeObs w t ω
            ∂(restrictLaw d (subcriticalBox d t) (tiltLaw ν s) (baseData hd)) := by
      have hrw : (∫ ω, holeObs w t ω
            ∂(restrictLaw d (subcriticalBox d t) (tiltLaw ν s) (baseData hd)))
          = ∫ ω, holeObs w t ω ∂(pDataLaw d (tiltLaw ν s)) :=
        integral_restrictLaw (dependsOn_holeObs w t) (measurable_holeObs w t)
      rw [hrw]
      exact rangeCard_mul_le_integral_holeObs hd (hnonpos s hs).1.abs w t
    have hFnn : 0 ≤ ∫ ω, survivalObs w r t ω
        ∂(restrictLaw d (subcriticalBox d t) (tiltLaw ν s) (baseData hd)) :=
      integral_nonneg fun ω => (survivalObs_mem_Icc w r t ω).1
    nlinarith [hmain, hZ, hFnn]
  have hgc : ContinuousOn (fun s => (rangeCard (0 : Site d) w t : ℝ) * drift ν s)
      (Set.Icc 0 lam₁) := continuousOn_const.mul (continuousOn_drift hexp hint hlam₁θ)
  have hmain := le_mul_exp_intervalIntegral
    (φ := fun u => ∫ ω, survivalObs w r t ω
      ∂(restrictLaw d (subcriticalBox d t) (tiltLaw ν u) (baseData hd)))
    (dφ := fun s => ∑ x ∈ subcriticalBox d t, cov (pDataLaw d (tiltLaw ν s))
      (survivalObs w r t) (fun ω => ((ω.1 x : ℤ) : ℝ)))
    (g := fun s => (rangeCard (0 : Site d) w t : ℝ) * drift ν s)
    (le_of_lt hlam₁) hgc hderiv hineq
  have h0 : (∫ ω, survivalObs w r t ω
      ∂(restrictLaw d (subcriticalBox d t) (tiltLaw ν 0) (baseData hd)))
      = ∫ ω, survivalObs w r t ω ∂(pDataLaw d ν) := by
    rw [tiltLaw_zero]
    exact (integral_restrictLaw (N := subcriticalBox d t) (ν := ν) (ω₀ := baseData hd)
      (dependsOn_survivalObs w r t) (measurable_survivalObs w r t) :
      (∫ ω, survivalObs w r t ω ∂(restrictLaw d (subcriticalBox d t) ν (baseData hd)))
        = ∫ ω, survivalObs w r t ω ∂(pDataLaw d ν))
  have h1 : (∫ ω, survivalObs w r t ω
      ∂(restrictLaw d (subcriticalBox d t) (tiltLaw ν lam₁) (baseData hd))) ≤ 1 := by
    haveI := hprob lam₁ (Set.right_mem_Icc.mpr (le_of_lt hlam₁))
    have hrw : (∫ ω, survivalObs w r t ω
          ∂(restrictLaw d (subcriticalBox d t) (tiltLaw ν lam₁) (baseData hd)))
        = ∫ ω, survivalObs w r t ω ∂(pDataLaw d (tiltLaw ν lam₁)) :=
      integral_restrictLaw (dependsOn_survivalObs w r t) (measurable_survivalObs w r t)
    rw [hrw]
    exact integral_survivalObs_le_one hd w r t
  have hgint : (∫ s in (0 : ℝ)..lam₁, (rangeCard (0 : Site d) w t : ℝ) * drift ν s)
      = (rangeCard (0 : Site d) w t : ℝ) * ∫ s in (0 : ℝ)..lam₁, drift ν s :=
    intervalIntegral.integral_const_mul _ _
  rw [h0, hgint] at hmain
  refine le_trans hmain ?_
  nlinarith [h1, Real.exp_pos (-((rangeCard (0 : Site d) w t : ℝ)
    * (∫ s in (0 : ℝ)..lam₁, drift ν s) / 3))]

end Parking

end
