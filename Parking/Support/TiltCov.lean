/-
Differentiating the tilted mean in the tilting parameter.

This closes Step 3 of `lem:product` (`parking.tex:2409-2412`).  Writing `S` for
the sum of the counts at the tilted sites, the density of `Support/TiltProduct.lean`
turns the tilted mean of a bounded observable `G` into a ratio

  `∫ G d(iidLaw (tiltLaw ν s)) = (∫ e^{s S} G d(iidLaw ν)) / (∫ e^{s S} d(iidLaw ν))`,

both integrals of which are differentiated by `Support/TiltDeriv.lean` within
`Set.Ici 0`.  The quotient rule then gives the derivative as the covariance of
`G` with `S` under the tilted law, and the covariance with a sum is the sum of
the covariances with the counts.  Taking `G` to be the conditional mean of the
observable over the particle randomness returns the paper's statement for the
particle data itself.

The derivative is a derivative WITHIN `Set.Icc 0 θ`, at a point `λ < θ`.  Only a
right exponential moment is assumed, so `tiltLaw ν s` is a probability measure
exactly for `0 ≤ s ≤ θ`, and at `s = 0` there need be no two-sided derivative.
That is enough to identify a two-sided derivative that does exist: the tangent
cone of `Set.Icc 0 θ` at each of its points spans the line, which is
`uniqueDiffOn_Icc`, so a function has at most one derivative within `Set.Icc 0 θ`
there, and a two-sided derivative is one of them.  At the endpoint `0` the
tangent cone is the half-line `[0, ∞)`, not a single direction; spanning, not
two-sidedness, is what the uniqueness needs.
-/
import Parking.Support.TiltProduct
import Parking.Support.TiltDeriv
import Parking.Support.ProductBound

open MeasureTheory Set

noncomputable section

namespace Parking

theorem integrable_sum_coords {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (N : Finset (Site d)) :
    Integrable (fun a : Site d → ℤ => ∑ x ∈ N, ((a x : ℤ) : ℝ))
      (LatticeProb.iidLaw d ν) :=
  integrable_finsetSum N fun x _ => integrable_coord hint x

theorem prod_exp_coords {d : ℕ} (s : ℝ) (N : Finset (Site d)) (a : Site d → ℤ) :
    ∏ y ∈ N, Real.exp (s * ((a y : ℤ) : ℝ))
      = Real.exp (s * ∑ x ∈ N, ((a x : ℤ) : ℝ)) := by
  rw [← Real.exp_sum, Finset.mul_sum]

theorem measurable_sum_coords {d : ℕ} (N : Finset (Site d)) :
    Measurable (fun a : Site d → ℤ => ∑ x ∈ N, ((a x : ℤ) : ℝ)) :=
  Finset.measurable_sum _ fun y _ =>
    (measurable_int_fun (fun k : ℤ => (k : ℝ))).comp (measurable_pi_apply y)

theorem dependsOnCounts_sum_coords {d : ℕ} (N : Finset (Site d)) :
    DependsOnCounts N (fun a : Site d → ℤ => ∑ x ∈ N, ((a x : ℤ) : ℝ)) := by
  intro a a' h
  exact Finset.sum_congr rfl fun x hx => by rw [h x hx]

theorem integral_exp_sum_coords {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν] {s : ℝ}
    (hexps : Integrable (fun k : ℤ => Real.exp (s * k)) ν) (N : Finset (Site d)) :
    Integrable (fun a : Site d → ℤ => Real.exp (s * ∑ x ∈ N, ((a x : ℤ) : ℝ)))
        (LatticeProb.iidLaw d ν)
    ∧ ∫ a, Real.exp (s * ∑ x ∈ N, ((a x : ℤ) : ℝ)) ∂(LatticeProb.iidLaw d ν)
        = (∫ k, Real.exp (s * k) ∂ν) ^ N.card := by
  have h := prod_coords (fun _ : Site d => fun k : ℤ => Real.exp (s * k)) (fun _ => hexps) N
  have heq : ∀ a : Site d → ℤ, ∏ y ∈ N, Real.exp (s * ((a y : ℤ) : ℝ))
      = Real.exp (s * ∑ x ∈ N, ((a x : ℤ) : ℝ)) := prod_exp_coords s N
  refine ⟨h.1.congr (Filter.Eventually.of_forall heq), ?_⟩
  rw [← integral_congr_ae (Filter.Eventually.of_forall heq), h.2, Finset.prod_const]

/-- `|x| e^{λ x}` is dominated by `e^{s₁ x}/(s₁ - λ) + |x|` for `0 ≤ λ < s₁`. -/
theorem abs_mul_exp_le {lam s₁ x : ℝ} (hlam0 : 0 ≤ lam) (h : lam < s₁) :
    |x| * Real.exp (lam * x) ≤ Real.exp (s₁ * x) / (s₁ - lam) + |x| := by
  have hts : (0 : ℝ) < s₁ - lam := by linarith
  rcases le_or_gt 0 x with hx | hx
  · have hE : x * Real.exp (lam * x) ≤ Real.exp (s₁ * x) / (s₁ - lam) := mul_exp_le_exp_div h
    rw [abs_of_nonneg hx]
    linarith
  · have hx' : x ≤ 0 := le_of_lt hx
    have h1 : lam * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam0 hx'
    have h2 : Real.exp (lam * x) ≤ 1 := Real.exp_le_one_iff.mpr h1
    have h3 : (0 : ℝ) ≤ |x| := abs_nonneg x
    have h4 : (0 : ℝ) ≤ Real.exp (s₁ * x) / (s₁ - lam) :=
      div_nonneg (Real.exp_nonneg _) (le_of_lt hts)
    nlinarith [h2, h3, h4]

/-- The sum of the counts against the exponential weight is integrable strictly
below the threshold. -/
theorem integrable_sum_mul_exp {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ : ℝ}
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamθ : lam < θ) (N : Finset (Site d)) {u : (Site d → ℤ) → ℝ} (hum : Measurable u)
    (hub : ∀ a, |u a| ≤ |∑ x ∈ N, ((a x : ℤ) : ℝ)|) :
    Integrable (fun a : Site d → ℤ => u a * Real.exp (lam * ∑ x ∈ N, ((a x : ℤ) : ℝ)))
      (LatticeProb.iidLaw d ν) := by
  set s₁ : ℝ := (lam + θ) / 2 with hs₁def
  have hlams₁ : lam < s₁ := by rw [hs₁def]; linarith
  have hs₁θ : s₁ < θ := by rw [hs₁def]; linarith
  have hs₁0 : 0 ≤ s₁ := by linarith
  have hexps₁ : Integrable (fun k : ℤ => Real.exp (s₁ * k)) ν :=
    integrable_exp_tilt hexp hs₁0 (le_of_lt hs₁θ)
  have hb1 := (integral_exp_sum_coords hexps₁ N).1
  have hb2 := (integrable_sum_coords hint N).abs
  refine Integrable.mono' (hb1.div_const (s₁ - lam) |>.add hb2)
    ((hum.mul (Real.measurable_exp.comp (measurable_const.mul (measurable_sum_coords N))))
      ).aestronglyMeasurable (Filter.Eventually.of_forall fun a => ?_)
  have hkey := abs_mul_exp_le (x := ∑ x ∈ N, ((a x : ℤ) : ℝ)) hlam0 hlams₁
  have hpos : (0 : ℝ) < Real.exp (lam * ∑ x ∈ N, ((a x : ℤ) : ℝ)) := Real.exp_pos _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
  simp only [Pi.add_apply]
  calc |u a| * Real.exp (lam * ∑ x ∈ N, ((a x : ℤ) : ℝ))
      ≤ |∑ x ∈ N, ((a x : ℤ) : ℝ)| * Real.exp (lam * ∑ x ∈ N, ((a x : ℤ) : ℝ)) :=
        mul_le_mul_of_nonneg_right (hub a) (le_of_lt hpos)
    _ ≤ Real.exp (s₁ * ∑ x ∈ N, ((a x : ℤ) : ℝ)) / (s₁ - lam)
          + |∑ x ∈ N, ((a x : ℤ) : ℝ)| := hkey

/-- The covariance with a finite sum is the sum of the covariances. -/
theorem cov_sum_right {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type} (N : Finset ι) (f : Ω → ℝ) (g : ι → Ω → ℝ)
    (hfg : ∀ x ∈ N, Integrable (fun ω => f ω * g x ω) μ)
    (hg : ∀ x ∈ N, Integrable (g x) μ) :
    ∑ x ∈ N, cov μ f (g x) = cov μ f (fun ω => ∑ x ∈ N, g x ω) := by
  unfold cov
  have h1 : ∫ ω, f ω * (∑ x ∈ N, g x ω) ∂μ = ∑ x ∈ N, ∫ ω, f ω * g x ω ∂μ := by
    rw [← integral_finsetSum N hfg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp [Finset.mul_sum])
  have h2 : ∫ ω, (∑ x ∈ N, g x ω) ∂μ = ∑ x ∈ N, ∫ ω, g x ω ∂μ := integral_finsetSum N hg
  rw [h1, h2, Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- The mean of an observable of the particle data is the mean of its
conditional mean given the counts. -/
theorem integral_pDataLaw_meanF {d : ℕ} (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {F : PData d → ℝ} (hFI : Integrable F (pDataLaw d ν)) :
    ∫ ω, F ω ∂(pDataLaw d ν) = ∫ a, meanF F a ∂(LatticeProb.iidLaw d ν) := by
  haveI := noiseLaw_isProbability hd
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  rw [pDataLaw_eq_prod]
  exact integral_prod F (by rwa [pDataLaw_eq_prod] at hFI)

/-- **The derivative of the tilted mean is the covariance with the counts.**
This is the last line of Step 3 of `lem:product` (`parking.tex:2409-2412`):
`∂_λ E_λ F = ∑_i Cov_λ(F, η(x_i))`.  The derivative is taken within `[0, θ]`,
which is where the tilted law is defined, and it is the covariance under the
conditioned law of the frozen statement because that law and the full product
law give the same integrals to observables of the tilted sites. -/
theorem hasDerivWithinAt_integral_restrictLaw {d : ℕ} (hd : 1 ≤ d) {ν : Measure ℤ}
    [IsProbabilityMeasure ν] (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    {θ : ℝ} (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamθ : lam < θ)
    (hmean : Integrable (fun k : ℤ => (k : ℝ)) (tiltLaw ν lam))
    (N : Finset (Site d)) (ω₀ : PData d) {F : PData d → ℝ}
    (hFN : DependsOn N F) (hFm : Measurable F) (hF01 : ∀ ω, F ω ∈ Set.Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun s => ∫ ω, F ω ∂(restrictLaw d N (tiltLaw ν s) ω₀))
      (∑ x ∈ N, cov (pDataLaw d (tiltLaw ν lam)) F (fun ω => ((ω.1 x : ℤ) : ℝ)))
      (Set.Icc 0 θ) lam := by
  classical
  haveI := noiseLaw_isProbability hd
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hGm : Measurable (meanF F) := measurable_meanF hd hFm
  have hGb : ∀ a, |meanF F a| ≤ 1 := fun a => by
    have h := meanF_mem_Icc hd hFm hF01 a
    rw [abs_le]; exact ⟨by linarith [h.1], h.2⟩
  have hGN : DependsOnCounts N (meanF F) := meanF_dependsOnCounts hFN
  have hScm : Measurable (fun a : Site d → ℤ => ∑ x ∈ N, ((a x : ℤ) : ℝ)) :=
    measurable_sum_coords N
  have hScN : DependsOnCounts N (fun a : Site d → ℤ => ∑ x ∈ N, ((a x : ℤ) : ℝ)) :=
    dependsOnCounts_sum_coords N
  have hexpSc : Integrable (fun a : Site d → ℤ => Real.exp (θ * ∑ x ∈ N, ((a x : ℤ) : ℝ)))
      (LatticeProb.iidLaw d ν) := (integral_exp_sum_coords hexp N).1
  have hintSc : Integrable (fun a : Site d → ℤ => |∑ x ∈ N, ((a x : ℤ) : ℝ)|)
      (LatticeProb.iidLaw d ν) := (integrable_sum_coords hint N).abs
  have hD1 := hasDerivWithinAt_integral_exp hScm hexpSc hintSc hGm hGb hlam0 hlamθ
  have hD2 := hasDerivWithinAt_integral_exp hScm hexpSc hintSc
    (f := fun _ : Site d → ℤ => (1:ℝ)) measurable_const (fun _ => by norm_num) hlam0 hlamθ
  have hexpslam : Integrable (fun k : ℤ => Real.exp (lam * k)) ν :=
    integrable_exp_tilt hexp hlam0 (le_of_lt hlamθ)
  have hZpos : (0:ℝ) < ∫ k, Real.exp (lam * k) ∂ν := integral_exp_pos hexpslam
  have hZNpos : (0:ℝ) < (∫ k, Real.exp (lam * k) ∂ν) ^ N.card := pow_pos hZpos _
  have hPsi1 : (∫ a, Real.exp (lam * ∑ x ∈ N, ((a x : ℤ) : ℝ)) * (1:ℝ)
        ∂(LatticeProb.iidLaw d ν)) = (∫ k, Real.exp (lam * k) ∂ν) ^ N.card := by
    simp only [mul_one]
    exact (integral_exp_sum_coords hexpslam N).2
  have hsub : Set.Icc (0:ℝ) θ ⊆ Set.Ici (0:ℝ) := fun x hx => hx.1
  have hne : (∫ a, Real.exp (lam * ∑ x ∈ N, ((a x : ℤ) : ℝ)) * (1:ℝ)
      ∂(LatticeProb.iidLaw d ν)) ≠ 0 := by rw [hPsi1]; exact ne_of_gt hZNpos
  have hquot := (hD1.mono hsub).div (hD2.mono hsub) hne
  have hcongr : ∀ s ∈ Set.Icc (0:ℝ) θ,
      (fun s => ∫ ω, F ω ∂(restrictLaw d N (tiltLaw ν s) ω₀)) s
        = ((fun s => ∫ a, Real.exp (s * ∑ x ∈ N, ((a x : ℤ) : ℝ)) * meanF F a
              ∂(LatticeProb.iidLaw d ν)) /
            (fun s => ∫ a, Real.exp (s * ∑ x ∈ N, ((a x : ℤ) : ℝ)) * (1:ℝ)
              ∂(LatticeProb.iidLaw d ν))) s := by
    intro s hs
    have hexps : Integrable (fun k : ℤ => Real.exp (s * k)) ν :=
      integrable_exp_tilt hexp hs.1 hs.2
    haveI := tiltLaw_isProbability hexps
    haveI : IsProbabilityMeasure (LatticeProb.iidLaw d (tiltLaw ν s)) := by
      unfold LatticeProb.iidLaw; infer_instance
    haveI : IsProbabilityMeasure (pDataLaw d (tiltLaw ν s)) := by
      rw [pDataLaw_eq_prod]; infer_instance
    have hFb : ∀ ω : PData d, ‖F ω‖ ≤ 1 := fun ω => by
      have h := hF01 ω
      rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [h.1], h.2⟩
    have hFI : Integrable F (pDataLaw d (tiltLaw ν s)) :=
      (integrable_const (1:ℝ)).mono' hFm.aestronglyMeasurable
        (Filter.Eventually.of_forall hFb)
    have hGiT : Integrable (meanF F) (LatticeProb.iidLaw d (tiltLaw ν s)) :=
      (integrable_const (1:ℝ)).mono' hGm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hGb a)
    have hGi0 : Integrable (fun a : Site d → ℤ =>
        meanF F a * Real.exp (s * ∑ x ∈ N, ((a x : ℤ) : ℝ))) (LatticeProb.iidLaw d ν) :=
      (integral_exp_sum_coords hexps N).1.bdd_mul hGm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hGb a)
    have hdens := integral_iidLaw_tilt hexps N hGm hGN hGiT hGi0
    have h1 : (∫ a, Real.exp (s * ∑ x ∈ N, ((a x : ℤ) : ℝ)) * (1:ℝ)
        ∂(LatticeProb.iidLaw d ν)) = (∫ k, Real.exp (s * k) ∂ν) ^ N.card := by
      simp only [mul_one]
      exact (integral_exp_sum_coords hexps N).2
    have h2 : (∫ a, Real.exp (s * ∑ x ∈ N, ((a x : ℤ) : ℝ)) * meanF F a
          ∂(LatticeProb.iidLaw d ν))
        = ∫ a, meanF F a * Real.exp (s * ∑ x ∈ N, ((a x : ℤ) : ℝ))
          ∂(LatticeProb.iidLaw d ν) :=
      integral_congr_ae (Filter.Eventually.of_forall fun a => by ring)
    have hZs : (0:ℝ) < (∫ k, Real.exp (s * k) ∂ν) ^ N.card :=
      pow_pos (integral_exp_pos hexps) _
    show ∫ ω, F ω ∂(restrictLaw d N (tiltLaw ν s) ω₀)
      = (∫ a, Real.exp (s * ∑ x ∈ N, ((a x : ℤ) : ℝ)) * meanF F a ∂(LatticeProb.iidLaw d ν))
        / ∫ a, Real.exp (s * ∑ x ∈ N, ((a x : ℤ) : ℝ)) * (1:ℝ) ∂(LatticeProb.iidLaw d ν)
    rw [integral_restrictLaw hFN hFm, integral_pDataLaw_meanF hd hFI, h1, h2, ← hdens]
    field_simp
  have hmain := hquot.congr hcongr (hcongr lam ⟨hlam0, le_of_lt hlamθ⟩)
  haveI := tiltLaw_isProbability hexpslam
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d (tiltLaw ν lam)) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI : IsProbabilityMeasure (pDataLaw d (tiltLaw ν lam)) := by
    rw [pDataLaw_eq_prod]; infer_instance
  have hmabs : Integrable (fun k : ℤ => |(k : ℝ)|) (tiltLaw ν lam) := hmean.abs
  have hGnorm : ∀ a : Site d → ℤ, ‖meanF F a‖ ≤ 1 := fun a => by
    rw [Real.norm_eq_abs]; exact hGb a
  have hGT : Integrable (meanF F) (LatticeProb.iidLaw d (tiltLaw ν lam)) :=
    (integrable_const (1:ℝ)).mono' hGm.aestronglyMeasurable
      (Filter.Eventually.of_forall hGnorm)
  have hScT : Integrable (fun a : Site d → ℤ => ∑ x ∈ N, ((a x : ℤ) : ℝ))
      (LatticeProb.iidLaw d (tiltLaw ν lam)) := integrable_sum_coords hmabs N
  have hGScT : Integrable (fun a : Site d → ℤ => meanF F a * ∑ x ∈ N, ((a x : ℤ) : ℝ))
      (LatticeProb.iidLaw d (tiltLaw ν lam)) :=
    hScT.bdd_mul hGm.aestronglyMeasurable (Filter.Eventually.of_forall hGnorm)
  have hGi0 : Integrable (fun a : Site d → ℤ =>
      meanF F a * Real.exp (lam * ∑ x ∈ N, ((a x : ℤ) : ℝ))) (LatticeProb.iidLaw d ν) :=
    (integral_exp_sum_coords hexpslam N).1.bdd_mul hGm.aestronglyMeasurable
      (Filter.Eventually.of_forall hGnorm)
  have hSci0 : Integrable (fun a : Site d → ℤ =>
      (∑ x ∈ N, ((a x : ℤ) : ℝ)) * Real.exp (lam * ∑ x ∈ N, ((a x : ℤ) : ℝ)))
      (LatticeProb.iidLaw d ν) :=
    integrable_sum_mul_exp hexp hint hlam0 hlamθ N hScm fun a => le_refl _
  have hGScN : DependsOnCounts N (fun a : Site d → ℤ => meanF F a * ∑ x ∈ N, ((a x : ℤ) : ℝ)) :=
    fun a a' h => by
      have h1 : meanF F a = meanF F a' := hGN a a' h
      have h2 : (∑ x ∈ N, ((a x : ℤ) : ℝ)) = ∑ x ∈ N, ((a' x : ℤ) : ℝ) := hScN a a' h
      show meanF F a * _ = meanF F a' * _
      rw [h1, h2]
  have hGSci0 : Integrable (fun a : Site d → ℤ =>
      (meanF F a * ∑ x ∈ N, ((a x : ℤ) : ℝ)) * Real.exp (lam * ∑ x ∈ N, ((a x : ℤ) : ℝ)))
      (LatticeProb.iidLaw d ν) :=
    integrable_sum_mul_exp hexp hint hlam0 hlamθ N (hGm.mul hScm) fun a => by
      rw [abs_mul]
      calc |meanF F a| * |∑ x ∈ N, ((a x : ℤ) : ℝ)|
          ≤ 1 * |∑ x ∈ N, ((a x : ℤ) : ℝ)| :=
            mul_le_mul_of_nonneg_right (hGb a) (abs_nonneg _)
        _ = |∑ x ∈ N, ((a x : ℤ) : ℝ)| := one_mul _
  have dG := integral_iidLaw_tilt hexpslam N hGm hGN hGT hGi0
  have dSc := integral_iidLaw_tilt hexpslam N hScm hScN hScT hSci0
  have dGSc := integral_iidLaw_tilt hexpslam N
    (G := fun a : Site d → ℤ => meanF F a * ∑ x ∈ N, ((a x : ℤ) : ℝ))
    (hGm.mul hScm) hGScN hGScT hGSci0
  have hcovsum : ∑ x ∈ N, cov (LatticeProb.iidLaw d (tiltLaw ν lam)) (meanF F)
        (fun a => ((a x : ℤ) : ℝ))
      = cov (LatticeProb.iidLaw d (tiltLaw ν lam)) (meanF F)
        (fun a => ∑ x ∈ N, ((a x : ℤ) : ℝ)) :=
    cov_sum_right N _ _
      (fun x _ => (integrable_coord hmabs x).bdd_mul hGm.aestronglyMeasurable
        (Filter.Eventually.of_forall hGnorm))
      (fun x _ => integrable_coord hmabs x)
  have hcoord : ∀ x ∈ N, cov (pDataLaw d (tiltLaw ν lam)) F (fun ω => ((ω.1 x : ℤ) : ℝ))
      = cov (LatticeProb.iidLaw d (tiltLaw ν lam)) (meanF F) (fun a => ((a x : ℤ) : ℝ)) :=
    fun x _ => cov_pData_coord hd hFm hF01 hmabs x
  have eB1 : (∫ a, Real.exp (lam * ∑ x ∈ N, ((a x : ℤ) : ℝ)) * meanF F a
        ∂(LatticeProb.iidLaw d ν))
      = (∫ k, Real.exp (lam * k) ∂ν) ^ N.card *
        ∫ a, meanF F a ∂(LatticeProb.iidLaw d (tiltLaw ν lam)) := by
    rw [dG]
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => by ring)
  have eB2 : (∫ a, (∑ x ∈ N, ((a x : ℤ) : ℝ)) *
        Real.exp (lam * ∑ x ∈ N, ((a x : ℤ) : ℝ)) * (1:ℝ) ∂(LatticeProb.iidLaw d ν))
      = (∫ k, Real.exp (lam * k) ∂ν) ^ N.card *
        ∫ a, (∑ x ∈ N, ((a x : ℤ) : ℝ)) ∂(LatticeProb.iidLaw d (tiltLaw ν lam)) := by
    rw [dSc]
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => by ring)
  have eB3 : (∫ a, (∑ x ∈ N, ((a x : ℤ) : ℝ)) *
        Real.exp (lam * ∑ x ∈ N, ((a x : ℤ) : ℝ)) * meanF F a ∂(LatticeProb.iidLaw d ν))
      = (∫ k, Real.exp (lam * k) ∂ν) ^ N.card *
        ∫ a, meanF F a * (∑ x ∈ N, ((a x : ℤ) : ℝ))
          ∂(LatticeProb.iidLaw d (tiltLaw ν lam)) := by
    rw [dGSc]
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => by ring)
  have hval : (∑ x ∈ N, cov (pDataLaw d (tiltLaw ν lam)) F (fun ω => ((ω.1 x : ℤ) : ℝ)))
      = (((∫ a, (∑ x ∈ N, ((a x : ℤ) : ℝ)) *
              Real.exp (lam * ∑ x ∈ N, ((a x : ℤ) : ℝ)) * meanF F a
              ∂(LatticeProb.iidLaw d ν)) *
            ∫ a, Real.exp (lam * ∑ x ∈ N, ((a x : ℤ) : ℝ)) * (1:ℝ)
              ∂(LatticeProb.iidLaw d ν) -
          (∫ a, Real.exp (lam * ∑ x ∈ N, ((a x : ℤ) : ℝ)) * meanF F a
              ∂(LatticeProb.iidLaw d ν)) *
            ∫ a, (∑ x ∈ N, ((a x : ℤ) : ℝ)) *
              Real.exp (lam * ∑ x ∈ N, ((a x : ℤ) : ℝ)) * (1:ℝ)
              ∂(LatticeProb.iidLaw d ν)) /
        (∫ a, Real.exp (lam * ∑ x ∈ N, ((a x : ℤ) : ℝ)) * (1:ℝ)
          ∂(LatticeProb.iidLaw d ν)) ^ 2) := by
    rw [Finset.sum_congr rfl hcoord, hcovsum, eB1, eB2, eB3, hPsi1]
    unfold cov
    field_simp
  rw [hval]
  exact hmain

/-- **`lem:product`.**  The covariance of the two observables under the
conditioned tilted law is at most three times the derivative of the tilted mean
of `F`.  This is `parking.tex:2321-2332` for measurable observables: the product
bound of `Support/ProductBound.lean` bounds the covariance by three times the
sum of the covariances with the counts at the tilted sites, and that sum IS the
derivative, by the identity above and the uniqueness of a derivative within
`Set.Icc 0 θ`. -/
theorem abs_cov_le_deriv {d : ℕ} (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    {θ : ℝ} (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamθ : lam < θ)
    (hmeanint : Integrable (fun k : ℤ => (k : ℝ)) (tiltLaw ν lam))
    (hmeanle : ∫ k, (k : ℝ) ∂(tiltLaw ν lam) ≤ 0)
    {N : Finset (Site d)} {ω₀ : PData d} {F Z : PData d → ℝ}
    (hFN : DependsOn N F) (hFrel : RelabelInvariant F)
    (hZN : DependsOn N Z) (hZrel : RelabelInvariant Z)
    (hFm : Measurable F) (hZm : Measurable Z)
    (hF01 : ∀ ω, F ω ∈ Set.Icc (0:ℝ) 1)
    (hFmono : ∀ (x₀ : Site d) (ω : PData d), F ω ≤ F (addAt x₀ ω))
    (hZanti : ∀ (x₀ : Site d) (ω : PData d), Z (addAt x₀ ω) ≤ Z ω)
    (hZlip : ∀ (x₀ : Site d) (ω : PData d),
      |Z (addAt x₀ ω) - Z ω| ≤ 1 ∧ |Z (delAt x₀ ω) - Z ω| ≤ 1)
    (hZint : Integrable Z (restrictLaw d N (tiltLaw ν lam) ω₀))
    {D : ℝ}
    (hD : HasDerivAt (fun s => ∫ ω, F ω ∂(restrictLaw d N (tiltLaw ν s) ω₀)) D lam) :
    Integrable (fun ω => F ω * Z ω) (restrictLaw d N (tiltLaw ν lam) ω₀) ∧
      |cov (restrictLaw d N (tiltLaw ν lam) ω₀) F Z| ≤ 3 * D := by
  haveI : IsProbabilityMeasure (tiltLaw ν lam) :=
    tiltLaw_isProbability (integrable_exp_tilt hexp hlam0 (le_of_lt hlamθ))
  have hmabs : Integrable (fun k : ℤ => |(k : ℝ)|) (tiltLaw ν lam) := hmeanint.abs
  have hbound := abs_cov_restrictLaw_le hd hFN hFrel.1 hFrel.2 hZN hZrel.1 hZrel.2 hFm hZm
    hF01 hFmono hZanti (fun x₀ ω => (hZlip x₀ ω).1) (fun x₀ ω => (hZlip x₀ ω).2)
    hmabs hmeanle hZint
  have hderiv := hasDerivWithinAt_integral_restrictLaw hd hint hexp hlam0 hlamθ hmeanint N ω₀
    hFN hFm hF01
  have huniq : D = ∑ x ∈ N, cov (pDataLaw d (tiltLaw ν lam)) F (fun ω => ((ω.1 x : ℤ) : ℝ)) :=
    (uniqueDiffOn_Icc hθ lam ⟨hlam0, le_of_lt hlamθ⟩).eq_deriv _ hD.hasDerivWithinAt hderiv
  exact ⟨hbound.1, by rw [huniq]; exact hbound.2⟩

/-- **The two-sided derivative at an interior tilt.**  For `0 < λ < θ` the set
`Set.Icc 0 θ` is a neighbourhood of `λ`, so the derivative within it is a
derivative.  This is the form `thm:subcritical` uses, where the differential
inequality is integrated over `(0, λ₁)`. -/
theorem hasDerivAt_integral_restrictLaw {d : ℕ} (hd : 1 ≤ d) {ν : Measure ℤ}
    [IsProbabilityMeasure ν] (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    {θ : ℝ} (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    {lam : ℝ} (hlam0 : 0 < lam) (hlamθ : lam < θ)
    (hmean : Integrable (fun k : ℤ => (k : ℝ)) (tiltLaw ν lam))
    (N : Finset (Site d)) (ω₀ : PData d) {F : PData d → ℝ}
    (hFN : DependsOn N F) (hFm : Measurable F) (hF01 : ∀ ω, F ω ∈ Set.Icc (0:ℝ) 1) :
    HasDerivAt (fun s => ∫ ω, F ω ∂(restrictLaw d N (tiltLaw ν s) ω₀))
      (∑ x ∈ N, cov (pDataLaw d (tiltLaw ν lam)) F (fun ω => ((ω.1 x : ℤ) : ℝ))) lam :=
  (hasDerivWithinAt_integral_restrictLaw hd hint hexp (le_of_lt hlam0) hlamθ hmean N ω₀
    hFN hFm hF01).hasDerivAt (Icc_mem_nhds hlam0 hlamθ)

end Parking

end
