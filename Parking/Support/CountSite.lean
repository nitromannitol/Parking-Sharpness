/-
Step 2 of `lem:product` at one of the tilted sites.

With the counts at the other sites held fixed, the count at a site is a single
integer with law `ν`, and the mean of the observable over the noise is a
nondecreasing function of it.  The bound of `Support/ParticleStep.lean` at that
site is then the one-site bound of the paper, and `Support/CountStep.lean`
compares its mean with `Cov(f(Y), Y)`.  Extracting one coordinate of the
i.i.d. field is `LatticeProb.measurePreserving_update_infinitePi`.
-/
import Parking.Support.CountStep
import Parking.Support.ParticleStep
import Parking.Support.SceneryHole

open MeasureTheory

noncomputable section

namespace Parking

/-- The mean of `F` over the noise, at fixed counts. -/
def meanF {d : ℕ} (F : PData d → ℝ) (a : Site d → ℤ) : ℝ :=
  ∫ b, F ((a, b) : PData d) ∂(noiseLaw d)

/-- Deleting one particle at `x` from the counts. -/
def delC {d : ℕ} (x : Site d) (a : Site d → ℤ) : Site d → ℤ :=
  fun y => if y = x then a y - 1 else a y

theorem delAt_eq_delC {d : ℕ} (x : Site d) (a : Site d → ℤ) (b : PNoise d) :
    delAt x ((a, b) : PData d) = ((delC x a, b) : PData d) := rfl

theorem meanF_delC {d : ℕ} (F : PData d → ℝ) (x : Site d) (a : Site d → ℤ) :
    meanF F (delC x a) = ∫ b, F (delAt x ((a, b) : PData d)) ∂(noiseLaw d) := rfl

/-- Deleting a particle at `x` lowers the count there by one. -/
theorem delC_update {d : ℕ} (x : Site d) (a : Site d → ℤ) (k : ℤ) :
    delC x (Function.update a x k) = Function.update a x (k - 1) := by
  funext y
  by_cases hy : y = x
  · subst hy
    simp [delC]
  · simp [delC, hy]

/-- **The observable does not decrease with the count at a site.** -/
theorem F_update_monotone {d : ℕ} {F : PData d → ℝ}
    (hFmono : ∀ (x₀ : Site d) (ω : PData d), F ω ≤ F (addAt x₀ ω))
    (x : Site d) (a : Site d → ℤ) (b : PNoise d) :
    Monotone (fun k : ℤ => F ((Function.update a x k, b) : PData d)) := by
  refine monotone_int_of_le_succ fun k => ?_
  have h := hFmono x ((Function.update a x k, b) : PData d)
  have h2 : addAt x ((Function.update a x k, b) : PData d)
      = ((Function.update a x (k + 1), b) : PData d) := by
    simp only [addAt]
    rw [addParticle_update]
  rw [h2] at h
  exact h

/-- The mean of `F` over the noise is measurable in the counts. -/
theorem measurable_meanF {d : ℕ} (hd : 1 ≤ d) {F : PData d → ℝ} (hFm : Measurable F) :
    Measurable (meanF F) := by
  haveI := noiseLaw_isProbability hd
  exact (hFm.stronglyMeasurable.integral_prod_right' (ν := noiseLaw d)).measurable

/-- The mean of `F` over the noise inherits the bounds of `F`. -/
theorem meanF_mem_Icc {d : ℕ} (hd : 1 ≤ d) {F : PData d → ℝ} (hFm : Measurable F)
    (hF01 : ∀ ω, F ω ∈ Set.Icc (0 : ℝ) 1) (a : Site d → ℤ) :
    meanF F a ∈ Set.Icc (0 : ℝ) 1 := by
  haveI := noiseLaw_isProbability hd
  have hm : Measurable (fun b : PNoise d => F ((a, b) : PData d)) :=
    hFm.comp (measurable_const.prodMk measurable_id)
  have hi : Integrable (fun b : PNoise d => F ((a, b) : PData d)) (noiseLaw d) :=
    (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun b => by
        have h := hF01 ((a, b) : PData d)
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [h.1], h.2⟩)
  constructor
  · exact integral_nonneg fun b => (hF01 ((a, b) : PData d)).1
  · calc meanF F a ≤ ∫ _b : PNoise d, (1 : ℝ) ∂(noiseLaw d) :=
        integral_mono hi (integrable_const _) fun b => (hF01 ((a, b) : PData d)).2
      _ = 1 := by simp

/-- The mean of `F` over the noise is a nondecreasing function of the count at a
site. -/
theorem meanF_update_monotone {d : ℕ} (hd : 1 ≤ d) {F : PData d → ℝ} (hFm : Measurable F)
    (hF01 : ∀ ω, F ω ∈ Set.Icc (0 : ℝ) 1)
    (hFmono : ∀ (x₀ : Site d) (ω : PData d), F ω ≤ F (addAt x₀ ω))
    (x : Site d) (a : Site d → ℤ) :
    Monotone (fun k : ℤ => meanF F (Function.update a x k)) := by
  haveI := noiseLaw_isProbability hd
  intro k k' hk
  have hbdd : ∀ m : ℤ, Integrable (fun b : PNoise d =>
      F ((Function.update a x m, b) : PData d)) (noiseLaw d) := by
    intro m
    have hm : Measurable (fun b : PNoise d => F ((Function.update a x m, b) : PData d)) :=
      hFm.comp (measurable_const.prodMk measurable_id)
    exact (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun b => by
        have h := hF01 ((Function.update a x m, b) : PData d)
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [h.1], h.2⟩)
  exact integral_mono (hbdd k) (hbdd k') fun b => F_update_monotone hFmono x a b hk

/-- The covariance with a constant vanishes. -/
theorem cov_const_right {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (g : Ω → ℝ) (c : ℝ) :
    cov μ g (fun _ => c) = 0 := by
  unfold cov
  rw [integral_mul_const, integral_const]
  simp

/-- A covariance is carried along a measure preserving map. -/
theorem cov_comp_measurePreserving {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ρ : Measure β} {f : α → β} (hf : MeasurePreserving f μ ρ)
    (g h : β → ℝ) (hg : AEStronglyMeasurable g ρ) (hh : AEStronglyMeasurable h ρ) :
    cov ρ g h = cov μ (fun a => g (f a)) (fun a => h (f a)) := by
  unfold cov
  rw [← hf.map_eq]
  have hmul : AEStronglyMeasurable (fun ω => g ω * h ω) (Measure.map f μ) := by
    rw [hf.map_eq]; exact hg.mul hh
  have hg' : AEStronglyMeasurable g (Measure.map f μ) := by rw [hf.map_eq]; exact hg
  have hh' : AEStronglyMeasurable h (Measure.map f μ) := by rw [hf.map_eq]; exact hh
  rw [integral_map hf.measurable.aemeasurable hmul,
    integral_map hf.measurable.aemeasurable hg',
    integral_map hf.measurable.aemeasurable hh']

/-- Deleting a particle at a site is measurable on the counts. -/
theorem measurable_delC {d : ℕ} (x : Site d) : Measurable (delC x) := by
  refine measurable_pi_lambda _ fun y => ?_
  show Measurable fun a : Site d → ℤ => if y = x then a y - 1 else a y
  by_cases hy : y = x
  · have he : (fun a : Site d → ℤ => if y = x then a y - 1 else a y)
        = fun a : Site d → ℤ => a y - 1 := by simp [hy]
    rw [he]
    exact (measurable_pi_apply y).sub measurable_const
  · have he : (fun a : Site d → ℤ => if y = x then a y - 1 else a y)
        = fun a : Site d → ℤ => a y := by simp [hy]
    rw [he]
    exact measurable_pi_apply y

/-- The one-site bound is measurable in the counts. -/
theorem measurable_site_step {d : ℕ} (hd : 1 ≤ d) {F : PData d → ℝ} (hFm : Measurable F)
    (x : Site d) :
    Measurable (fun a : Site d → ℤ =>
      ((a x).toNat : ℝ) * (2 * (meanF F a - meanF F (delC x a)))) := by
  have hmeanFm : Measurable (meanF F) := measurable_meanF hd hFm
  refine Measurable.mul ?_ ?_
  · exact (measurable_int_fun (fun k : ℤ => (k.toNat : ℝ))).comp (measurable_pi_apply x)
  · exact measurable_const.mul (hmeanFm.sub (hmeanFm.comp (measurable_delC x)))

/-- The one-site bound is integrable in the counts. -/
theorem integrable_site_step {d : ℕ} (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {F : PData d → ℝ} (hFm : Measurable F) (hF01 : ∀ ω, F ω ∈ Set.Icc (0 : ℝ) 1)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (x : Site d) :
    Integrable (fun a : Site d → ℤ =>
        ((a x).toNat : ℝ) * (2 * (meanF F a - meanF F (delC x a))))
      (LatticeProb.iidLaw d ν) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI := noiseLaw_isProbability hd
  have heval : MeasurePreserving (fun a : Site d → ℤ => a x) (LatticeProb.iidLaw d ν) ν :=
    measurePreserving_eval_infinitePi (fun _ : Site d => ν) x
  have hmeanFb : ∀ a : Site d → ℤ, meanF F a ∈ Set.Icc (0 : ℝ) 1 := meanF_mem_Icc hd hFm hF01
  have habs : ∀ a : Site d → ℤ, |meanF F a - meanF F (delC x a)| ≤ 1 := by
    intro a
    have h1 := hmeanFb a
    have h2 := hmeanFb (delC x a)
    rw [abs_le]
    constructor <;> [linarith [h1.1, h2.2]; linarith [h1.2, h2.1]]
  have hGm : Measurable (fun a : Site d → ℤ =>
      ((a x).toNat : ℝ) * (2 * (meanF F a - meanF F (delC x a)))) :=
    measurable_site_step hd hFm x
  have hcoord : Integrable (fun a : Site d → ℤ => |((a x : ℤ) : ℝ)|)
      (LatticeProb.iidLaw d ν) := heval.integrable_comp_of_integrable hint
  have hGb : ∀ a : Site d → ℤ,
      |((a x).toNat : ℝ) * (2 * (meanF F a - meanF F (delC x a)))| ≤ 2 * |((a x : ℤ) : ℝ)| := by
    intro a
    have h3 : |((a x).toNat : ℝ)| ≤ |((a x : ℤ) : ℝ)| := by
      rcases le_or_gt 0 (a x) with hk | hk
      · have hk' : (((a x).toNat : ℤ) : ℝ) = ((a x : ℤ) : ℝ) :=
          congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hk)
        rw [show (((a x).toNat : ℝ)) = (((a x).toNat : ℤ) : ℝ) by push_cast; ring, hk']
      · have hk0 : (a x).toNat = 0 := Int.toNat_of_nonpos (by omega)
        rw [hk0]
        simp
    have h4 : |2 * (meanF F a - meanF F (delC x a))| ≤ 2 := by
      rw [abs_mul, abs_two]
      linarith [habs a]
    calc |((a x).toNat : ℝ) * (2 * (meanF F a - meanF F (delC x a)))|
        = |((a x).toNat : ℝ)| * |2 * (meanF F a - meanF F (delC x a))| := abs_mul _ _
      _ ≤ |((a x : ℤ) : ℝ)| * 2 := mul_le_mul h3 h4 (abs_nonneg _) (abs_nonneg _)
      _ = 2 * |((a x : ℤ) : ℝ)| := by ring
  refine Integrable.mono' (hcoord.const_mul 2) hGm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => ?_)
  simpa [Real.norm_eq_abs] using hGb a

/-- **Step 2 at one site.**  The mean of the one-site bound at `x` is at most
twice the covariance of the mean of `F` with the count at `x`. -/
theorem integral_site_step_le {d : ℕ} (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {F : PData d → ℝ} (hFm : Measurable F) (hF01 : ∀ ω, F ω ∈ Set.Icc (0 : ℝ) 1)
    (hFmono : ∀ (x₀ : Site d) (ω : PData d), F ω ≤ F (addAt x₀ ω))
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k, (k : ℝ) ∂ν ≤ 0)
    (x : Site d) :
    ∫ a, ((a x).toNat : ℝ) * (2 * (meanF F a - meanF F (delC x a)))
        ∂(LatticeProb.iidLaw d ν)
      ≤ 2 * cov (LatticeProb.iidLaw d ν) (meanF F) (fun a => ((a x : ℤ) : ℝ)) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI := noiseLaw_isProbability hd
  have hu : MeasurePreserving (fun q : (Site d → ℤ) × ℤ => Function.update q.1 x q.2)
      ((LatticeProb.iidLaw d ν).prod ν) (LatticeProb.iidLaw d ν) :=
    LatticeProb.measurePreserving_update_infinitePi (fun _ : Site d => ν) x
  have heval : MeasurePreserving (fun a : Site d → ℤ => a x) (LatticeProb.iidLaw d ν) ν :=
    measurePreserving_eval_infinitePi (fun _ : Site d => ν) x
  have hmeanFm : Measurable (meanF F) := measurable_meanF hd hFm
  have hmeanFb : ∀ a : Site d → ℤ, meanF F a ∈ Set.Icc (0 : ℝ) 1 := meanF_mem_Icc hd hFm hF01
  have hGm : Measurable (fun a : Site d → ℤ =>
      ((a x).toNat : ℝ) * (2 * (meanF F a - meanF F (delC x a)))) :=
    measurable_site_step hd hFm x
  have hGi : Integrable (fun a : Site d → ℤ =>
      ((a x).toNat : ℝ) * (2 * (meanF F a - meanF F (delC x a)))) (LatticeProb.iidLaw d ν) :=
    integrable_site_step hd hFm hF01 hint x
  -- transport to the product
  have hpt : ∀ q : (Site d → ℤ) × ℤ,
      (((Function.update q.1 x q.2) x).toNat : ℝ)
          * (2 * (meanF F (Function.update q.1 x q.2)
              - meanF F (delC x (Function.update q.1 x q.2))))
        = ((q.2).toNat : ℝ) * (2 * (meanF F (Function.update q.1 x q.2)
            - meanF F (Function.update q.1 x (q.2 - 1)))) := by
    intro q
    rw [Function.update_self, delC_update]
  have hA : ∫ a, ((a x).toNat : ℝ) * (2 * (meanF F a - meanF F (delC x a)))
        ∂(LatticeProb.iidLaw d ν)
      = ∫ q, ((q.2).toNat : ℝ) * (2 * (meanF F (Function.update q.1 x q.2)
            - meanF F (Function.update q.1 x (q.2 - 1))))
          ∂((LatticeProb.iidLaw d ν).prod ν) := by
    conv_lhs => rw [← hu.map_eq]
    rw [integral_map hu.measurable.aemeasurable hGm.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hHi : Integrable (fun q : (Site d → ℤ) × ℤ =>
      ((q.2).toNat : ℝ) * (2 * (meanF F (Function.update q.1 x q.2)
        - meanF F (Function.update q.1 x (q.2 - 1)))))
      ((LatticeProb.iidLaw d ν).prod ν) :=
    (hu.integrable_comp_of_integrable hGi).congr
      (Filter.Eventually.of_forall hpt)
  rw [hA, integral_prod _ hHi]
  -- the one-site bound, with the counts at the other sites held fixed
  have hfbdd : ∀ (a : Site d → ℤ) (k : ℤ), |meanF F (Function.update a x k)| ≤ 1 := by
    intro a k
    have h := hmeanFb (Function.update a x k)
    rw [abs_le]
    exact ⟨by linarith [h.1], h.2⟩
  have hC : ∀ a : Site d → ℤ,
      (∫ k, ((k.toNat : ℝ) * (2 * (meanF F (Function.update a x k)
            - meanF F (Function.update a x (k - 1))))) ∂ν)
        ≤ 2 * cov ν (fun k => meanF F (Function.update a x k)) (fun k : ℤ => (k : ℝ)) :=
    fun a => integral_count_step_le (meanF_update_monotone hd hFm hF01 hFmono x a)
      (hfbdd a) hint hmean
  -- the covariance of the mean of `F` with the count at `x`
  have hcoordm : Measurable (fun a : Site d → ℤ => ((a x : ℤ) : ℝ)) :=
    (measurable_int_fun (fun k : ℤ => (k : ℝ))).comp (measurable_pi_apply x)
  have hFum : Measurable (fun q : (Site d → ℤ) × ℤ =>
      meanF F (Function.update q.1 x q.2)) := hmeanFm.comp hu.measurable
  have hFub : ∀ q : (Site d → ℤ) × ℤ, |meanF F (Function.update q.1 x q.2)| ≤ 1 :=
    fun q => hfbdd q.1 q.2
  have hFui : Integrable (fun q : (Site d → ℤ) × ℤ =>
      meanF F (Function.update q.1 x q.2)) ((LatticeProb.iidLaw d ν).prod ν) :=
    (integrable_const (1 : ℝ)).mono' hFum.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by simpa [Real.norm_eq_abs] using hFub q)
  have hcast : Integrable (fun k : ℤ => (k : ℝ)) ν := integrable_cast hint
  have hZum : Measurable (fun q : (Site d → ℤ) × ℤ => ((q.2 : ℤ) : ℝ)) :=
    (measurable_int_fun (fun k : ℤ => (k : ℝ))).comp measurable_snd
  have hZui : Integrable (fun q : (Site d → ℤ) × ℤ => ((q.2 : ℤ) : ℝ))
      ((LatticeProb.iidLaw d ν).prod ν) := hcast.comp_snd _
  have hFZi : Integrable (fun q : (Site d → ℤ) × ℤ =>
      meanF F (Function.update q.1 x q.2) * ((q.2 : ℤ) : ℝ))
      ((LatticeProb.iidLaw d ν).prod ν) := by
    refine Integrable.mono' hZui.abs (hFum.mul hZum).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hFub q
    have h2 : (0 : ℝ) ≤ |((q.2 : ℤ) : ℝ)| := abs_nonneg _
    have h3 : (0 : ℝ) ≤ |meanF F (Function.update q.1 x q.2)| := abs_nonneg _
    nlinarith
  have hfz : Integrable (fun a : Site d → ℤ =>
      (∫ k, meanF F (Function.update a x k) ∂ν) * ∫ k : ℤ, ((k : ℤ) : ℝ) ∂ν)
      (LatticeProb.iidLaw d ν) := (Integrable.integral_prod_left hFui).mul_const _
  have hdec := cov_prod_decomp (LatticeProb.iidLaw d ν) ν
    (fun q : (Site d → ℤ) × ℤ => meanF F (Function.update q.1 x q.2))
    (fun q : (Site d → ℤ) × ℤ => ((q.2 : ℤ) : ℝ)) hFZi hFui hZui hfz
  dsimp only at hdec
  rw [cov_const_right] at hdec
  have hEcov : cov (LatticeProb.iidLaw d ν) (meanF F) (fun a => ((a x : ℤ) : ℝ))
      = ∫ a, cov ν (fun k => meanF F (Function.update a x k)) (fun k : ℤ => (k : ℝ))
          ∂(LatticeProb.iidLaw d ν) := by
    rw [cov_comp_measurePreserving hu (meanF F) (fun a => ((a x : ℤ) : ℝ))
      hmeanFm.aestronglyMeasurable hcoordm.aestronglyMeasurable]
    simp only [Function.update_self]
    rw [hdec, zero_add]
  have hcovi : Integrable (fun a : Site d → ℤ =>
      cov ν (fun k => meanF F (Function.update a x k)) (fun k : ℤ => (k : ℝ)))
      (LatticeProb.iidLaw d ν) :=
    ((Integrable.integral_prod_left hFZi).sub hfz).congr
      (Filter.Eventually.of_forall fun a => rfl)
  have hinner : Integrable (fun a : Site d → ℤ =>
      ∫ k, ((k.toNat : ℝ) * (2 * (meanF F (Function.update a x k)
        - meanF F (Function.update a x (k - 1))))) ∂ν) (LatticeProb.iidLaw d ν) :=
    Integrable.integral_prod_left hHi
  calc ∫ a, (∫ k, ((k.toNat : ℝ) * (2 * (meanF F (Function.update a x k)
          - meanF F (Function.update a x (k - 1))))) ∂ν) ∂(LatticeProb.iidLaw d ν)
      ≤ ∫ a, 2 * cov ν (fun k => meanF F (Function.update a x k)) (fun k : ℤ => (k : ℝ))
          ∂(LatticeProb.iidLaw d ν) := integral_mono hinner (hcovi.const_mul 2) hC
    _ = 2 * ∫ a, cov ν (fun k => meanF F (Function.update a x k)) (fun k : ℤ => (k : ℝ))
          ∂(LatticeProb.iidLaw d ν) := integral_const_mul 2 _
    _ = 2 * cov (LatticeProb.iidLaw d ν) (meanF F) (fun a => ((a x : ℤ) : ℝ)) := by
        rw [hEcov]

/-- **The mean of the conditional covariances.**  This is the paper's
`E|Cov(F, Z | Y)| ≤ 2 Cov(f(Y), Y)` at `parking.tex:2391-2394`, for the finite
family of tilted sites. -/
theorem integral_abs_cov_noise_le {d : ℕ} (hd : 1 ≤ d) {ν : Measure ℤ}
    [IsProbabilityMeasure ν] {N : Finset (Site d)} {F Z : PData d → ℝ}
    (hFN : DependsOn N F) (hFsym : SymmetricInParticles F) (hFP : ReadsParticles F)
    (hZN : DependsOn N Z) (hZsym : SymmetricInParticles Z) (hZP : ReadsParticles Z)
    (hFm : Measurable F) (hZm : Measurable Z)
    (hF01 : ∀ ω, F ω ∈ Set.Icc (0 : ℝ) 1)
    (hFmono : ∀ (x₀ : Site d) (ω : PData d), F ω ≤ F (addAt x₀ ω))
    (hZanti : ∀ (x₀ : Site d) (ω : PData d), Z (addAt x₀ ω) ≤ Z ω)
    (hZlip : ∀ (x₀ : Site d) (ω : PData d), |Z (delAt x₀ ω) - Z ω| ≤ 1)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k, (k : ℝ) ∂ν ≤ 0)
    (hZI : Integrable Z (pDataLaw d ν))
    (hFZI : Integrable (fun ω => F ω * Z ω) (pDataLaw d ν)) :
    ∫ a, |cov (noiseLaw d) (fun b => F ((a, b) : PData d)) (fun b => Z ((a, b) : PData d))|
        ∂(LatticeProb.iidLaw d ν)
      ≤ 2 * ∑ x ∈ N, cov (LatticeProb.iidLaw d ν) (meanF F) (fun a => ((a x : ℤ) : ℝ)) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI : IsProbabilityMeasure (stepLaw d) := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    LatticeProb.uniformUnit_isProbability
  haveI : IsProbabilityMeasure (moveLaw d) := by unfold moveLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  haveI : IsProbabilityMeasure (noiseLaw d) := by unfold noiseLaw; infer_instance
  have hmeanFm : Measurable (meanF F) := measurable_meanF hd hFm
  have hmeanFb : ∀ a : Site d → ℤ, meanF F a ∈ Set.Icc (0 : ℝ) 1 := meanF_mem_Icc hd hFm hF01
  have hsec : ∀ᵐ a ∂(LatticeProb.iidLaw d ν),
      Integrable (fun b : PNoise d => Z ((a, b) : PData d)) (noiseLaw d) :=
    hZI.prod_right_ae
  have hbd : ∀ᵐ a ∂(LatticeProb.iidLaw d ν),
      |cov (noiseLaw d) (fun b => F ((a, b) : PData d)) (fun b => Z ((a, b) : PData d))|
        ≤ ∑ x ∈ N, ((a x).toNat : ℝ) * (2 * (meanF F a - meanF F (delC x a))) := by
    filter_upwards [hsec] with a ha
    exact abs_cov_noise_le hd hFN hFsym hFP hZN hZsym hZP hFm hZm hF01 hFmono hZanti hZlip a ha
  have hi1 : Integrable (fun a : Site d → ℤ =>
      ∫ b, F ((a, b) : PData d) * Z ((a, b) : PData d) ∂(noiseLaw d))
      (LatticeProb.iidLaw d ν) := Integrable.integral_prod_left hFZI
  have hi2 : Integrable (fun a : Site d → ℤ => ∫ b, Z ((a, b) : PData d) ∂(noiseLaw d))
      (LatticeProb.iidLaw d ν) := Integrable.integral_prod_left hZI
  have hi3 : Integrable (fun a : Site d → ℤ =>
      meanF F a * ∫ b, Z ((a, b) : PData d) ∂(noiseLaw d)) (LatticeProb.iidLaw d ν) :=
    hi2.bdd_mul hmeanFm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => by
        have h := hmeanFb a
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [h.1], h.2⟩)
  have hcovi : Integrable (fun a : Site d → ℤ =>
      cov (noiseLaw d) (fun b => F ((a, b) : PData d)) (fun b => Z ((a, b) : PData d)))
      (LatticeProb.iidLaw d ν) :=
    (hi1.sub hi3).congr (Filter.Eventually.of_forall fun a => rfl)
  have hsumi : Integrable (fun a : Site d → ℤ =>
      ∑ x ∈ N, ((a x).toNat : ℝ) * (2 * (meanF F a - meanF F (delC x a))))
      (LatticeProb.iidLaw d ν) :=
    integrable_finsetSum N fun x _ => integrable_site_step hd hFm hF01 hint x
  calc ∫ a, |cov (noiseLaw d) (fun b => F ((a, b) : PData d)) (fun b => Z ((a, b) : PData d))|
          ∂(LatticeProb.iidLaw d ν)
      ≤ ∫ a, ∑ x ∈ N, ((a x).toNat : ℝ) * (2 * (meanF F a - meanF F (delC x a)))
          ∂(LatticeProb.iidLaw d ν) := integral_mono_ae hcovi.abs hsumi hbd
    _ = ∑ x ∈ N, ∫ a, ((a x).toNat : ℝ) * (2 * (meanF F a - meanF F (delC x a)))
          ∂(LatticeProb.iidLaw d ν) :=
        integral_finsetSum N fun x _ => integrable_site_step hd hFm hF01 hint x
    _ ≤ ∑ x ∈ N, 2 * cov (LatticeProb.iidLaw d ν) (meanF F) (fun a => ((a x : ℤ) : ℝ)) :=
        Finset.sum_le_sum fun x _ => integral_site_step_le hd hFm hF01 hFmono hint hmean x
    _ = 2 * ∑ x ∈ N, cov (LatticeProb.iidLaw d ν) (meanF F) (fun a => ((a x : ℤ) : ℝ)) := by
        rw [Finset.mul_sum]

end Parking

end
