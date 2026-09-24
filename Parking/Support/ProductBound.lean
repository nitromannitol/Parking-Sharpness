/-
The three steps of `lem:product` combined.

The covariance under the particle-driven law splits into the covariance of the
two conditional means given the counts and the mean of the conditional
covariance given the counts (`Support/NoiseSplice.lean`).  The first is bounded
by Step 1 (`Support/CountFiltration.lean`) and the second by Step 2
(`Support/CountSite.lean`), each by the sum over the tilted sites of the
covariance of the mean of `F` with the count there, so the covariance is at most
three times that sum.
-/
import Parking.Support.CountFiltration
import Parking.Support.NoiseSplice
import Parking.Support.RestrictLaw

open MeasureTheory

noncomputable section

namespace Parking

/-- A function of the integers whose consecutive increments are at most one is
one-Lipschitz. -/
theorem lipschitz_int_of_succ {g : ℤ → ℝ} (h : ∀ n : ℤ, |g (n + 1) - g n| ≤ 1) (k k' : ℤ) :
    |g k - g k'| ≤ |(k : ℝ) - (k' : ℝ)| := by
  have key : ∀ m n : ℤ, m ≤ n → |g n - g m| ≤ (n : ℝ) - (m : ℝ) := by
    intro m n hmn
    induction n, hmn using Int.leInduction with
    | base => simp
    | succ n hn ih =>
        have h1 := h n
        have h2 : |g (n + 1) - g m| ≤ |g (n + 1) - g n| + |g n - g m| := by
          calc |g (n + 1) - g m| = |(g (n + 1) - g n) + (g n - g m)| := by ring_nf
            _ ≤ _ := abs_add_le _ _
        push_cast
        linarith
  rcases le_total k k' with hk | hk
  · have hkey := key k k' hk
    have h4 : (k : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hk
    rw [abs_sub_comm]
    calc |g k' - g k| ≤ (k' : ℝ) - (k : ℝ) := hkey
      _ = |(k : ℝ) - (k' : ℝ)| := by
          rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  · have hkey := key k' k hk
    have h4 : (k' : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    calc |g k - g k'| ≤ (k : ℝ) - (k' : ℝ) := hkey
      _ = |(k : ℝ) - (k' : ℝ)| := by rw [abs_of_nonneg (by linarith)]

/-- One step of the count at a site changes the observable by at most one. -/
theorem abs_sub_step_le {d : ℕ} {Z : PData d → ℝ}
    (hZlipadd : ∀ (x₀ : Site d) (ω : PData d), |Z (addAt x₀ ω) - Z ω| ≤ 1)
    (y : Site d) (c : Site d → ℤ) (b : PNoise d) (n : ℤ) :
    |Z ((Function.update c y (n + 1), b) : PData d)
      - Z ((Function.update c y n, b) : PData d)| ≤ 1 := by
  have h := hZlipadd y ((Function.update c y n, b) : PData d)
  have h2 : addAt y ((Function.update c y n, b) : PData d)
      = ((Function.update c y (n + 1), b) : PData d) := by
    simp only [addAt]
    rw [addParticle_update]
  rw [h2] at h
  exact h

/-- The observable is one-Lipschitz in the count at each site. -/
theorem abs_sub_update_le {d : ℕ} {Z : PData d → ℝ}
    (hZlipadd : ∀ (x₀ : Site d) (ω : PData d), |Z (addAt x₀ ω) - Z ω| ≤ 1)
    (y : Site d) (c : Site d → ℤ) (b : PNoise d) (k k' : ℤ) :
    |Z ((Function.update c y k, b) : PData d) - Z ((Function.update c y k', b) : PData d)|
      ≤ |(k : ℝ) - (k' : ℝ)| :=
  lipschitz_int_of_succ (g := fun n : ℤ => Z ((Function.update c y n, b) : PData d))
    (fun n => abs_sub_step_le hZlipadd y c b n) k k'

/-- **Changing the counts at finitely many sites.**  An observable that changes
by at most one when a particle is added changes by at most the total change in
the counts it reads. -/
theorem abs_sub_le_sum_counts {d : ℕ} {Z : PData d → ℝ}
    (hZlipadd : ∀ (x₀ : Site d) (ω : PData d), |Z (addAt x₀ ω) - Z ω| ≤ 1)
    (b : PNoise d) :
    ∀ (M : Finset (Site d)) (a a' : Site d → ℤ), (∀ x, x ∉ M → a x = a' x) →
      |Z ((a, b) : PData d) - Z ((a', b) : PData d)|
        ≤ ∑ x ∈ M, |(a x : ℝ) - (a' x : ℝ)| := by
  intro M
  induction M using Finset.induction_on with
  | empty =>
      intro a a' h
      have haa : a = a' := funext fun x => h x (by simp)
      rw [haa]
      simp
  | insert x M' hx ih =>
      intro a a' h
      have hoff : ∀ y, y ∉ M' → Function.update a x (a' x) y = a' y := by
        intro y hy
        by_cases hyx : y = x
        · subst hyx; simp
        · rw [Function.update_of_ne hyx]
          refine h y fun hc => ?_
          rcases Finset.mem_insert.mp hc with hc' | hc'
          · exact hyx hc'
          · exact hy hc'
      have hstep : |Z ((a, b) : PData d)
          - Z ((Function.update a x (a' x), b) : PData d)| ≤ |(a x : ℝ) - (a' x : ℝ)| := by
        have hh := abs_sub_update_le hZlipadd x a b (a x) (a' x)
        rwa [Function.update_eq_self] at hh
      have hrest := ih (Function.update a x (a' x)) a' hoff
      have hsum : ∑ y ∈ M', |((Function.update a x (a' x) y : ℤ) : ℝ) - (a' y : ℝ)|
          = ∑ y ∈ M', |(a y : ℝ) - (a' y : ℝ)| := by
        refine Finset.sum_congr rfl fun y hy => ?_
        have hyx : y ≠ x := fun hc => hx (hc ▸ hy)
        rw [Function.update_of_ne hyx]
      rw [hsum] at hrest
      rw [Finset.sum_insert hx]
      calc |Z ((a, b) : PData d) - Z ((a', b) : PData d)|
          ≤ |Z ((a, b) : PData d) - Z ((Function.update a x (a' x), b) : PData d)|
            + |Z ((Function.update a x (a' x), b) : PData d) - Z ((a', b) : PData d)| := by
              calc |Z ((a, b) : PData d) - Z ((a', b) : PData d)|
                  = |(Z ((a, b) : PData d) - Z ((Function.update a x (a' x), b) : PData d))
                      + (Z ((Function.update a x (a' x), b) : PData d)
                        - Z ((a', b) : PData d))| := by ring_nf
                _ ≤ _ := abs_add_le _ _
        _ ≤ |(a x : ℝ) - (a' x : ℝ)| + ∑ y ∈ M', |(a y : ℝ) - (a' y : ℝ)| :=
            add_le_add hstep hrest

/-- All the sections of the observable are integrable as soon as one is. -/
theorem integrable_section_of_section {d : ℕ} {Z : PData d → ℝ} {N : Finset (Site d)}
    (hZm : Measurable Z) (hZN : DependsOn N Z)
    (hZlipadd : ∀ (x₀ : Site d) (ω : PData d), |Z (addAt x₀ ω) - Z ω| ≤ 1)
    (hd : 1 ≤ d) {a₀ : Site d → ℤ}
    (h₀ : Integrable (fun b : PNoise d => Z ((a₀, b) : PData d)) (noiseLaw d))
    (a : Site d → ℤ) :
    Integrable (fun b : PNoise d => Z ((a, b) : PData d)) (noiseLaw d) := by
  classical
  haveI := noiseLaw_isProbability hd
  set a₁ : Site d → ℤ := fun y => if y ∈ N then a y else a₀ y with ha₁
  have heq : ∀ b : PNoise d, Z ((a, b) : PData d) = Z ((a₁, b) : PData d) := by
    intro b
    refine hZN _ _ (fun y hy => ?_) (fun q _ => rfl) (fun q _ => rfl)
    simp [ha₁, hy]
  have hoff : ∀ y, y ∉ N → a₁ y = a₀ y := by
    intro y hy
    simp [ha₁, hy]
  have hbnd : ∀ b : PNoise d,
      |Z ((a, b) : PData d)| ≤ |Z ((a₀, b) : PData d)|
        + ∑ x ∈ N, |(a₁ x : ℝ) - (a₀ x : ℝ)| := by
    intro b
    have h := abs_sub_le_sum_counts hZlipadd b N a₁ a₀ hoff
    rw [heq b]
    calc |Z ((a₁, b) : PData d)|
        = |(Z ((a₁, b) : PData d) - Z ((a₀, b) : PData d)) + Z ((a₀, b) : PData d)| := by
          ring_nf
      _ ≤ |Z ((a₁, b) : PData d) - Z ((a₀, b) : PData d)| + |Z ((a₀, b) : PData d)| :=
          abs_add_le _ _
      _ ≤ ∑ x ∈ N, |(a₁ x : ℝ) - (a₀ x : ℝ)| + |Z ((a₀, b) : PData d)| := by
          linarith [h]
      _ = |Z ((a₀, b) : PData d)| + ∑ x ∈ N, |(a₁ x : ℝ) - (a₀ x : ℝ)| := by ring
  have hm : Measurable (fun b : PNoise d => Z ((a, b) : PData d)) :=
    hZm.comp (measurable_const.prodMk measurable_id)
  exact Integrable.mono' (h₀.abs.add (integrable_const _)) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun b => by
      simpa [Real.norm_eq_abs] using hbnd b)

/-- Every section of an integrable observable is integrable. -/
theorem integrable_sections {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {Z : PData d → ℝ} {N : Finset (Site d)} (hd : 1 ≤ d)
    (hZm : Measurable Z) (hZN : DependsOn N Z)
    (hZlipadd : ∀ (x₀ : Site d) (ω : PData d), |Z (addAt x₀ ω) - Z ω| ≤ 1)
    (hZI : Integrable Z (pDataLaw d ν)) (a : Site d → ℤ) :
    Integrable (fun b : PNoise d => Z ((a, b) : PData d)) (noiseLaw d) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI : IsProbabilityMeasure (stepLaw d) := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    LatticeProb.uniformUnit_isProbability
  haveI : IsProbabilityMeasure (moveLaw d) := by unfold moveLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  haveI : IsProbabilityMeasure (noiseLaw d) := by unfold noiseLaw; infer_instance
  obtain ⟨a₀, h₀⟩ := (hZI.prod_right_ae).exists
  exact integrable_section_of_section hZm hZN hZlipadd hd h₀ a

/-- **The mean of `Z` over the noise is one-Lipschitz in each count.** -/
theorem meanF_update_lipschitz {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hd : 1 ≤ d) {Z : PData d → ℝ} {N : Finset (Site d)}
    (hZm : Measurable Z) (hZN : DependsOn N Z)
    (hZlipadd : ∀ (x₀ : Site d) (ω : PData d), |Z (addAt x₀ ω) - Z ω| ≤ 1)
    (hZI : Integrable Z (pDataLaw d ν))
    (y : Site d) (a : Site d → ℤ) (k k' : ℤ) :
    |meanF Z (Function.update a y k) - meanF Z (Function.update a y k')|
      ≤ |(k : ℝ) - (k' : ℝ)| := by
  haveI := noiseLaw_isProbability hd
  have hsec : ∀ c : Site d → ℤ,
      Integrable (fun b : PNoise d => Z ((c, b) : PData d)) (noiseLaw d) :=
    fun c => integrable_sections hd hZm hZN hZlipadd hZI c
  unfold meanF
  rw [← integral_sub (hsec (Function.update a y k)) (hsec (Function.update a y k'))]
  calc |∫ b, (Z ((Function.update a y k, b) : PData d)
          - Z ((Function.update a y k', b) : PData d)) ∂(noiseLaw d)|
      ≤ ∫ b, |Z ((Function.update a y k, b) : PData d)
          - Z ((Function.update a y k', b) : PData d)| ∂(noiseLaw d) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _b : PNoise d, |(k : ℝ) - (k' : ℝ)| ∂(noiseLaw d) :=
        integral_mono ((hsec (Function.update a y k)).sub
          (hsec (Function.update a y k'))).abs (integrable_const _)
          (fun b => abs_sub_update_le hZlipadd y a b k k')
    _ = |(k : ℝ) - (k' : ℝ)| := by simp

/-- **The covariance with a count reads only the counts.** -/
theorem cov_pData_coord {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν] (hd : 1 ≤ d)
    {F : PData d → ℝ} (hFm : Measurable F) (hF01 : ∀ ω, F ω ∈ Set.Icc (0 : ℝ) 1)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (x : Site d) :
    cov (pDataLaw d ν) F (fun ω => ((ω.1 x : ℤ) : ℝ))
      = cov (LatticeProb.iidLaw d ν) (meanF F) (fun a => ((a x : ℤ) : ℝ)) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI := noiseLaw_isProbability hd
  haveI : IsProbabilityMeasure (pDataLaw d ν) := by
    rw [pDataLaw_eq_prod]; infer_instance
  have hFb : ∀ ω : PData d, ‖F ω‖ ≤ 1 := by
    intro ω
    have h := hF01 ω
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [h.1], h.2⟩
  have hFI : Integrable F (pDataLaw d ν) :=
    (integrable_const (1 : ℝ)).mono' hFm.aestronglyMeasurable
      (Filter.Eventually.of_forall hFb)
  have hZI : Integrable (fun ω : PData d => ((ω.1 x : ℤ) : ℝ)) (pDataLaw d ν) :=
    (integrable_coord hint x).comp_fst (noiseLaw d)
  have hFZI : Integrable (fun ω : PData d => F ω * ((ω.1 x : ℤ) : ℝ)) (pDataLaw d ν) :=
    hZI.bdd_mul hFm.aestronglyMeasurable (Filter.Eventually.of_forall hFb)
  have hfz : Integrable (fun a : Site d → ℤ =>
      (∫ b, F ((a, b) : PData d) ∂(noiseLaw d))
        * ∫ _b : PNoise d, ((a x : ℤ) : ℝ) ∂(noiseLaw d)) (LatticeProb.iidLaw d ν) := by
    have hsimp : (fun a : Site d → ℤ =>
        (∫ b, F ((a, b) : PData d) ∂(noiseLaw d))
          * ∫ _b : PNoise d, ((a x : ℤ) : ℝ) ∂(noiseLaw d))
        = fun a : Site d → ℤ => meanF F a * ((a x : ℤ) : ℝ) := by
      funext a
      simp [meanF]
    rw [hsimp]
    exact (integrable_coord hint x).bdd_mul (measurable_meanF hd hFm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => by
        have h := meanF_mem_Icc hd hFm hF01 a
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [h.1], h.2⟩)
  have hdec := cov_pData_split d ν hd F (fun ω : PData d => ((ω.1 x : ℤ) : ℝ))
    hFZI hFI hZI hfz
  have h0 : ∫ a, cov (noiseLaw d) (fun b => F ((a, b) : PData d))
      (fun _b : PNoise d => ((a x : ℤ) : ℝ)) ∂(LatticeProb.iidLaw d ν) = 0 := by
    have hz : ∀ a : Site d → ℤ, cov (noiseLaw d) (fun b => F ((a, b) : PData d))
        (fun _b : PNoise d => ((a x : ℤ) : ℝ)) = 0 :=
      fun a => cov_const_right (noiseLaw d) _ _
    simp [hz]
  have h1 : (fun a : Site d → ℤ => ∫ _b : PNoise d, ((a x : ℤ) : ℝ) ∂(noiseLaw d))
      = fun a : Site d → ℤ => ((a x : ℤ) : ℝ) := by
    funext a
    simp
  rw [h0, add_zero, h1] at hdec
  exact hdec

/-- **`lem:product` without its derivative.**  The covariance of the two
observables is at most three times the sum of the covariances of `F` with the
counts at the tilted sites. -/
theorem abs_cov_pData_le {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν] (hd : 1 ≤ d)
    {N : Finset (Site d)} {F Z : PData d → ℝ}
    (hFN : DependsOn N F) (hFsym : SymmetricInParticles F) (hFP : ReadsParticles F)
    (hZN : DependsOn N Z) (hZsym : SymmetricInParticles Z) (hZP : ReadsParticles Z)
    (hFm : Measurable F) (hZm : Measurable Z)
    (hF01 : ∀ ω, F ω ∈ Set.Icc (0 : ℝ) 1)
    (hFmono : ∀ (x₀ : Site d) (ω : PData d), F ω ≤ F (addAt x₀ ω))
    (hZanti : ∀ (x₀ : Site d) (ω : PData d), Z (addAt x₀ ω) ≤ Z ω)
    (hZlipadd : ∀ (x₀ : Site d) (ω : PData d), |Z (addAt x₀ ω) - Z ω| ≤ 1)
    (hZlipdel : ∀ (x₀ : Site d) (ω : PData d), |Z (delAt x₀ ω) - Z ω| ≤ 1)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k, (k : ℝ) ∂ν ≤ 0)
    (hZI : Integrable Z (pDataLaw d ν))
    (hFZI : Integrable (fun ω => F ω * Z ω) (pDataLaw d ν)) :
    |cov (pDataLaw d ν) F Z|
      ≤ 3 * ∑ x ∈ N, cov (pDataLaw d ν) F (fun ω => ((ω.1 x : ℤ) : ℝ)) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI := noiseLaw_isProbability hd
  haveI : IsProbabilityMeasure (pDataLaw d ν) := by
    rw [pDataLaw_eq_prod]; infer_instance
  have hFb : ∀ ω : PData d, ‖F ω‖ ≤ 1 := by
    intro ω
    have h := hF01 ω
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [h.1], h.2⟩
  have hFI : Integrable F (pDataLaw d ν) :=
    (integrable_const (1 : ℝ)).mono' hFm.aestronglyMeasurable
      (Filter.Eventually.of_forall hFb)
  have hmeanZi : Integrable (meanF Z) (LatticeProb.iidLaw d ν) :=
    Integrable.integral_prod_left hZI
  have hfz : Integrable (fun a : Site d → ℤ =>
      (∫ b, F ((a, b) : PData d) ∂(noiseLaw d)) * ∫ b, Z ((a, b) : PData d) ∂(noiseLaw d))
      (LatticeProb.iidLaw d ν) :=
    hmeanZi.bdd_mul (measurable_meanF hd hFm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => by
        have h : (∫ b, F ((a, b) : PData d) ∂(noiseLaw d)) ∈ Set.Icc (0 : ℝ) 1 :=
          meanF_mem_Icc hd hFm hF01 a
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [h.1], h.2⟩)
  have hsplit := cov_pData_split d ν hd F Z hFZI hFI hZI hfz
  have hstep1 := abs_cov_counts_le hint N (meanF F) (meanF Z)
    (measurable_meanF hd hFm) (measurable_meanF hd hZm)
    (meanF_dependsOnCounts hFN) (meanF_dependsOnCounts hZN)
    (fun a => by
      have h := meanF_mem_Icc hd hFm hF01 a
      rw [abs_le]
      exact ⟨by linarith [h.1], h.2⟩)
    (fun y a => meanF_update_monotone hd hFm hF01 hFmono y a)
    (fun y a k k' => meanF_update_lipschitz hd hZm hZN hZlipadd hZI y a k k')
    hmeanZi
  have hstep2 := integral_abs_cov_noise_le hd hFN hFsym hFP hZN hZsym hZP hFm hZm hF01
    hFmono hZanti hZlipdel hint hmean hZI hFZI
  have hcond : |∫ a, cov (noiseLaw d) (fun b => F ((a, b) : PData d))
        (fun b => Z ((a, b) : PData d)) ∂(LatticeProb.iidLaw d ν)|
      ≤ 2 * ∑ x ∈ N, cov (LatticeProb.iidLaw d ν) (meanF F) (fun a => ((a x : ℤ) : ℝ)) :=
    le_trans abs_integral_le_integral_abs hstep2
  have hsum : ∑ x ∈ N, cov (pDataLaw d ν) F (fun ω => ((ω.1 x : ℤ) : ℝ))
      = ∑ x ∈ N, cov (LatticeProb.iidLaw d ν) (meanF F) (fun a => ((a x : ℤ) : ℝ)) :=
    Finset.sum_congr rfl fun x _ => cov_pData_coord hd hFm hF01 hint x
  rw [hsum, hsplit]
  calc |cov (LatticeProb.iidLaw d ν) (meanF F) (meanF Z)
        + ∫ a, cov (noiseLaw d) (fun b => F ((a, b) : PData d))
            (fun b => Z ((a, b) : PData d)) ∂(LatticeProb.iidLaw d ν)|
      ≤ |cov (LatticeProb.iidLaw d ν) (meanF F) (meanF Z)|
        + |∫ a, cov (noiseLaw d) (fun b => F ((a, b) : PData d))
            (fun b => Z ((a, b) : PData d)) ∂(LatticeProb.iidLaw d ν)| := abs_add_le _ _
    _ ≤ (∑ x ∈ N, cov (LatticeProb.iidLaw d ν) (meanF F) (fun a => ((a x : ℤ) : ℝ)))
        + 2 * ∑ x ∈ N, cov (LatticeProb.iidLaw d ν) (meanF F) (fun a => ((a x : ℤ) : ℝ)) :=
        add_le_add hstep1 hcond
    _ = 3 * ∑ x ∈ N, cov (LatticeProb.iidLaw d ν) (meanF F) (fun a => ((a x : ℤ) : ℝ)) := by
        ring

/-- A product of two functionals of the data at the sites of `N` is one. -/
theorem DependsOn.mul {d : ℕ} {N : Finset (Site d)} {F Z : PData d → ℝ}
    (hF : DependsOn N F) (hZ : DependsOn N Z) : DependsOn N (fun ω => F ω * Z ω) := by
  intro ω ω' h1 h2 h3
  show F ω * Z ω = F ω' * Z ω'
  rw [hF ω ω' h1 h2 h3, hZ ω ω' h1 h2 h3]

/-- **Conditioning on the randomness away from the tilted sites changes no
covariance of two observables of those sites.** -/
theorem cov_restrictLaw {d : ℕ} {N : Finset (Site d)} {ν : Measure ℤ}
    [IsProbabilityMeasure ν] {ω₀ : PData d} {F Z : PData d → ℝ}
    (hFN : DependsOn N F) (hZN : DependsOn N Z) (hFm : Measurable F) (hZm : Measurable Z) :
    cov (restrictLaw d N ν ω₀) F Z = cov (pDataLaw d ν) F Z := by
  unfold cov
  rw [integral_restrictLaw (hFN.mul hZN) (hFm.mul hZm), integral_restrictLaw hFN hFm,
    integral_restrictLaw hZN hZm]

/-- **`lem:product` under the conditioned law.**  The covariance of the two
observables under the law in which only the tilted sites are random is at most
three times the sum of the covariances of `F` with the counts there. -/
theorem abs_cov_restrictLaw_le {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hd : 1 ≤ d) {N : Finset (Site d)} {ω₀ : PData d} {F Z : PData d → ℝ}
    (hFN : DependsOn N F) (hFsym : SymmetricInParticles F) (hFP : ReadsParticles F)
    (hZN : DependsOn N Z) (hZsym : SymmetricInParticles Z) (hZP : ReadsParticles Z)
    (hFm : Measurable F) (hZm : Measurable Z)
    (hF01 : ∀ ω, F ω ∈ Set.Icc (0 : ℝ) 1)
    (hFmono : ∀ (x₀ : Site d) (ω : PData d), F ω ≤ F (addAt x₀ ω))
    (hZanti : ∀ (x₀ : Site d) (ω : PData d), Z (addAt x₀ ω) ≤ Z ω)
    (hZlipadd : ∀ (x₀ : Site d) (ω : PData d), |Z (addAt x₀ ω) - Z ω| ≤ 1)
    (hZlipdel : ∀ (x₀ : Site d) (ω : PData d), |Z (delAt x₀ ω) - Z ω| ≤ 1)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k, (k : ℝ) ∂ν ≤ 0)
    (hZI : Integrable Z (restrictLaw d N ν ω₀)) :
    Integrable (fun ω => F ω * Z ω) (restrictLaw d N ν ω₀) ∧
      |cov (restrictLaw d N ν ω₀) F Z|
        ≤ 3 * ∑ x ∈ N, cov (pDataLaw d ν) F (fun ω => ((ω.1 x : ℤ) : ℝ)) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI := noiseLaw_isProbability hd
  haveI : IsProbabilityMeasure (pDataLaw d ν) := by rw [pDataLaw_eq_prod]; infer_instance
  have hFb : ∀ ω : PData d, ‖F ω‖ ≤ 1 := by
    intro ω
    have h := hF01 ω
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [h.1], h.2⟩
  have hZI' : Integrable Z (pDataLaw d ν) :=
    (integrable_restrictLaw_iff hZN hZm).mp hZI
  have hFZI : Integrable (fun ω => F ω * Z ω) (pDataLaw d ν) :=
    hZI'.bdd_mul hFm.aestronglyMeasurable (Filter.Eventually.of_forall hFb)
  refine ⟨(integrable_restrictLaw_iff (hFN.mul hZN) (hFm.mul hZm)).mpr hFZI, ?_⟩
  rw [cov_restrictLaw hFN hZN hFm hZm]
  exact abs_cov_pData_le hd hFN hFsym hFP hZN hZsym hZP hFm hZm hF01 hFmono hZanti
    hZlipadd hZlipdel hint hmean hZI' hFZI

end Parking

end
