/-
One step of the particle filtration of Step 2.

Step 2 of `lem:product` (`parking.tex:2367-2394`) reveals the particles of the
tilted sites one at a time and compares the observable at each step with its
value after that particle is deleted.  This module puts the two comparisons of
`Support/SpliceAvg.lean` on the filtration of `Support/ParticleFiltration.lean`
with the deleted-particle functionals of `Support/DeleteCompare.lean`:

- the deleted-particle functional lies above `Z` and within one of it, so the
  increment of `Z` across a step is at most one;
- it lies below `F`, so the mean absolute increment of `F` across the step that
  reveals the particle labelled `i` at `x` is at most twice the difference
  between the mean of `F` and its mean after that particle is deleted.

Summing over the particles present weights each site by its count, which is the
line `|Cov(F,Z | Y = k)| ≤ 2k (f(k) - f(k-1))` of the paper.
-/
import Parking.Support.PrefixLabel
import Parking.Support.DeleteCompare
import Parking.Support.SpliceAvg
import Parking.Support.Cov

open MeasureTheory

noncomputable section

namespace Parking

/-- The noise of the particle-driven construction is a probability measure. -/
theorem noiseLaw_isProbability {d : ℕ} (hd : 1 ≤ d) : IsProbabilityMeasure (noiseLaw d) := by
  haveI : IsProbabilityMeasure (stepLaw d) := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    LatticeProb.uniformUnit_isProbability
  haveI : IsProbabilityMeasure (moveLaw d) := by unfold moveLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  unfold noiseLaw
  infer_instance

/-- Deleting a particle at a site is measurable. -/
theorem measurable_delAt {d : ℕ} (x : Site d) : Measurable (fun ω : PData d => delAt x ω) := by
  unfold delAt
  refine Measurable.prodMk ?_ measurable_snd
  refine measurable_pi_lambda _ fun y => ?_
  show Measurable fun ω : PData d => if y = x then ω.1 y - 1 else ω.1 y
  by_cases hy : y = x
  · have he : (fun ω : PData d => if y = x then ω.1 y - 1 else ω.1 y)
        = fun ω : PData d => ω.1 y - 1 := by simp [hy]
    rw [he]
    exact Measurable.sub (measurable_fst.eval) measurable_const
  · have he : (fun ω : PData d => if y = x then ω.1 y - 1 else ω.1 y)
        = fun ω : PData d => ω.1 y := by simp [hy]
    rw [he]
    exact measurable_fst.eval

/-- The deleted-particle functional is measurable in the noise. -/
theorem measurable_deleted {d : ℕ} (hd : 1 ≤ d) {F : PData d → ℝ} (hFm : Measurable F)
    (a : Site d → ℤ) (x : Site d) (i : ℕ) :
    Measurable (fun b : PNoise d => deleted F a x i b) := by
  have h1 : Measurable (relabelNoise x (Equiv.swap i ((a x).toNat - 1))) :=
    (measurePreserving_relabelNoise hd x (Equiv.swap i ((a x).toNat - 1))).measurable
  have h2 : Measurable (fun c : PNoise d => ((a, c) : PData d)) :=
    measurable_const.prodMk measurable_id
  exact hFm.comp ((measurable_delAt x).comp (h2.comp h1))

/-- **The deletion does not lower an antitone functional.** -/
theorem le_deleted {d : ℕ} {Z : PData d → ℝ} (hZsym : SymmetricInParticles Z)
    (hZanti : ∀ (x₀ : Site d) (ω : PData d), Z (addAt x₀ ω) ≤ Z ω)
    (a : Site d → ℤ) (x : Site d) (i : ℕ) (hi : i < (a x).toNat) (b : PNoise d)
    (hb : Function.Injective b.2) :
    Z ((a, b) : PData d) ≤ deleted Z a x i b := by
  have hfix : ∀ j : ℕ, (a x).toNat ≤ j → (Equiv.swap i ((a x).toNat - 1)) j = j :=
    swap_apply_of_le hi (by omega)
  have h1 : Z ((a, relabelNoise x (Equiv.swap i ((a x).toNat - 1)) b) : PData d)
      = Z ((a, b) : PData d) := hZsym x (Equiv.swap i ((a x).toNat - 1)) (a, b) hb hfix
  calc Z ((a, b) : PData d)
      = Z ((a, relabelNoise x (Equiv.swap i ((a x).toNat - 1)) b) : PData d) := h1.symm
    _ = Z (addAt x (delAt x
          ((a, relabelNoise x (Equiv.swap i ((a x).toNat - 1)) b) : PData d))) := by
        rw [addAt_delAt]
    _ ≤ Z (delAt x ((a, relabelNoise x (Equiv.swap i ((a x).toNat - 1)) b) : PData d)) :=
        hZanti _ _
    _ = deleted Z a x i b := rfl

/-- **The deletion raises the functional by at most one.** -/
theorem deleted_sub_le_one {d : ℕ} {Z : PData d → ℝ} (hZsym : SymmetricInParticles Z)
    (hZlip : ∀ (x₀ : Site d) (ω : PData d), |Z (delAt x₀ ω) - Z ω| ≤ 1)
    (a : Site d → ℤ) (x : Site d) (i : ℕ) (hi : i < (a x).toNat) (b : PNoise d)
    (hb : Function.Injective b.2) :
    deleted Z a x i b - Z ((a, b) : PData d) ≤ 1 := by
  have hfix : ∀ j : ℕ, (a x).toNat ≤ j → (Equiv.swap i ((a x).toNat - 1)) j = j :=
    swap_apply_of_le hi (by omega)
  have h1 : Z ((a, relabelNoise x (Equiv.swap i ((a x).toNat - 1)) b) : PData d)
      = Z ((a, b) : PData d) := hZsym x (Equiv.swap i ((a x).toNat - 1)) (a, b) hb hfix
  have h2 := hZlip x ((a, relabelNoise x (Equiv.swap i ((a x).toNat - 1)) b) : PData d)
  have h3 : deleted Z a x i b
      = Z (delAt x ((a, relabelNoise x (Equiv.swap i ((a x).toNat - 1)) b) : PData d)) := rfl
  have h4 := (abs_le.mp h2).2
  linarith

/-- A comparison functional within one above the observable is integrable when the
observable is. -/
theorem integrable_of_le_add_one {d : ℕ} (hd : 1 ≤ d) {Z : PData d → ℝ} (a : Site d → ℤ)
    {W : PNoise d → ℝ}
    (hWm : Measurable W)
    (hZi : Integrable (fun b : PNoise d => Z ((a, b) : PData d)) (noiseLaw d))
    (hlow : ∀ b : PNoise d, Z ((a, b) : PData d) ≤ W b)
    (hup : ∀ b : PNoise d, W b - Z ((a, b) : PData d) ≤ 1) :
    Integrable W (noiseLaw d) := by
  haveI := noiseLaw_isProbability hd
  refine Integrable.mono' (hZi.abs.add (integrable_const (1 : ℝ)))
    hWm.aestronglyMeasurable (Filter.Eventually.of_forall fun b => ?_)
  have h1 := hlow b
  have h2 := hup b
  have h3 := le_abs_self (Z ((a, b) : PData d))
  have h4 := neg_abs_le (Z ((a, b) : PData d))
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> simp only [Pi.add_apply] <;> linarith

/-- The guarded comparison functional is measurable. -/
theorem measurable_deletedGuard {d : ℕ} (hd : 1 ≤ d) {F : PData d → ℝ} (hFm : Measurable F)
    (a : Site d → ℤ) (x : Site d) (i : ℕ) :
    Measurable (fun b : PNoise d => deletedGuard F a x i b) := by
  have h1 : Measurable (fun b : PNoise d => deleted F a x i b) :=
    measurable_deleted hd hFm a x i
  have h2 : Measurable (fun b : PNoise d => F ((a, b) : PData d)) :=
    hFm.comp (measurable_const.prodMk measurable_id)
  exact ((h1.sub h2).indicator (measurableSet_injective_noise d)).add h2

/-- **The guarded deletion does not lower an antitone functional.** -/
theorem le_deletedGuard {d : ℕ} {Z : PData d → ℝ} (hZsym : SymmetricInParticles Z)
    (hZanti : ∀ (x₀ : Site d) (ω : PData d), Z (addAt x₀ ω) ≤ Z ω)
    (a : Site d → ℤ) (x : Site d) (i : ℕ) (hi : i < (a x).toNat) (b : PNoise d) :
    Z ((a, b) : PData d) ≤ deletedGuard Z a x i b := by
  by_cases hb : Function.Injective b.2
  · rw [deletedGuard_of_injective Z a x i hb]
    exact le_deleted hZsym hZanti a x i hi b hb
  · rw [deletedGuard_of_not_injective Z a x i hb]

/-- **The guarded deletion raises the functional by at most one.** -/
theorem deletedGuard_sub_le_one {d : ℕ} {Z : PData d → ℝ} (hZsym : SymmetricInParticles Z)
    (hZlip : ∀ (x₀ : Site d) (ω : PData d), |Z (delAt x₀ ω) - Z ω| ≤ 1)
    (a : Site d → ℤ) (x : Site d) (i : ℕ) (hi : i < (a x).toNat) (b : PNoise d) :
    deletedGuard Z a x i b - Z ((a, b) : PData d) ≤ 1 := by
  by_cases hb : Function.Injective b.2
  · rw [deletedGuard_of_injective Z a x i hb]
    exact deleted_sub_le_one hZsym hZlip a x i hi b hb
  · rw [deletedGuard_of_not_injective Z a x i hb]
    simp

/-- The last stage of the filtration reveals every particle present. -/
theorem particleSplice_card {d : ℕ} (N : Finset (Site d)) (a : Site d → ℤ) (b η : PNoise d) :
    particleSplice N a (particleLabels N a).card b η
      = noiseComb ((particleLabels N a : Finset (Label d)) : Set (Label d)) b η := by
  unfold particleSplice
  rw [prefixSet_card]

/-- The first stage of the filtration reveals nothing. -/
theorem spInt_particleSplice_zero {d : ℕ} (N : Finset (Site d)) (a : Site d → ℤ)
    (G : PNoise d → ℝ) (ω : PNoise d) :
    spInt (noiseLaw d) (particleSplice N a 0) G ω = ∫ η, G η ∂(noiseLaw d) :=
  spInt_of_snd (particleSplice_zero N a) G ω

/-- The last stage of the filtration changes nothing. -/
theorem spInt_particleSplice_last {d : ℕ} (hd : 1 ≤ d) {N : Finset (Site d)}
    {G : PData d → ℝ} (hGN : DependsOn N G) (hGP : ReadsParticles G) (a : Site d → ℤ) :
    ∀ᵐ ω ∂(noiseLaw d), spInt (noiseLaw d) (particleSplice N a (particleLabels N a).card)
        (fun b => G ((a, b) : PData d)) ω = G ((a, ω) : PData d) := by
  haveI := noiseLaw_isProbability hd
  have hsplice : ∀ᵐ q ∂((noiseLaw d).prod (noiseLaw d)),
      Function.Injective
        (noiseComb {p : Label d | p.1 ∈ N → p.2 < (a p.1).toNat} q.1 q.2).2 :=
    (measurePreserving_noiseComb hd
      {p : Label d | p.1 ∈ N → p.2 < (a p.1).toNat}).quasiMeasurePreserving.ae
      (noiseLaw_ae_injective hd)
  filter_upwards [noiseLaw_ae_injective hd, Measure.ae_ae_of_ae_prod hsplice] with ω hω hηae
  unfold spInt
  have h : ∀ᵐ η ∂(noiseLaw d),
      G ((a, particleSplice N a (particleLabels N a).card ω η) : PData d)
        = G ((a, ω) : PData d) := by
    filter_upwards [hηae] with η hη
    rw [particleSplice_card]
    exact endpoint_particleSplice hGN hGP a ω η hω hη
  rw [integral_congr_ae h]
  simp

/-- **The comparison functional of a step does not see the label the step
reveals.** -/
theorem deleted_particleSplice_agree {d : ℕ} {G : PData d → ℝ} (hGP : ReadsParticles G)
    (N : Finset (Site d)) (a : Site d → ℤ) {i : ℕ} (hi : i < (particleLabels N a).card)
    (ω η : PNoise d) (h1 : Function.Injective (particleSplice N a (i + 1) ω η).2)
    (h2 : Function.Injective (particleSplice N a i ω η).2) :
    deleted G a (enumLabel (particleLabels N a) i).1 (enumLabel (particleLabels N a) i).2
        (particleSplice N a (i + 1) ω η)
      = deleted G a (enumLabel (particleLabels N a) i).1 (enumLabel (particleLabels N a) i).2
        (particleSplice N a i ω η) := by
  refine deleted_congr hGP a _ _ _ _ h1 h2 ?_ ?_
  · intro q hq
    exact (particleSplice_succ_agree N a hi ω η hq).1
  · intro q hq
    exact (particleSplice_succ_agree N a hi ω η hq).2

/-- **The guarded comparison functional of a step does not see the label the step
reveals**, at almost every pair of realizations: almost surely both stages of the
splicing have pairwise distinct uniform variables, and there the guard is off. -/
theorem deletedGuard_particleSplice_agree_ae {d : ℕ} (hd : 1 ≤ d) {G : PData d → ℝ}
    (hGP : ReadsParticles G) (N : Finset (Site d)) (a : Site d → ℤ) {i : ℕ}
    (hi : i < (particleLabels N a).card) :
    ∀ᵐ q ∂((noiseLaw d).prod (noiseLaw d)),
      deletedGuard G a (enumLabel (particleLabels N a) i).1
          (enumLabel (particleLabels N a) i).2 (particleSplice N a (i + 1) q.1 q.2)
        = deletedGuard G a (enumLabel (particleLabels N a) i).1
          (enumLabel (particleLabels N a) i).2 (particleSplice N a i q.1 q.2) := by
  have hT : ∀ᵐ q ∂((noiseLaw d).prod (noiseLaw d)),
      Function.Injective (particleSplice N a (i + 1) q.1 q.2).2 :=
    (measurePreserving_particleSplice hd N a (i + 1)).quasiMeasurePreserving.ae
      (noiseLaw_ae_injective hd)
  have hS : ∀ᵐ q ∂((noiseLaw d).prod (noiseLaw d)),
      Function.Injective (particleSplice N a i q.1 q.2).2 :=
    (measurePreserving_particleSplice hd N a i).quasiMeasurePreserving.ae
      (noiseLaw_ae_injective hd)
  filter_upwards [hT, hS] with q h1 h2
  rw [deletedGuard_of_injective G a _ _ h1, deletedGuard_of_injective G a _ _ h2]
  exact deleted_particleSplice_agree hGP N a hi q.1 q.2 h1 h2

/-- **The increment of `Z` across one step is at most one.**  The comparison is
the value after the particle the step reveals is deleted. -/
theorem abs_spInt_particle_Z_le_one {d : ℕ} (hd : 1 ≤ d) {N : Finset (Site d)}
    {Z : PData d → ℝ} (hZsym : SymmetricInParticles Z) (hZP : ReadsParticles Z)
    (hZm : Measurable Z)
    (hZanti : ∀ (x₀ : Site d) (ω : PData d), Z (addAt x₀ ω) ≤ Z ω)
    (hZlip : ∀ (x₀ : Site d) (ω : PData d), |Z (delAt x₀ ω) - Z ω| ≤ 1)
    (a : Site d → ℤ) {i : ℕ} (hi : i < (particleLabels N a).card)
    (hZi : Integrable (fun b : PNoise d => Z ((a, b) : PData d)) (noiseLaw d)) :
    ∀ᵐ ω ∂(noiseLaw d),
      |spInt (noiseLaw d) (particleSplice N a (i + 1)) (fun b => Z ((a, b) : PData d)) ω
        - spInt (noiseLaw d) (particleSplice N a i) (fun b => Z ((a, b) : PData d)) ω|
        ≤ 1 := by
  haveI := noiseLaw_isProbability hd
  set p : Label d := enumLabel (particleLabels N a) i with hp
  have hmem : p ∈ particleLabels N a := enumLabel_mem _ hi
  have hp2 : p.2 < (a p.1).toNat := (mem_particleLabels.mp hmem).2
  have hWm : Measurable (fun b : PNoise d => deletedGuard Z a p.1 p.2 b) :=
    measurable_deletedGuard hd hZm a p.1 p.2
  have hlow : ∀ b : PNoise d, Z ((a, b) : PData d) ≤ deletedGuard Z a p.1 p.2 b :=
    fun b => le_deletedGuard hZsym hZanti a p.1 p.2 hp2 b
  have hup : ∀ b : PNoise d, deletedGuard Z a p.1 p.2 b - Z ((a, b) : PData d) ≤ 1 :=
    fun b => deletedGuard_sub_le_one hZsym hZlip a p.1 p.2 hp2 b
  have hWi := integrable_of_le_add_one hd a hWm hZi hlow hup
  exact abs_spInt_sub_le_one_ae (measurePreserving_particleSplice hd N a i)
    (measurePreserving_particleSplice hd N a (i + 1))
    (deletedGuard_particleSplice_agree_ae hd hZP N a hi)
    (fun b => by linarith [hlow b]) (fun b => hup b) hZi hWi

/-- **The mean absolute increment of `F` across one step** is at most twice the
drop in the mean of `F` when the particle the step reveals is deleted. -/
theorem integral_abs_spInt_particle_F_le {d : ℕ} (hd : 1 ≤ d) {N : Finset (Site d)}
    {F : PData d → ℝ} (hFsym : SymmetricInParticles F) (hFP : ReadsParticles F)
    (hFm : Measurable F) (hF01 : ∀ ω, F ω ∈ Set.Icc (0 : ℝ) 1)
    (hFmono : ∀ (x₀ : Site d) (ω : PData d), F ω ≤ F (addAt x₀ ω))
    (a : Site d → ℤ) {i : ℕ} (hi : i < (particleLabels N a).card) :
    ∫ ω, |spInt (noiseLaw d) (particleSplice N a (i + 1)) (fun b => F ((a, b) : PData d)) ω
        - spInt (noiseLaw d) (particleSplice N a i) (fun b => F ((a, b) : PData d)) ω|
        ∂(noiseLaw d)
      ≤ 2 * ((∫ b, F ((a, b) : PData d) ∂(noiseLaw d))
              - ∫ b, F (delAt (enumLabel (particleLabels N a) i).1 ((a, b) : PData d))
                  ∂(noiseLaw d)) := by
  haveI := noiseLaw_isProbability hd
  set p : Label d := enumLabel (particleLabels N a) i with hp
  have hmem : p ∈ particleLabels N a := enumLabel_mem _ hi
  have hp2 : p.2 < (a p.1).toNat := (mem_particleLabels.mp hmem).2
  have hFm' : Measurable (fun b : PNoise d => F ((a, b) : PData d)) :=
    hFm.comp (measurable_const.prodMk measurable_id)
  have hVm : Measurable (fun b : PNoise d => deletedGuard F a p.1 p.2 b) :=
    measurable_deletedGuard hd hFm a p.1 p.2
  have hFb : ∀ b : PNoise d, |F ((a, b) : PData d)| ≤ 1 := by
    intro b
    have h := hF01 ((a, b) : PData d)
    rw [abs_le]
    exact ⟨by linarith [h.1], h.2⟩
  have hVb : ∀ b : PNoise d, |deletedGuard F a p.1 p.2 b| ≤ 1 := by
    intro b
    by_cases hb : Function.Injective b.2
    · rw [deletedGuard_of_injective F a p.1 p.2 hb]
      have h3 : deleted F a p.1 p.2 b
          = F (delAt p.1
            ((a, relabelNoise p.1 (Equiv.swap p.2 ((a p.1).toNat - 1)) b) : PData d)) := rfl
      have h := hF01 (delAt p.1
        ((a, relabelNoise p.1 (Equiv.swap p.2 ((a p.1).toNat - 1)) b) : PData d))
      rw [h3, abs_le]
      exact ⟨by linarith [h.1], h.2⟩
    · rw [deletedGuard_of_not_injective F a p.1 p.2 hb]
      exact hFb b
  have hFV : ∀ b : PNoise d, 0 ≤ F ((a, b) : PData d) - deletedGuard F a p.1 p.2 b := by
    intro b
    have := deletedGuard_le hFsym hFmono a p.1 p.2 hp2 b
    linarith
  have hmain := integral_abs_spInt_sub_le_of_bdd
    (measurePreserving_particleSplice hd N a i)
    (measurePreserving_particleSplice hd N a (i + 1))
    hFm' hVm hFb hVb (deletedGuard_particleSplice_agree_ae hd hFP N a hi) hFV
  have hFi : Integrable (fun b : PNoise d => F ((a, b) : PData d)) (noiseLaw d) :=
    (integrable_const (1 : ℝ)).mono' hFm'.aestronglyMeasurable
      (Filter.Eventually.of_forall fun b => by simpa [Real.norm_eq_abs] using hFb b)
  have hVi : Integrable (fun b : PNoise d => deletedGuard F a p.1 p.2 b) (noiseLaw d) :=
    (integrable_const (1 : ℝ)).mono' hVm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun b => by simpa [Real.norm_eq_abs] using hVb b)
  rw [integral_sub hFi hVi, integral_deletedGuard hd hFm a p.1 p.2] at hmain
  exact hmain

/-- **Step 2 of `lem:product`, for the particles of finitely many sites.**  With
the counts held at `a`, the covariance of two observables of the particles
present is at most twice the sum, over the sites, of the count there times the
drop in the mean of `F` when one particle is deleted there.  This is the paper's
`|Cov(F, Z | Y = k)| ≤ 2k (f(k) - f(k-1))` at `parking.tex:2383`, summed over the
tilted sites. -/
theorem abs_cov_noise_le {d : ℕ} (hd : 1 ≤ d) {N : Finset (Site d)} {F Z : PData d → ℝ}
    (hFN : DependsOn N F) (hFsym : SymmetricInParticles F) (hFP : ReadsParticles F)
    (hZN : DependsOn N Z) (hZsym : SymmetricInParticles Z) (hZP : ReadsParticles Z)
    (hFm : Measurable F) (hZm : Measurable Z)
    (hF01 : ∀ ω, F ω ∈ Set.Icc (0 : ℝ) 1)
    (hFmono : ∀ (x₀ : Site d) (ω : PData d), F ω ≤ F (addAt x₀ ω))
    (hZanti : ∀ (x₀ : Site d) (ω : PData d), Z (addAt x₀ ω) ≤ Z ω)
    (hZlip : ∀ (x₀ : Site d) (ω : PData d), |Z (delAt x₀ ω) - Z ω| ≤ 1)
    (a : Site d → ℤ)
    (hZi : Integrable (fun b : PNoise d => Z ((a, b) : PData d)) (noiseLaw d)) :
    |cov (noiseLaw d) (fun b => F ((a, b) : PData d)) (fun b => Z ((a, b) : PData d))|
      ≤ ∑ x ∈ N, ((a x).toNat : ℝ) *
          (2 * ((∫ b, F ((a, b) : PData d) ∂(noiseLaw d))
                - ∫ b, F (delAt x ((a, b) : PData d)) ∂(noiseLaw d))) := by
  haveI := noiseLaw_isProbability hd
  have hFm' : Measurable (fun b : PNoise d => F ((a, b) : PData d)) :=
    hFm.comp (measurable_const.prodMk measurable_id)
  have hFb : ∀ b : PNoise d, |F ((a, b) : PData d)| ≤ 1 := by
    intro b
    have h := hF01 ((a, b) : PData d)
    rw [abs_le]
    exact ⟨by linarith [h.1], h.2⟩
  have key := abs_cov_le_sum_abs_spInt (P := noiseLaw d)
    (fun i => particleSplice N a i) (particleLabels N a).card
    (fun i => measurePreserving_particleSplice hd N a i)
    (fun i => particleSplice_idem N a i)
    (fun i => particleSplice_step N a i)
    (spInt_particleSplice_zero N a (fun b => F ((a, b) : PData d)))
    (spInt_particleSplice_zero N a (fun b => Z ((a, b) : PData d)))
    (spInt_particleSplice_last hd hFN hFP a)
    (spInt_particleSplice_last hd hZN hZP a)
    hFm' hFb hZi
    (fun i hi => abs_spInt_particle_Z_le_one hd hZsym hZP hZm hZanti hZlip a hi hZi)
  have hstep2 : ∑ i ∈ Finset.range (particleLabels N a).card,
      ∫ ω, |spInt (noiseLaw d) (particleSplice N a (i + 1))
            (fun b => F ((a, b) : PData d)) ω
          - spInt (noiseLaw d) (particleSplice N a i)
            (fun b => F ((a, b) : PData d)) ω| ∂(noiseLaw d)
      ≤ ∑ i ∈ Finset.range (particleLabels N a).card,
          2 * ((∫ b, F ((a, b) : PData d) ∂(noiseLaw d))
            - ∫ b, F (delAt (enumLabel (particleLabels N a) i).1 ((a, b) : PData d))
                ∂(noiseLaw d)) :=
    Finset.sum_le_sum fun i hi =>
      integral_abs_spInt_particle_F_le hd hFsym hFP hFm hF01 hFmono a (Finset.mem_range.mp hi)
  have hsum := sum_range_equivFin (particleLabels N a)
    (fun p : Label d => 2 * ((∫ b, F ((a, b) : PData d) ∂(noiseLaw d))
      - ∫ b, F (delAt p.1 ((a, b) : PData d)) ∂(noiseLaw d)))
    (enumLabel (particleLabels N a))
    (fun i hi => by unfold enumLabel; rw [dif_pos hi])
  have hsum2 := sum_particleLabels N a
    (fun x : Site d => 2 * ((∫ b, F ((a, b) : PData d) ∂(noiseLaw d))
      - ∫ b, F (delAt x ((a, b) : PData d)) ∂(noiseLaw d)))
  unfold cov
  calc |(∫ b, F ((a, b) : PData d) * Z ((a, b) : PData d) ∂(noiseLaw d))
        - (∫ b, F ((a, b) : PData d) ∂(noiseLaw d))
          * ∫ b, Z ((a, b) : PData d) ∂(noiseLaw d)|
      ≤ ∑ i ∈ Finset.range (particleLabels N a).card,
          ∫ ω, |spInt (noiseLaw d) (particleSplice N a (i + 1))
                (fun b => F ((a, b) : PData d)) ω
              - spInt (noiseLaw d) (particleSplice N a i)
                (fun b => F ((a, b) : PData d)) ω| ∂(noiseLaw d) := key
    _ ≤ ∑ i ∈ Finset.range (particleLabels N a).card,
          2 * ((∫ b, F ((a, b) : PData d) ∂(noiseLaw d))
            - ∫ b, F (delAt (enumLabel (particleLabels N a) i).1 ((a, b) : PData d))
                ∂(noiseLaw d)) := hstep2
    _ = ∑ p ∈ particleLabels N a,
          2 * ((∫ b, F ((a, b) : PData d) ∂(noiseLaw d))
            - ∫ b, F (delAt p.1 ((a, b) : PData d)) ∂(noiseLaw d)) := hsum
    _ = ∑ x ∈ N, ((a x).toNat : ℝ) *
          (2 * ((∫ b, F ((a, b) : PData d) ∂(noiseLaw d))
                - ∫ b, F (delAt x ((a, b) : PData d)) ∂(noiseLaw d))) := hsum2

end Parking

end
