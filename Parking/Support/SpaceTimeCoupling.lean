import Sandpile.Support.MainExplStability
import Sandpile.Support.MainExplBrownCutoff
import Sandpile.Support.MainExplAssemblyZ

/-!
# Space-time coupling of stopping values

The stability and cutoff estimates hold uniformly on compact intervals of positive
horizons. The coupling follows the four-error comparison in
`Sandpile.dlt4_scaling_of_version`.
-/

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open Sandpile Sandpile.Continuum
open scoped NNReal ENNReal

universe u v

namespace Parking.Support

/-- A common finite-family threshold controls the two-reward gap at every horizon in an
interval of positive times. -/
theorem stability_gap_of_two_rewards_uniform
    (hStab : Sandpile.External.ContinuumStoppingStability.{u}) (d : ℕ) (hd : 1 ≤ d)
    (ΩB : Type u) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    (hB : ∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB)
    (T₀ T₁ : ℝ) (hT₀ : 0 < T₀) (hT : T₀ ≤ T₁)
    (K : Set (Sandpile.Continuum.Space d)) (hK : IsCompact K)
    (N : ℕ) (G : Fin N → ℝ → Sandpile.Continuum.Space d → ℝ)
    (hGc : ∀ i, Continuous fun p : ℝ × Sandpile.Continuum.Space d => G i p.1 p.2)
    (M : ℝ) (hGM : ∀ (i : Fin N) (s : ℝ) (y : Sandpile.Continuum.Space d), |G i s y| ≤ M)
    (ε ηF ηH : ℝ) (hε : 0 < ε) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → 0 < R → ∀ T ∈ Set.Icc T₀ T₁, ∀ x ∈ K,
      ∀ (F H : ℝ → Sandpile.Continuum.Space d → ℝ) (i : Fin N),
        ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => H p.1 p.2)
          (Set.Icc 0 T ×ˢ Set.univ) →
        (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y : Sandpile.Continuum.Space d, |F s y - G i s y| ≤ ηF) →
        (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y : Sandpile.Continuum.Space d, |H s y - G i s y| ≤ ηH) →
        |Sandpile.stoppingSup ⌊R ^ 2 * T⌋₊ (fun j => ⌊R * x j⌋)
              (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
                F (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
                  (Sandpile.External.Lclt.scaledSite R (X k))) -
            Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -H s y) T|
          ≤ ε + ηF + ηH := by
  obtain ⟨R₀, hR₀pos, hR₀⟩ := Sandpile.stability_uniform_of_finite hStab d hd ΩB PB B hB
    T₀ T₁ hT₀ hT K hK N G hGc M hGM ε hε
  refine ⟨R₀, hR₀pos, ?_⟩
  intro R hR hRp T hTT x hx F H i hHc hF hH
  have hTp : 0 < T := lt_of_lt_of_le hT₀ hTT.1
  set n : ℕ := ⌊R ^ 2 * T⌋₊ with hn
  set z : Sandpile.Site d := fun j => ⌊R * x j⌋ with hz
  set f : ℕ → Sandpile.Site d → ℝ := fun k y =>
    F (((n : ℕ) - (k : ℝ)) / R ^ 2) (Sandpile.External.Lclt.scaledSite R y) with hf
  set g : ℕ → Sandpile.Site d → ℝ := fun k y =>
    G i (((n : ℕ) - (k : ℝ)) / R ^ 2) (Sandpile.External.Lclt.scaledSite R y) with hg
  have hw : |Sandpile.stoppingSup n z (fun k X => f k (X k)) -
      Sandpile.stoppingSup n z (fun k X => g k (X k))| ≤ ηF :=
    Sandpile.abs_stoppingSup_sub_le_of_reward hd n z _ _ ηF
      (Sandpile.bddAbove_walk_stopped_value hd z n f)
      (Sandpile.bddAbove_walk_stopped_value hd z n g)
      (fun τ ht hnn => Sandpile.integrable_stopped_value hd z n f ht hnn)
      (fun τ ht hnn => Sandpile.integrable_stopped_value hd z n g ht hnn)
      (Sandpile.reward_gap_of_uniform R T T hRp hTp.le le_rfl F (G i) ηF hF)
  have hbH : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y, |H s y| ≤ M + ηH := by
    intro s hs y
    have ha := abs_sub_le (H s y) (G i s y) 0
    simp only [sub_zero] at ha
    linarith [hH s hs y, hGM i s y]
  have hm : |Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -H s y) T -
      Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -G i s y) T| ≤ ηH := by
    refine Sandpile.Continuum.abs_brownianDiscount_sub_le_of_continuousOn (hB x)
      (fun s y => -H s y) (fun s y => -G i s y) T (M + ηH) M ηH hTp.le
      hHc.neg ((hGc i).continuousOn.neg) ?_ ?_ ?_
    · intro s hs y
      simpa only [abs_neg] using hbH s hs y
    · intro s _hs y
      simpa only [abs_neg] using hGM i s y
    · intro s hs y
      simpa only [neg_sub_neg, abs_sub_comm] using hH s hs y
  have hmid := hR₀ R hR i T hTT x hx
  have ha := abs_sub_le (Sandpile.stoppingSup n z (fun k X => f k (X k)))
    (Sandpile.stoppingSup n z (fun k X => g k (X k)))
    (Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -H s y) T)
  have hb := abs_sub_le (Sandpile.stoppingSup n z (fun k X => g k (X k)))
    (Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -G i s y) T)
    (Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -H s y) T)
  rw [abs_sub_comm] at hm
  change |Sandpile.stoppingSup n z (fun k X => f k (X k)) -
    Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -H s y) T| ≤ ε + ηF + ηH
  change |Sandpile.stoppingSup n z (fun k X => g k (X k)) -
    Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -G i s y) T| ≤ ε at hmid
  linarith

/-- The Brownian cutoff radius may be chosen uniformly for horizons below a fixed bound. -/
theorem exists_brownianDiscount_cutoff_gap_of_growth_uniform (d : ℕ) (p : ℕ) {K T₁ ε : ℝ}
    (hK : 0 ≤ K) (hT₁ : 0 < T₁) (hε : 0 < ε) :
    ∃ A₀ : ℝ, 4 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
      ∀ T ∈ Set.Icc (0 : ℝ) T₁, ∀ (x : Space d) (Ω : Type*) (_ : MeasurableSpace Ω) (P : Measure Ω),
        IsProbabilityMeasure P → ∀ B : ℝ≥0 → Ω → Space d, IsBrownian d x B P →
        ∀ ρ : ℝ, 0 ≤ ρ → ‖x‖ ≤ ρ → 2 * ρ ≤ A →
        ∀ h : ℝ → Space d → ℝ,
          (∀ s ∈ Set.Icc (0 : ℝ) T₁, ∀ y : Space d, |h s y| ≤ K * (1 + ‖y‖) ^ p) →
          BddAbove (stoppingPayoffs B P h T) →
          BddAbove (stoppingPayoffs B P (fun s y => cutoff A y * h s y) T) →
          (∀ τ : Ω → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
            Integrable (fun ω => -h (T - τ ω) (B (τ ω) ω)) P) →
          (∀ τ : Ω → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
            Integrable (fun ω => -(cutoff A (B (τ ω) ω) * h (T - τ ω) (B (τ ω) ω))) P) →
          (∀ τ : Ω → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
            Integrable
              (fun ω => (1 - cutoff A (B (τ ω) ω)) * |h (T - (τ ω : ℝ)) (B (τ ω) ω)|) P) →
          (∀ τ : Ω → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
            ∀ j : ℕ, MeasurableSet {ω | 2 ^ j * A ≤ ‖B (τ ω) ω‖}) →
          |brownianDiscount B P h T
              - brownianDiscount B P (fun s y => cutoff A y * h s y) T| ≤ ε := by
  obtain ⟨A₀, hA₀4, hA₀⟩ := exists_brownian_cutoff_error d p
    (K := K * 2 ^ p) (T := T₁) (ε := ε) (by positivity) hT₁ hε
  refine ⟨A₀, hA₀4, ?_⟩
  intro A hA T hTT x Ω mΩ P hP B hB ρ hρ hxρ hρA h hgrow hbdd hbdd' hf hχf hint hmeas
  have hA4 : (4 : ℝ) ≤ A := le_trans hA₀4 hA
  have hA0 : (0 : ℝ) < A := by linarith
  refine abs_brownianDiscount_sub_cutoffDiscount_le B P h T A ε hTT.1 hbdd hbdd' hf hχf ?_
  intro τ hτ hτT
  refine hA₀ A hA x Ω mΩ P hP B hB ρ hρ hxρ hρA τ (fun ω => le_trans (hτT ω) hTT.2)
    (fun ω => h (T - (τ ω : ℝ)) (B (τ ω) ω)) (hmeas τ hτ hτT) ?_ (hint τ hτ hτT)
  intro ω j hj
  have h2j : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ (by norm_num)
  have hz1 : (1 : ℝ) ≤ 2 ^ (j + 1) * A := by nlinarith
  have hmem : T - (τ ω : ℝ) ∈ Set.Icc (0 : ℝ) T :=
    ⟨by linarith [hτT ω], sub_le_self T (τ ω).coe_nonneg⟩
  have hb := hgrow _ ⟨hmem.1, le_trans hmem.2 hTT.2⟩ (B (τ ω) ω)
  have hlt : ‖B (τ ω) ω‖ < 2 ^ (j + 1) * A := hj.2
  have hstep : (1 + ‖B (τ ω) ω‖) ^ p ≤ (2 * (2 ^ (j + 1) * A)) ^ p := by
    refine pow_le_pow_left₀ (by positivity) ?_ p
    linarith
  have hpow : (2 * (2 ^ (j + 1) * A)) ^ p = 2 ^ p * (2 ^ (j + 1) * A) ^ p := mul_pow _ _ _
  calc |h (T - (τ ω : ℝ)) (B (τ ω) ω)| ≤ K * (1 + ‖B (τ ω) ω‖) ^ p := hb
    _ ≤ K * (2 * (2 ^ (j + 1) * A)) ^ p := mul_le_mul_of_nonneg_left hstep hK
    _ = K * 2 ^ p * (2 ^ (j + 1) * A) ^ p := by rw [hpow]; ring

/-- The rescaled odometer and the Brownian value can be coupled uniformly on a compact
interval of positive times and a compact set of spatial points. -/
theorem dlt4_scaling_of_version_uniform
    (hStab : Sandpile.External.ContinuumStoppingStability.{u})
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (ΩW : Type v) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ)
    (hW : Sandpile.Continuum.IsWhiteNoise d W PW)
    (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Sandpile.Continuum.Space d),
      Z t x =ᵐ[PW] fun ω =>
        Sandpile.Continuum.gaussianPotential d (variance id ν) W t x ω)
    (ΩB : Type u) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    (hB : ∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB)
    (hBc : ∀ (y : Sandpile.Continuum.Space d) (ω : ΩB), Continuous fun s => B y s ω)
    (hBm : ∀ (y : Sandpile.Continuum.Space d) (t : ℝ≥0), StronglyMeasurable (B y t))
    (K : Set (Sandpile.Continuum.Space d)) (hK : IsCompact K)
    (T₀ T : ℝ) (hT₀ : 0 < T₀) (hT₀T : T₀ ≤ T)
    (hZcont : ∀ᵐ ω ∂PW, ContinuousOn (fun q : ℝ × Sandpile.Continuum.Space d =>
        Z q.1 q.2 ω)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))))
    (hZgrow : ∀ᵐ ω ∂PW, ∃ C k : ℝ,
      ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
        |Z q.1 q.2 ω| ≤ C * (1 + ‖q.2‖) ^ k)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∃ P : Measure ((Sandpile.Site d → ℝ) × ΩW), IsProbabilityMeasure P ∧
        P.map Prod.fst = Sandpile.centeredMassLaw d ν ∧
        P.map Prod.snd = PW ∧
        P {p | ∃ S ∈ Set.Icc T₀ T, ∃ u ∈ K,
            ε < |R ^ (-(2 - (d : ℝ) / 2)) *
                  Sandpile.odometerOf (Sandpile.scenery d p.1) ⌊S * R ^ 2⌋₊
                    (fun i => ⌊R * u i⌋)
                - Sandpile.Continuum.brownianValue (B u) PB
                    (fun t y => Z t y p.2)
                    S u|}
          ≤ ENNReal.ofReal δ := by
  classical
  have hT : 0 < T := lt_of_lt_of_le hT₀ hT₀T
  have hBmM : ∀ (y : Space d) (t : ℝ≥0), Measurable (B y t) :=
    fun y t => (hBm y t).measurable
  obtain ⟨hfdd, htight⟩ := Sandpile.Frozen.heat_potential_invariance d (by omega) hd3
    ν hmean hvar hvar' θ₀ hθ₀ hexp PW W hW T hT
  obtain ⟨ρ, hρ, hKρ⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : Space d)
  have hKn : ∀ u ∈ K, ‖u‖ ≤ ρ := fun u hu => by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hKρ hu
  set η : ℝ := ε / 32 with hηdef
  have hη : 0 < η := by rw [hηdef]; positivity
  have hδ5 : 0 < δ / 5 := by positivity
  obtain ⟨Kw, hKw, hwenv⟩ := Sandpile.Support.exists_mesh_annulus_bound
    Sandpile.External.heatKernelBounds hd hd3 (θ := 1/2) (by norm_num) (by norm_num)
    ν hmean hθ₀ hexp T hT.le (δ / 5) hδ5
  have hmeasZ : ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)),
      AEMeasurable (Z q.1 q.2) PW := by
    intro q hq
    exact (measurable_const.mul (hW.meas _
      (Sandpile.Support.memLp_greenTimeBM hd hd3 hq.1.1 q.2))).aemeasurable.congr
      (hZmod q.1 q.2).symm
  obtain ⟨mz, Nz, hNzm, hNz, hzenv⟩ := Sandpile.Support.exists_deterministic_growth_of_version
    PW Z T hT.le hmeasZ hZcont hZgrow (δ / 5) hδ5
  obtain ⟨A₁, hA₁4, hA₁⟩ := Sandpile.exists_walk_cutoff_stoppingSup_gap d hd 1
    (K := Kw) (T := T) (ε := ε / 8) hKw hT (by positivity)
  obtain ⟨A₂, hA₂4, hA₂⟩ := exists_brownianDiscount_cutoff_gap_of_growth_uniform
    d mz (K := (mz : ℝ)) (T₁ := T) (ε := ε / 8) (Nat.cast_nonneg mz) hT (by positivity)
  set ρ' : ℝ := ρ + Real.sqrt d + 1 with hρ'def
  have hρ'0 : 0 ≤ ρ' := by rw [hρ'def]; positivity
  set A : ℝ := max (max A₁ A₂) (max (2 * ρ' + 1) (ρ' + 3 * Real.sqrt d + 4)) with hAdef
  have hAA₁ : A₁ ≤ A := le_trans (le_max_left _ _) (le_max_left _ _)
  have hAA₂ : A₂ ≤ A := le_trans (le_max_right _ _) (le_max_left _ _)
  have hA4 : (4 : ℝ) ≤ A := le_trans hA₁4 hAA₁
  have hA0 : (0 : ℝ) < A := by linarith
  have hAρ' : 2 * ρ' + 1 ≤ A := le_trans (le_max_left _ _) (le_max_right _ _)
  have hAbox : ρ' + 3 * Real.sqrt d + 4 ≤ A := le_trans (le_max_right _ _) (le_max_right _ _)
  set C : Set (ℝ × Space d) := rewardBox d T A with hCdef
  have hCc : IsCompact C := isCompact_rewardBox d T A
  have hCs : C ⊆ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)) :=
    fun _ h => ⟨h.1, Set.mem_univ _⟩
  obtain ⟨M₀, hM₀⟩ := (htight C hCc hCs).1 (δ / 5) hδ5
  set M : ℝ := max M₀ 0 with hMdef
  have hM : (0 : ℝ) ≤ M := le_max_right _ _
  obtain ⟨a, ha, hosc⟩ := (htight C hCc hCs).2 (δ / 5) η hδ5 hη
  obtain ⟨N, G, hGc, hGM, hnear⟩ := exists_cutoff_reward_family d A T hA0 M η a hM hη ha
  obtain ⟨Rs, hRs, hstab⟩ := stability_gap_of_two_rewards_uniform hStab d hd ΩB PB B hB T₀ T hT₀ hT₀T
    K hK N (fun i s y => -G i s y) (fun i => (hGc i).neg) (M + η)
    (fun i s y => by simpa only [abs_neg] using hGM i s y) (ε / 8) (2 * η) (3 * η)
    (by positivity)
  obtain ⟨Rm, hRm, hmesh⟩ := Sandpile.exists_parabolic_mesh_threshold d a ha
  obtain ⟨Rc, hRc, hcoup⟩ := Sandpile.Continuum.heat_field_coupling_of_version d hd hd3 ν
    ΩW PW W hW Z hZmod T hT hZcont hfdd htight C hCc hCs η (δ / 5) hη hδ5
  refine ⟨max (1 + 1 / T₀) (max Rs (max Rm Rc)),
    lt_of_lt_of_le (by positivity) (le_max_left _ _), ?_⟩
  intro R hR
  have hR1T : 1 + 1 / T₀ ≤ R := (le_max_left _ _).trans hR
  have hTinv : (0 : ℝ) < 1 / T₀ := by positivity
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hRp : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  have hrest : max Rs (max Rm Rc) ≤ R := (le_max_right _ _).trans hR
  have hRsm : Rs ≤ R := (le_max_left _ _).trans hrest
  have hRmm : Rm ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hrest)
  have hRcm : Rc ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans hrest)
  have hTR : (1 : ℝ) ≤ T₀ * R ^ 2 := by
    have h1 : 1 / T₀ ≤ R := by linarith
    have h2 : R ≤ R ^ 2 := by nlinarith
    have h3 : 1 / T₀ ≤ R ^ 2 := le_trans h1 h2
    rw [div_le_iff₀ hT₀] at h3
    nlinarith
  have hn1 : ∀ S ∈ Set.Icc T₀ T, 1 ≤ ⌊S * R ^ 2⌋₊ := by
    intro S hS
    apply Nat.le_floor
    have : (1 : ℝ) ≤ S * R ^ 2 :=
      hTR.trans (mul_le_mul_of_nonneg_right hS.1 (sq_nonneg R))
    exact_mod_cast this
  obtain ⟨P, hP, hPf, hPs, hPgap⟩ := hcoup R hRcm
  obtain ⟨Gw, hGwm, hGw⟩ := hwenv R hR1
  refine ⟨P, hP, hPf, hPs, ?_⟩
  set v : (Site d → ℝ) → ℝ → Space d → ℝ := fun σ s y =>
    Frozen.HeatPotentialInvariance.linInterp d R (scenery d σ) s y with hvdef
  set z : ΩW → ℝ → Space d → ℝ := fun ω s y => Z s y ω with hzdef
  set badM : Set (Site d → ℝ) := {σ | ∃ p ∈ C, M < |v σ p.1 p.2|} with hbadMdef
  set badO : Set (Site d → ℝ) := {σ | ∃ p ∈ C, ∃ q ∈ C,
    dist p q < a ∧ η < |v σ p.1 p.2 - v σ q.1 q.2|} with hbadOdef
  set badG : Set ((Site d → ℝ) × ΩW) := {p | ∃ q ∈ C,
    η < |v p.1 q.1 q.2 - z p.2 q.1 q.2|} with hbadGdef
  set badC : Set ΩW := {ω | ¬ ContinuousOn (fun q : ℝ × Space d => z ω q.1 q.2)
    (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)))} with hbadCdef
  have hbadM : centeredMassLaw d ν badM ≤ ENNReal.ofReal (δ / 5) := by
    apply le_trans (measure_mono ?_) (hM₀ R hR1)
    rintro σ ⟨q, hq, hv⟩
    exact ⟨q, hq, (le_max_left M₀ 0).trans_lt hv⟩
  have hbadO : centeredMassLaw d ν badO ≤ ENNReal.ofReal (δ / 5) := hosc R hR1
  have hbadC : PW badC = 0 := ae_iff.mp hZcont
  have hsub : {p : (Site d → ℝ) × ΩW | ∃ S ∈ Set.Icc T₀ T, ∃ u ∈ K,
      ε < |R ^ (-(2 - (d : ℝ) / 2)) *
            odometerOf (scenery d p.1) ⌊S * R ^ 2⌋₊ (fun i => ⌊R * u i⌋)
          - brownianValue (B u) PB (z p.2) S u|} ⊆
      (Prod.fst ⁻¹' ((badM ∪ badO) ∪ Gwᶜ)) ∪ badG ∪ (Prod.snd ⁻¹' (badC ∪ Nz)) := by
    intro p hp
    by_cases hm : p.1 ∈ badM ∪ badO
    · exact Or.inl (Or.inl (Or.inl hm))
    by_cases hw : p.1 ∈ Gwᶜ
    · exact Or.inl (Or.inl (Or.inr hw))
    by_cases hg : p ∈ badG
    · exact Or.inl (Or.inr hg)
    by_cases hc : p.2 ∈ badC
    · exact Or.inr (Or.inl hc)
    by_cases hzb : p.2 ∈ Nz
    · exact Or.inr (Or.inr hzb)
    exfalso
    have hvc : ContinuousOn (fun q : ℝ × Space d => z p.2 q.1 q.2)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d))) := of_not_not hc
    have hσG : p.1 ∈ Gw := of_not_not hw
    have hmb : ¬ ∃ q ∈ C, M < |v p.1 q.1 q.2| := fun h => hm (Or.inl h)
    have hob : ¬ ∃ q ∈ C, ∃ r ∈ C, dist q r < a ∧ η < |v p.1 q.1 q.2 - v p.1 r.1 r.2| :=
      fun h => hm (Or.inr h)
    obtain ⟨i, hi⟩ := hnear (v p.1) hmb hob
    obtain ⟨S, hS, u, hu, huerr⟩ := hp
    have hSp : 0 < S := lt_of_lt_of_le hT₀ hS.1
    have hvcS : ContinuousOn (fun q : ℝ × Space d => z p.2 q.1 q.2)
        (Set.Icc (0 : ℝ) S ×ˢ (Set.univ : Set (Space d))) :=
      hvc.mono (fun q hq => ⟨⟨hq.1.1, le_trans hq.1.2 hS.2⟩, hq.2⟩)
    have hRne : R ≠ 0 := ne_of_gt hRp
    set n : ℕ := ⌊R ^ 2 * S⌋₊ with hndef
    set yy : Sandpile.Site d := fun j => ⌊R * u j⌋ with hyydef
    have hnT : (n : ℝ) ≤ R ^ 2 * S := Nat.floor_le (by positivity)
    have hnTupper : (n : ℝ) ≤ R ^ 2 * T := hnT.trans (mul_le_mul_of_nonneg_left hS.2 (sq_nonneg R))
    have hnn : ⌊S * R ^ 2⌋₊ = n := by rw [hndef, mul_comm]
    have hun : ‖u‖ ≤ ρ := hKn u hu
    have hsd0 : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
    have hmesh0 : ‖Support.meshPoint R u - u‖ ≤ Real.sqrt d / R :=
      Support.norm_meshPoint_sub_le hRp u
    have hsd : Real.sqrt d / R ≤ Real.sqrt d := div_le_self hsd0 hR1
    have hmeshn : ‖Support.meshPoint R u‖ ≤ ρ + Real.sqrt d := by
      have h := norm_add_le (Support.meshPoint R u - u) u
      rw [sub_add_cancel] at h
      linarith
    have hρ'val : ρ' = ρ + Real.sqrt d + 1 := hρ'def
    have hρA : ρ ≤ A := by rw [hρ'val] at hAbox; linarith
    have hyρ' : ‖Sandpile.External.Lclt.scaledSite R yy‖ ≤ ρ' := by
      rw [hyydef, Support.scaledSite_floor_eq_meshPoint, hρ'val]
      linarith
    have hcu : (S, u) ∈ C := by
      refine ⟨⟨hSp.le, hS.2⟩, ?_⟩
      simp only [Metric.mem_closedBall, dist_zero_right]
      linarith
    have hqmem : (((n : ℝ) / R ^ 2, Support.meshPoint R u) : ℝ × Space d) ∈ C := by
      refine ⟨⟨div_nonneg (Nat.cast_nonneg n) (sq_nonneg R), ?_⟩, ?_⟩
      · apply (div_le_iff₀ (by positivity : (0:ℝ) < R ^ 2)).2
        rw [hndef]
        nlinarith [Nat.floor_le (show (0:ℝ) ≤ R ^ 2 * S by positivity), mul_le_mul_of_nonneg_left hS.2 (sq_nonneg R)]
      · simp only [Metric.mem_closedBall, dist_zero_right]
        rw [hρ'val] at hAbox
        linarith
    have hmo : |v p.1 ((n : ℝ) / R ^ 2) (Support.meshPoint R u) - v p.1 S u| ≤ η :=
      le_of_not_gt (fun h => hob ⟨((n : ℝ) / R ^ 2, Support.meshPoint R u), hqmem, (S, u), hcu,
        by rw [hndef]; exact hmesh R hRmm S hSp.le u, h⟩)
    have hcou : |v p.1 S u - z p.2 S u| ≤ η :=
      le_of_not_gt (fun h => hg ⟨(S, u), hcu, h⟩)
    have hqval : v p.1 ((n : ℝ) / R ^ 2) (Support.meshPoint R u)
        = Frozen.HeatPotentialInvariance.meshValue d R (scenery d p.1) n yy := by
      have h := Sandpile.linInterp_scaledSite R hRne (scenery d p.1) n 0 (Nat.zero_le n) yy
      simpa only [hvdef, hyydef, Nat.cast_zero, sub_zero, Nat.sub_zero,
        Support.scaledSite_floor_eq_meshPoint] using h
    have hfield : |Frozen.HeatPotentialInvariance.meshValue d R (scenery d p.1) n yy
        - z p.2 S u| ≤ 2 * η := by
      rw [← hqval]
      have ht := abs_sub_le (v p.1 ((n : ℝ) / R ^ 2) (Support.meshPoint R u)) (v p.1 S u)
        (z p.2 S u)
      linarith
    have hA1 : (1 : ℝ) ≤ A := by linarith
    set f : ℕ → Sandpile.Site d → ℝ := fun k w =>
      -(Frozen.HeatPotentialInvariance.meshValue d R (scenery d p.1) (n - k) w) with hfdef
    set g : ℕ → Sandpile.Site d → ℝ := fun k w =>
      cutoff A (Sandpile.External.Lclt.scaledSite R w) * f k w with hgdef
    have hE₁ : |stoppingSup n yy (fun k X => f k (X k)) -
        stoppingSup n yy (fun k X =>
          cutoff A (Sandpile.External.Lclt.scaledSite R (X k)) * f k (X k))| ≤ ε / 8 := by
      refine hA₁ A hAA₁ R hR1 yy ρ' hρ'0 hyρ' (by linarith) n (hnn ▸ hn1 S hS) hnTupper
        (fun k X => f k (X k)) (fun τ hτ hτn => Sandpile.measurable_stopped_value n f hτ hτn)
        ?_ (Sandpile.bddAbove_walk_stopped_value hd yy n f)
        (Sandpile.bddAbove_walk_stopped_value hd yy n g)
        (fun τ hτ hτn => Sandpile.integrable_stopped_value hd yy n f hτ hτn)
        (fun τ hτ hτn => Sandpile.integrable_stopped_value hd yy n g hτ hτn)
      intro τ hτn X j hj
      exact hGw p.1 hσG A hA1 n hnTupper τ hτn X j hj
    have hcutgap : ∀ s ∈ Set.Icc (0 : ℝ) S, ∀ w : Space d,
        |cutoff A w * z p.2 s w - cutoff A w * v p.1 s w| ≤ η := by
      intro s hs w
      by_cases hy : 2 * A ≤ ‖w‖
      · rw [cutoff_eq_zero_of_norm_ge A hA0 w hy]
        simpa only [zero_mul, sub_self, abs_zero] using hη.le
      have hwC : (s, w) ∈ C := ⟨⟨hs.1, le_trans hs.2 hS.2⟩, by
        simpa only [Metric.mem_closedBall, dist_zero_right] using (le_of_not_ge hy)⟩
      have he : |v p.1 s w - z p.2 s w| ≤ η := le_of_not_gt (fun h => hg ⟨(s, w), hwC, h⟩)
      rw [← mul_sub, abs_mul, abs_of_nonneg (cutoff_nonneg A w), abs_sub_comm]
      exact (mul_le_of_le_one_left (abs_nonneg _) (cutoff_le_one A w)).trans he
    have hE₂ := hstab R hRsm hRp S hS u hu
      (fun s w => -(cutoff A w * v p.1 s w)) (fun s w => -(cutoff A w * z p.2 s w)) i
      ((((continuous_cutoff A).comp continuous_snd).continuousOn.mul hvcS).neg)
      (fun s hs w => by
        have h := hi s ⟨hs.1, le_trans hs.2 hS.2⟩ w
        have hrw : -(cutoff A w * v p.1 s w) - -G i s w
            = -(cutoff A w * v p.1 s w - G i s w) := by ring
        rw [hrw, abs_neg]; exact h)
      (fun s hs w => by
        have h1 := hcutgap s hs w
        have h2 := hi s ⟨hs.1, le_trans hs.2 hS.2⟩ w
        have ht := abs_sub_le (cutoff A w * z p.2 s w) (cutoff A w * v p.1 s w) (G i s w)
        have hrw : -(cutoff A w * z p.2 s w) - -G i s w
            = -(cutoff A w * z p.2 s w - G i s w) := by ring
        rw [hrw, abs_neg]; linarith)
    have hwalkeq : stoppingSup n yy (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
        -(cutoff A (Sandpile.External.Lclt.scaledSite R (X k)) *
          v p.1 (((n : ℕ) - (k : ℝ)) / R ^ 2)
            (Sandpile.External.Lclt.scaledSite R (X k))))
        = stoppingSup n yy (fun k X =>
          cutoff A (Sandpile.External.Lclt.scaledSite R (X k)) * f k (X k)) := by
      refine Sandpile.stoppingSup_congr_of_le n yy _ _ ?_
      intro k hk X
      simpa only [hvdef, hfdef] using
        Sandpile.cutoff_linInterp_scaledSite R hRne (scenery d p.1) A n k hk (X k)
    have hgrowz := hzenv p.2 hzb
    have hcz : ContinuousOn (fun q : ℝ × Space d => z p.2 q.1 q.2)
        (Set.Icc 0 S ×ˢ (Set.univ : Set (Space d))) := hvcS
    have hcχ : ContinuousOn (fun q : ℝ × Space d => cutoff A q.2 * z p.2 q.1 q.2)
        (Set.Icc 0 S ×ˢ (Set.univ : Set (Space d))) :=
      ((continuous_cutoff A).comp continuous_snd).continuousOn.mul hvcS
    have hgrowu : ∀ vv : ℝ≥0, vv ≤ S.toNNReal → ∀ w : Space d,
        ‖z p.2 (vv : ℝ) w‖ ≤ ((mz : ℝ) * (1 + ρ) ^ mz) * (1 + ‖w - u‖) ^ mz := by
      intro vv hvv w
      have hvvT : (vv : ℝ) ≤ S := by
        have := NNReal.coe_le_coe.2 hvv
        rwa [Real.coe_toNNReal S hSp.le] at this
      have h1 := hgrowz (vv : ℝ) ⟨vv.coe_nonneg, le_trans hvvT hS.2⟩ w
      have h2 : ‖w‖ ≤ ‖w - u‖ + ρ := by
        have h := norm_add_le (w - u) u
        rw [sub_add_cancel] at h
        linarith
      have h3 : (1 + ‖w‖) ≤ (1 + ρ) * (1 + ‖w - u‖) := by
        nlinarith only [h2, mul_nonneg hρ.le (norm_nonneg (w - u))]
      have h4 : (1 + ‖w‖) ^ mz ≤ ((1 + ρ) * (1 + ‖w - u‖)) ^ mz :=
        pow_le_pow_left₀ (by positivity) h3 mz
      rw [Real.norm_eq_abs]
      calc |z p.2 (vv : ℝ) w| ≤ (mz : ℝ) * (1 + ‖w‖) ^ mz := h1
        _ ≤ (mz : ℝ) * ((1 + ρ) * (1 + ‖w - u‖)) ^ mz :=
            mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg mz)
        _ = ((mz : ℝ) * (1 + ρ) ^ mz) * (1 + ‖w - u‖) ^ mz := by rw [mul_pow]; ring
    have hgrowuχ : ∀ vv : ℝ≥0, vv ≤ S.toNNReal → ∀ w : Space d,
        ‖cutoff A w * z p.2 (vv : ℝ) w‖ ≤ ((mz : ℝ) * (1 + ρ) ^ mz) * (1 + ‖w - u‖) ^ mz := by
      intro vv hvv w
      have h := hgrowu vv hvv w
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cutoff_nonneg A w)] at *
      calc
        cutoff A w * |z p.2 (vv : ℝ) w| ≤ |z p.2 (vv : ℝ) w| := by
          simpa using mul_le_mul_of_nonneg_right (cutoff_le_one A w)
            (abs_nonneg (z p.2 (vv : ℝ) w))
        _ ≤ _ := h
    obtain ⟨Denv, hDenv, hDdom⟩ := Sandpile.Support.exists_brownian_envelope_of_polynomial_growth
      (hB u) (hBmM u) (hBc u) (z p.2) S.toNNReal ((mz : ℝ) * (1 + ρ) ^ mz) (by positivity) mz
      hgrowu
    have hdom : ∀ᵐ ω' ∂PB, ∀ r : ℝ≥0, (r : ℝ) ≤ S →
        ‖z p.2 (S - (r : ℝ)) (B u r ω')‖ ≤ Denv ω' := by
      refine Filter.Eventually.of_forall fun ω' r hr => ?_
      have hrT : r ≤ S.toNNReal := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal S hSp.le]; exact hr
      have hsub : ((S.toNNReal - r : ℝ≥0) : ℝ) = S - (r : ℝ) := by
        rw [NNReal.coe_sub hrT, Real.coe_toNNReal S hSp.le]
      have h := hDdom ω' (S.toNNReal - r) tsub_le_self r hrT
      rwa [hsub] at h
    have hdomχ : ∀ᵐ ω' ∂PB, ∀ r : ℝ≥0, (r : ℝ) ≤ S →
        ‖cutoff A (B u r ω') * z p.2 (S - (r : ℝ)) (B u r ω')‖ ≤ Denv ω' := by
      filter_upwards [hdom] with ω' hω' r hr
      have h := hω' r hr
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cutoff_nonneg A _)]
      rw [Real.norm_eq_abs] at h
      exact (mul_le_of_le_one_left (abs_nonneg _) (cutoff_le_one A _)).trans h
    have hint1 := Sandpile.Continuum.integrable_stopped_reward_of_envelope (B u) PB (z p.2) S
      hcz (fun t => (hBmM u t).aemeasurable) (Filter.Eventually.of_forall (hBc u)) Denv hDenv hdom
    have hint2 := Sandpile.Continuum.integrable_stopped_reward_of_envelope (B u) PB
      (fun s w => cutoff A w * z p.2 s w) S hcχ (fun t => (hBmM u t).aemeasurable)
      (Filter.Eventually.of_forall (hBc u)) Denv hDenv hdomχ
    have hmeasY : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping (B u) τ →
        Measurable (fun ω' => B u (τ ω') ω') := fun τ hτ =>
      Sandpile.Continuum.measurable_stopped_position (hBmM u) (hBc u)
        (hτ.measurable (hBm u))
    have hint3 : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping (B u) τ → (∀ ω', (τ ω' : ℝ) ≤ S) →
        Integrable (fun ω' => (1 - cutoff A (B u (τ ω') ω')) *
          |z p.2 (S - (τ ω' : ℝ)) (B u (τ ω') ω')|) PB := by
      intro τ hτ hτT
      have hz1 : Integrable (fun ω' => |z p.2 (S - (τ ω' : ℝ)) (B u (τ ω') ω')|) PB := by
        simpa only [abs_neg] using (hint1 τ hτ hτT).abs
      refine Integrable.mono' hz1 ?_ ?_
      · exact (((continuous_cutoff A).measurable.comp (hmeasY τ hτ)).const_sub
          1).aestronglyMeasurable.mul hz1.aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun ω' => ?_
        rw [Real.norm_eq_abs, abs_mul, abs_abs]
        have h0 : 0 ≤ 1 - cutoff A (B u (τ ω') ω') := by
          exact sub_nonneg.mpr (cutoff_le_one A _)
        rw [abs_of_nonneg h0]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (sub_le_self 1 (cutoff_nonneg A _)) (abs_nonneg _)
    have hbdd1 : BddAbove (stoppingPayoffs (B u) PB (z p.2) S) :=
      Sandpile.Continuum.bddAbove_stoppingPayoffs_of_samplewise_growth (hB u) (hBmM u) (hBc u)
        (z p.2) S hSp.le hcz (fun _ => (mz : ℝ) * (1 + ρ) ^ mz) ((mz : ℝ) * (1 + ρ) ^ mz)
        (Filter.Eventually.of_forall fun _ => le_refl _) mz
        (Filter.Eventually.of_forall fun _ vv hvv w => hgrowu vv
          (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal S hSp.le]; exact hvv) w)
    have hbdd2 : BddAbove (stoppingPayoffs (B u) PB (fun s w => cutoff A w * z p.2 s w) S) :=
      Sandpile.Continuum.bddAbove_stoppingPayoffs_of_samplewise_growth (hB u) (hBmM u) (hBc u)
        (fun s w => cutoff A w * z p.2 s w) S hSp.le hcχ
        (fun _ => (mz : ℝ) * (1 + ρ) ^ mz) ((mz : ℝ) * (1 + ρ) ^ mz)
        (Filter.Eventually.of_forall fun _ => le_refl _) mz
        (Filter.Eventually.of_forall fun _ vv hvv w => hgrowuχ vv
          (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal S hSp.le]; exact hvv) w)
    have hE₃ := hA₂ A hAA₂ S ⟨hSp.le, hS.2⟩ u ΩB inferInstance PB inferInstance (B u) (hB u) ρ hρ.le hun
      (by linarith) (z p.2) hgrowz hbdd1 hbdd2 hint1 hint2 hint3
      (fun τ hτ _ j => Sandpile.Continuum.measurableSet_reach_brownian (hBmM u) (hBc u) hτ _)
    have hcutB : |brownianDiscount (B u) PB (fun s w => cutoff A w * z p.2 s w) S
        - brownianDiscount (B u) PB (z p.2) S| ≤ ε / 8 := by
      rw [abs_sub_comm]; exact hE₃
    have hE₂' : |stoppingSup n yy (fun k X =>
          cutoff A (Sandpile.External.Lclt.scaledSite R (X k)) * f k (X k))
        - brownianDiscount (B u) PB (fun s w => cutoff A w * z p.2 s w) S|
        ≤ ε / 8 + 2 * η + 3 * η := by
      rw [← hwalkeq]
      simpa only [hnn, neg_neg] using hE₂
    simp only [hfdef] at hE₁ hE₂'
    have hb := Sandpile.abs_rescaled_odometer_sub_brownianValue_le hd R hRp (scenery d p.1) n yy
      (B u) PB (z p.2) (fun s w => cutoff A w * z p.2 s w) S u
      (fun k X => cutoff A (Sandpile.External.Lclt.scaledSite R (X k)) *
        -(Frozen.HeatPotentialInvariance.meshValue d R (scenery d p.1) (n - k) (X k)))
      (2 * η) (ε / 8) (ε / 8 + 2 * η + 3 * η) (ε / 8) hfield hE₁ hE₂' hcutB
    rw [hnn] at huerr
    have he : -(2 - (d : ℝ) / 2) = (d : ℝ) / 2 - 2 := by ring
    rw [he] at huerr
    rw [hηdef] at hb
    linarith only [hb, huerr, hε]
  calc P _ ≤ centeredMassLaw d ν ((badM ∪ badO) ∪ Gwᶜ) + P badG + PW (badC ∪ Nz) :=
        measure_error_le_of_marginals (centeredMassLaw d ν) PW P hPf hPs
          ((badM ∪ badO) ∪ Gwᶜ) (badC ∪ Nz) badG _ hsub
    _ ≤ ((ENNReal.ofReal (δ / 5) + ENNReal.ofReal (δ / 5)) + ENNReal.ofReal (δ / 5))
          + ENNReal.ofReal (δ / 5) + (0 + ENNReal.ofReal (δ / 5)) := by
        refine add_le_add (add_le_add ?_ hPgap) ?_
        · exact (measure_union_le _ _).trans
            (add_le_add ((measure_union_le _ _).trans (add_le_add hbadM hbadO)) hGwm)
        · exact (measure_union_le _ _).trans (add_le_add (le_of_eq hbadC) hNz)
    _ = ENNReal.ofReal δ := by
        rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end Parking.Support
