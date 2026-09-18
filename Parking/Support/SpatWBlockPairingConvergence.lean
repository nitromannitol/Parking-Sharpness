/-
Pairings of the rescaled divisible odometer converge jointly with a finite random block.
The limit space and field are parameters, so every pairing uses the same continuum witness.
-/
import Parking.Support.SpatWBarDivisibleJointMeasurable
import Parking.Support.NearestBallEvent
import Parking.Generic.FddBlockTightness

open MeasureTheory ProbabilityTheory Filter Topology
open Parking.Generic.BoundedFunctionalLift

noncomputable section
namespace Parking

variable {d p : ℕ} {B : Type*} [NormedAddCommGroup B]
    [MeasurableSpace B] [BorelSpace B] {Ω : Type} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {Uc : Ω → ℝ → (Fin d → ℝ) → ℝ}
    {V : ℝ → Data d → B} {Vlim : Ω → B}

/-- Bounded Lipschitz tests of the extra block and any finite family of odometer pairings
converge jointly. -/
theorem tendsto_integral_barDivisible_block_pairings_of_lipschitz
    (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure (law d ν)]
    (hUccont : ∀ ω, Continuous fun q : ℝ × (Fin d → ℝ) => Uc ω q.1 q.2)
    (hUcmeas : ∀ s x, Measurable fun ω => Uc ω s x)
    (hVm : ∀ R, Measurable (V R)) (hVlimm : Measurable Vlim)
    (t : ℝ) (ht : 0 < t) (K : Set (Fin d → ℝ)) (hK : IsCompact K) (hKne : K.Nonempty)
    (hfdd : ∀ (m : ℕ) (x : Fin m → (Fin d → ℝ)), (∀ k, x k ∈ K) →
      TendstoInDistribution (fun R w => (V R w, fun k => barDivisible w R t (x k))) atTop
        (fun ω => (Vlim ω, fun k => Uc ω t (x k))) (fun _ : ℝ => law d ν) Q)
    (htight : ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ R : ℝ in atTop,
      (law d ν) {w | ∃ z ∈ K, ∃ y ∈ K, dist z y < δ ∧
        η < |barDivisible w R t z - barDivisible w R t y|} ≤ ENNReal.ofReal ε)
    (h : Fin p → (Fin d → ℝ) → ℝ) (hh : ∀ j, Continuous (h j))
    {F : B × (Fin p → ℝ) → ℝ} {M : ℝ} (hFb : ∀ y, |F y| ≤ M)
    {LF : NNReal} (hFlip : LipschitzWith LF F) :
    Tendsto (fun R : ℝ => ∫ w, F (V R w,
      fun j => ∫ x in K, barDivisible w R t x * h j x) ∂law d ν) atTop
      (𝓝 (∫ ω, F (Vlim ω, fun j => ∫ x in K, Uc ω t x * h j x) ∂Q)) := by
  classical
  have hM : 0 ≤ M := (abs_nonneg (F 0)).trans (hFb 0)
  choose Mh hMh0 hhb using fun j => exists_bound_h_on_K hK (hh j)
  let C : ℝ := (∑ j, Mh j) * volume.real K
  have hC : 0 ≤ C := mul_nonneg (Finset.sum_nonneg fun j _ => hMh0 j) measureReal_nonneg
  let H : ((Fin d → ℝ) → ℝ) → (Fin p → ℝ) := fun g j => ∫ x in K, g x * h j x
  let Φ0 : B → ((Fin d → ℝ) → ℝ) → ℝ := fun b g => F (b, H g)
  have hΦ0 : ∀ b G, |Φ0 b G| ≤ M := fun b G => hFb _
  have hHLip : ∀ G J, NiceOnK K G → NiceOnK K J →
      dist (H G) (H J) ≤ C * supDistOn K G J := by
    intro G J hG hJ
    apply (dist_pi_le_iff (mul_nonneg hC (supDistOn_nonneg K G J))).2
    intro j
    have hj := abs_Phi0_sub_le (F := id) (LF := 1) hK hKne (hh j)
      (fun y z => by simp) (hMh0 j) (hhb j) hG hJ
    have hMj : Mh j ≤ ∑ j, Mh j := Finset.single_le_sum (fun i _ => hMh0 i) (Finset.mem_univ j)
    have hcoef : Mh j * volume.real K ≤ C :=
      mul_le_mul_of_nonneg_right hMj (measureReal_nonneg)
    have hbound := mul_le_mul_of_nonneg_right hcoef (supDistOn_nonneg K G J)
    simp only [one_mul] at hj
    simpa [H, Phi0, Real.dist_eq] using hj.trans hbound
  have hΦLip : ∀ b G J, NiceOnK K G → NiceOnK K J →
      |Φ0 b G - Φ0 b J| ≤ ((LF : ℝ) * C) * supDistOn K G J := by
    intro b G J hG hJ
    have hdist : dist (b, H G) (b, H J) = dist (H G) (H J) := by simp [Prod.dist_eq]
    have hF := hFlip.dist_le_mul (b, H G) (b, H J)
    rw [hdist, Real.dist_eq] at hF
    exact hF.trans (by simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left (hHLip G J hG hJ) LF.coe_nonneg)
  let L0 : ℝ := (LF : ℝ) * C + 2 * M
  have hL0 : 0 ≤ L0 := by dsimp [L0]; positivity
  let Φ : B → ((Fin d → ℝ) → ℝ) → ℝ :=
    fun b => liftPhiOn K (Φ0 b) (NiceOnK K) L0
  have hG0 : NiceOnK K (fun _ => (0 : ℝ)) :=
    ⟨measurable_const, ⟨0, fun x _ => by simp⟩⟩
  have hrecover : ∀ b G, NiceOnK K G → Φ b G = Φ0 b G := by
    intro b G hG
    exact liftPhiOn_eq_of_nice K (Φ0 b) (NiceOnK K) (hΦ0 b) hG
      (fun J hJ => hΦLip b G J hG hJ) (mul_nonneg LF.coe_nonneg hC)
  obtain ⟨B, hB⟩ := hK.isBounded.subset_closedBall (0 : Fin d → ℝ)
  have hBnn : 0 ≤ B := by
    obtain ⟨x, hx⟩ := hKne
    have hb := hB hx
    rw [Metric.mem_closedBall, dist_zero_right] at hb
    exact (norm_nonneg x).trans hb
  have hbar : ∀ b w R, 0 ≤ R → Φ b (fun z => barDivisible w R t z)
      = F (b, fun j => ∫ x in K, barDivisible w R t x * h j x) := by
    intro b w R hR
    exact hrecover b _ (niceOnK_mono hB (niceOnK_barDivisible hd w R t B hR ht.le))
  have hlim : ∀ b ω, Φ b (fun z => Uc ω t z)
      = F (b, fun j => ∫ x in K, Uc ω t x * h j x) := by
    intro b ω
    exact hrecover b _ (niceOnK_mono hB (niceOnK_Uc Uc ω t B hBnn (hUccont ω)))
  have hΦb : ∀ b G, |Φ b G| ≤ M + L0 := fun b G =>
    abs_liftPhiOn_le K (Φ0 b) (NiceOnK K) hG0 (hΦ0 b) hL0 G
  have hblock : ∀ a b G, NiceOnK K G → |Φ0 a G - Φ0 b G| ≤ (LF : ℝ) * dist a b := by
    intro a b G _
    simpa [Φ0, Prod.dist_eq, Real.dist_eq] using hFlip.dist_le_mul (a, H G) (b, H G)
  have hΦu := block_modulus_liftPhiOn K Φ0 (NiceOnK K) hG0 hΦ0 hL0 LF.coe_nonneg hblock
  have hfΦm : ∀ᶠ R : ℝ in atTop, Measurable fun w => Φ (V R w) (fun z => barDivisible w R t z) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    have heq : (fun w => Φ (V R w) (fun z => barDivisible w R t z)) =
        fun w => F (V R w, fun j => ∫ x in K, barDivisible w R t x * h j x) :=
      funext fun w => hbar (V R w) w R hR
    rw [heq]
    exact hFlip.continuous.measurable.comp ((hVm R).prodMk
      (measurable_pi_lambda _ fun j => measurable_integral_barDivisible_mul R t K hK (h j) (hh j)))
  haveI : ∀ _ : ℝ, IsProbabilityMeasure (law d ν) := fun _ => inferInstance
  have hconv := Generic.FddBlockTightness.tendsto_integral_of_fdd_of_equicontinuous
    (Φ := Φ) hK (Filter.Eventually.of_forall hVm) hVlimm
    (Filter.Eventually.of_forall fun R z => measurable_barDivisible R t z)
    (fun z => hUcmeas t z)
    (fun ω => ((hUccont ω).comp (Continuous.prodMk continuous_const continuous_id)).continuousOn)
    hfΦm hfdd htight hΦb hΦu
  have heqL : (fun R : ℝ => ∫ w, Φ (V R w) (fun z => barDivisible w R t z) ∂law d ν)
      =ᶠ[atTop] fun R => ∫ w, F (V R w,
        fun j => ∫ x in K, barDivisible w R t x * h j x) ∂law d ν := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact integral_congr_ae (Filter.Eventually.of_forall fun w => hbar (V R w) w R hR)
  have heqR : (∫ ω, Φ (Vlim ω) (fun z => Uc ω t z) ∂Q) =
      ∫ ω, F (Vlim ω, fun j => ∫ x in K, Uc ω t x * h j x) ∂Q :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => hlim (Vlim ω) ω)
  rw [heqR] at hconv
  exact hconv.congr' heqL


/-- Any finite collection of spatial pairings converges jointly with the prescribed
finite block, on the same continuum probability space as the finite-dimensional limit. -/
theorem tendstoInDistribution_barDivisible_block_pairings
    (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure (law d ν)]
    (hUccont : ∀ ω, Continuous fun q : ℝ × (Fin d → ℝ) => Uc ω q.1 q.2)
    (hUcmeas : ∀ s x, Measurable fun ω => Uc ω s x)
    (hVm : ∀ R, Measurable (V R)) (hVlimm : Measurable Vlim)
    (t : ℝ) (ht : 0 < t) (K : Set (Fin d → ℝ)) (hK : IsCompact K) (hKne : K.Nonempty)
    (hfdd : ∀ (m : ℕ) (x : Fin m → (Fin d → ℝ)), (∀ k, x k ∈ K) →
      TendstoInDistribution (fun R w => (V R w, fun k => barDivisible w R t (x k))) atTop
        (fun ω => (Vlim ω, fun k => Uc ω t (x k))) (fun _ : ℝ => law d ν) Q)
    (htight : ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ R : ℝ in atTop,
      (law d ν) {w | ∃ z ∈ K, ∃ y ∈ K, dist z y < δ ∧
        η < |barDivisible w R t z - barDivisible w R t y|} ≤ ENNReal.ofReal ε)
    (h : Fin p → (Fin d → ℝ) → ℝ) (hh : ∀ j, Continuous (h j))
    : TendstoInDistribution
      (fun R w => (V R w, fun j => ∫ x in K, barDivisible w R t x * h j x)) atTop
      (fun ω => (Vlim ω, fun j => ∫ x in K, Uc ω t x * h j x))
      (fun _ : ℝ => law d ν) Q := by
  have hXm : ∀ R, Measurable fun w =>
      (V R w, fun j => ∫ x in K, barDivisible w R t x * h j x) := fun R =>
    (hVm R).prodMk (measurable_pi_lambda _ fun j =>
      measurable_integral_barDivisible_mul R t K hK (h j) (hh j))
  have hZm : Measurable fun ω =>
      (Vlim ω, fun j => ∫ x in K, Uc ω t x * h j x) :=
    hVlimm.prodMk (measurable_pi_lambda _ fun j =>
      measurable_integral_Uc_mul hUcmeas hUccont t K hK (h j) (hh j))
  refine ⟨fun R => (hXm R).aemeasurable, hZm.aemeasurable, ?_⟩
  rw [tendsto_iff_forall_lipschitz_integral_tendsto]
  intro F hFb hFlip
  obtain ⟨M, hM⟩ := hFb
  obtain ⟨LF, hLF⟩ := hFlip
  have hbound : ∀ y, |F y| ≤ M + |F 0| := by
    intro y
    have hy := hM y 0
    rw [Real.dist_eq] at hy
    linarith [abs_sub_abs_le_abs_sub (F y) (F 0)]
  have hcore := tendsto_integral_barDivisible_block_pairings_of_lipschitz
    hd ν hUccont hUcmeas hVm hVlimm t ht K hK hKne hfdd htight h hh hbound hLF
  have hmap1 : ∀ R, ∫ y, F y ∂((law d ν).map
      (fun w => (V R w, fun j => ∫ x in K, barDivisible w R t x * h j x))) =
        ∫ w, F (V R w, fun j => ∫ x in K, barDivisible w R t x * h j x) ∂law d ν :=
    fun R => integral_map (hXm R).aemeasurable hLF.continuous.aestronglyMeasurable
  have hmap2 : ∫ y, F y ∂(Q.map
      (fun ω => (Vlim ω, fun j => ∫ x in K, Uc ω t x * h j x))) =
        ∫ ω, F (Vlim ω, fun j => ∫ x in K, Uc ω t x * h j x) ∂Q :=
    integral_map hZm.aemeasurable hLF.continuous.aestronglyMeasurable
  simpa only [ProbabilityMeasure.coe_mk, hmap1, hmap2] using hcore

end Parking
end
