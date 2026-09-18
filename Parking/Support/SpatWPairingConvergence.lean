/-
The LOCALLY-UNIFORM-IN-PROBABILITY convergence of `barDivisible` to `Uc` on compacts, in the
"pairing" form the rest of the assembly consumes: for a fixed positive time `t`, a fixed compact
spatial set `K`, and a fixed continuous test function `h`,
```
TendstoInDistribution (fun R w => ∫ x in K, barDivisible w R t x * h x) atTop
  (fun ω => ∫ x in K, Uc ω t x * h x) (fun _ => law d ν) Q
```
This is the pairing convergence needed to close, one level up, the `signedPair` block of
`Parking.Frozen.spatial_scaling`'s joint clause and the continuum equation (paper Step 2's
"Taylor expansion and the locally uniform convergence of `\overline U_R(1,\cdot)`" sentence):
once `signedMiddle`/the discrete recursion are Riemann-sum-approximated by a sum of
`barDivisible(w,R,1,\cdot)` against a fixed test function, THIS pairing convergence identifies
the limit.

The route has four steps, all carried out against ABSTRACT `Ω, Q, W, Uc` carrying the
properties `Parking.External.SpatialOdometerScaling` supplies, rather than by re-invoking the
External a second time: `Parking.Frozen.spatial_scaling`'s own proof destructures the External
EXACTLY ONCE, at the top of its `by` block, and every fact consumed there must be about THAT
SAME witness, not a freshly re-derived one — a second `obtain` on the same External would
produce, in general, a DIFFERENT, unrelated existential witness, since Prop elimination gives no
identity between two separate eliminations of the same hypothesis:

1. `hfdd`: the finite-dimensional convergence of `barDivisible` alone (no scenery, no
   `barOdometer`), at an arbitrary finite tuple of points of `K` at the fixed time `t`, from
   `hjointFDD` specialized at the empty `φ`-tuple (`m := 0`) and `sp j := (t, x j)`, via the
   `F.compContinuous ⟨Prod.snd, continuous_snd⟩` reindexing trick (`Parking/Support/
   SpatWBarOdometerJointFdd.lean` uses the same technique for a different reindexing).
2. `htight`: the spatial equicontinuity-in-probability of `barDivisible(\cdot,t,\cdot)` on `K`,
   from `hequicont` (the External's own JOINT space-time clause) applied at the space-time
   compact `K' := {t} ×ˢ K`, sliced back down to a purely spatial statement using
   `dist (t,z) (t,y) = dist z y` on the product metric.
3. The McShane lift `Parking.Generic.BoundedFunctionalLift.liftPhiOn` applied to
   `Phi0 K h F := fun g => F (∫_K g \cdot h)` (`Parking/Support/SpatWDivisiblePairing.lean`),
   fed into `LatticeProb.tendsto_integral_of_fdd_of_equicontinuous'` together with (1)-(2) and
   the measurability facts `Parking/Support/SpatWBarDivisibleJointMeasurable.lean` supplies
   (joint measurability of the lattice field lets the Bochner integral `\int_K
   barDivisible(w,R,t,\cdot)h` be shown measurable in `w`, hence `\Phi` composed with the field
   is measurable), recovering `\Phi` as `Phi0 K h F` exactly at both
   `barDivisible(w,R,t,\cdot)` and `Uc(\omega,t,\cdot)` via `liftPhiOn_eq_of_nice`
   (`niceOnK_barDivisible`/`niceOnK_Uc`, transferred down to the compact `K` from a containing
   closed ball via `niceOnK_mono`).
4. The Lipschitz-to-continuous bootstrap, EXACTLY mirroring `Parking.hlaw_orientedBoxReward`
   (`Parking/Support/TightHlawAssembly.lean`): weak convergence of the two real-valued laws is
   equivalent to convergence against every bounded Lipschitz `F : ℝ → ℝ`
   (`MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto`), and (3) supplies exactly
   that; the Portmanteau equivalence then gives it against every bounded CONTINUOUS `F`
   (`MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`), which is what
   `Parking.Generic.Slutsky.tendstoInDistribution_of_tendsto_integral` needs to conclude
   `TendstoInDistribution`.
-/
import Parking.Support.SpatWBarDivisibleJointMeasurable
import Parking.Support.NearestBallEvent
import Parking.Generic.Slutsky
import Mathlib.MeasureTheory.Measure.Portmanteau

open MeasureTheory ProbabilityTheory Filter Topology
open Parking.Generic.BoundedFunctionalLift

noncomputable section
namespace Parking

variable {d : ℕ}

/-! ### Step 1: the finite-dimensional convergence of `barDivisible` alone -/

/-- **`barDivisible` alone converges in finite dimensions to `Uc`**, at the fixed time `t`, from
`hjointFDD` specialized at the empty scenery tuple. -/
theorem tendstoInDistribution_barDivisible_fdd {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {W : ((Fin d → ℝ) → ℝ) → Ω → ℝ} {Uc : Ω → ℝ → (Fin d → ℝ) → ℝ}
    (_hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure (law d ν)]
    (hUcmeas : ∀ s x, Measurable fun ω => Uc ω s x)
    (hjointFDD : ∀ (m p' : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ) (sp : Fin p' → ℝ × (Fin d → ℝ)),
      (∀ i, IsTestFun (φ i)) → (∀ j, 0 < (sp j).1) →
      ∀ F : BoundedContinuousFunction ((Fin m → ℝ) × (Fin p' → ℝ)) ℝ,
        Tendsto (fun R : ℝ => ∫ w, F (fun i => scenePair w R (φ i),
              fun j => barDivisible w R (sp j).1 (sp j).2) ∂(law d ν)) atTop
          (𝓝 (∫ ω, F (fun i => W (φ i) ω, fun j => Uc ω (sp j).1 (sp j).2) ∂Q)))
    (t : ℝ) (ht : 0 < t) (m : ℕ) (x : Fin m → (Fin d → ℝ)) :
    TendstoInDistribution (fun R w k => barDivisible w R t (x k)) atTop
      (fun ω k => Uc ω t (x k)) (fun _ : ℝ => law d ν) Q := by
  have hXm : ∀ R : ℝ, AEMeasurable (fun w => fun k => barDivisible w R t (x k)) (law d ν) :=
    fun R => (measurable_pi_lambda _ fun k => measurable_barDivisible R t (x k)).aemeasurable
  have hZm : AEMeasurable (fun ω => fun k => Uc ω t (x k)) Q :=
    (measurable_pi_lambda _ fun k => hUcmeas t (x k)).aemeasurable
  refine Parking.Generic.Slutsky.tendstoInDistribution_of_tendsto_integral hXm hZm ?_
  intro G
  set φ : Fin 0 → (Fin d → ℝ) → ℝ := Fin.elim0 with hφdef
  set sp : Fin m → ℝ × (Fin d → ℝ) := fun j => (t, x j) with hspdef
  have hφ : ∀ i : Fin 0, IsTestFun (φ i) := fun i => i.elim0
  have hsp : ∀ j, 0 < (sp j).1 := fun _ => ht
  have hres := hjointFDD 0 m φ sp hφ hsp (G.compContinuous ⟨Prod.snd, continuous_snd⟩)
  have heqL : (fun R : ℝ => ∫ w, (G.compContinuous (⟨Prod.snd, continuous_snd⟩ : C(_, _)))
        (fun i => scenePair w R (φ i), fun j => barDivisible w R (sp j).1 (sp j).2)
      ∂(law d ν))
      = fun R : ℝ => ∫ w, G (fun k => barDivisible w R t (x k)) ∂(law d ν) := by
    funext R
    congr 1
  have heqR : (∫ ω, (G.compContinuous (⟨Prod.snd, continuous_snd⟩ : C(_, _)))
        (fun i => W (φ i) ω, fun j => Uc ω (sp j).1 (sp j).2) ∂Q)
      = ∫ ω, G (fun k => Uc ω t (x k)) ∂Q := by
    congr 1
  rw [heqL, heqR] at hres
  exact hres

/-! ### Step 2: the spatial equicontinuity of `barDivisible(\cdot,t,\cdot)` from the joint
space-time clause -/

theorem htight_barDivisible_fixedTime
    (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure (law d ν)]
    (hequicont : ∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → (∀ p ∈ K, 0 < p.1) → ∀ ε : ℝ, 0 < ε →
      ∀ ε' : ℝ, 0 < ε' → ∃ δ : ℝ, 0 < δ ∧ ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
        ((law d ν) {w | ε < ⨆ p ∈ K, ⨆ q ∈ K, ⨆ _ : dist p q ≤ δ,
            |barDivisible w R p.1 p.2 - barDivisible w R q.1 q.2|}).toReal ≤ ε')
    (t : ℝ) (ht : 0 < t) (K : Set (Fin d → ℝ)) (hK : IsCompact K) :
    ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ R : ℝ in atTop,
      (law d ν) {w | ∃ z ∈ K, ∃ y ∈ K, dist z y < δ ∧
          η < |barDivisible w R t z - barDivisible w R t y|} ≤ ENNReal.ofReal ε := by
  intro ε η hε hη
  set K' : Set (ℝ × (Fin d → ℝ)) := ({t} : Set ℝ) ×ˢ K with hK'def
  have hK'compact : IsCompact K' := isCompact_singleton.prod hK
  have hK'pos : ∀ p ∈ K', 0 < p.1 := by
    rintro p hp
    rw [hK'def, Set.mem_prod, Set.mem_singleton_iff] at hp
    rw [hp.1]; exact ht
  obtain ⟨δ, hδ, hev⟩ :=
    htight_of_spatial_tightness hd ν K' hK'compact (hequicont K' hK'compact hK'pos) ε η hε hη
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hev] with R hR
  refine le_trans (measure_mono ?_) hR
  rintro w ⟨z, hz, y, hy, hzy, hgt⟩
  refine ⟨(t, z), ?_, (t, y), ?_, ?_, ?_⟩
  · rw [hK'def, Set.mem_prod]; exact ⟨rfl, hz⟩
  · rw [hK'def, Set.mem_prod]; exact ⟨rfl, hy⟩
  · rw [Prod.dist_eq]; simpa using hzy
  · simpa using hgt

/-! ### Step 3-4: the assembly, and the Lipschitz-to-continuous bootstrap -/

/-- **The Lipschitz-tested core of the pairing convergence.** -/
theorem tendsto_integral_barDivisible_pairing_of_lipschitz {Ω : Type} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {W : ((Fin d → ℝ) → ℝ) → Ω → ℝ}
    {Uc : Ω → ℝ → (Fin d → ℝ) → ℝ}
    (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure (law d ν)]
    (hUccont : ∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2)
    (hUcmeas : ∀ s x, Measurable fun ω => Uc ω s x)
    (hjointFDD : ∀ (m p' : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ) (sp : Fin p' → ℝ × (Fin d → ℝ)),
      (∀ i, IsTestFun (φ i)) → (∀ j, 0 < (sp j).1) →
      ∀ F : BoundedContinuousFunction ((Fin m → ℝ) × (Fin p' → ℝ)) ℝ,
        Tendsto (fun R : ℝ => ∫ w, F (fun i => scenePair w R (φ i),
              fun j => barDivisible w R (sp j).1 (sp j).2) ∂(law d ν)) atTop
          (𝓝 (∫ ω, F (fun i => W (φ i) ω, fun j => Uc ω (sp j).1 (sp j).2) ∂Q)))
    (hequicont : ∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → (∀ p ∈ K, 0 < p.1) → ∀ ε : ℝ, 0 < ε →
      ∀ ε' : ℝ, 0 < ε' → ∃ δ : ℝ, 0 < δ ∧ ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
        ((law d ν) {w | ε < ⨆ p ∈ K, ⨆ q ∈ K, ⨆ _ : dist p q ≤ δ,
            |barDivisible w R p.1 p.2 - barDivisible w R q.1 q.2|}).toReal ≤ ε')
    (t : ℝ) (ht : 0 < t) (K : Set (Fin d → ℝ)) (hK : IsCompact K) (hKne : K.Nonempty)
    (h : (Fin d → ℝ) → ℝ) (hh : Continuous h)
    {F : ℝ → ℝ} {M0 : ℝ} (hFb : ∀ y, |F y| ≤ M0) {LF : ℝ}
    (hFlip : ∀ y z, |F y - F z| ≤ LF * |y - z|) :
    Tendsto (fun R : ℝ => ∫ w, F (∫ x in K, barDivisible w R t x * h x) ∂(law d ν)) atTop
      (𝓝 (∫ ω, F (∫ x in K, Uc ω t x * h x) ∂Q)) := by
  have hM0 : 0 ≤ M0 := le_trans (abs_nonneg _) (hFb 0)
  have hLF : 0 ≤ LF := by
    have h10 := hFlip 1 0
    norm_num at h10
    exact le_trans (abs_nonneg _) h10
  obtain ⟨Mh, hMh0, hhb⟩ := exists_bound_h_on_K hK hh
  set L0' : ℝ := LF * Mh * volume.real K with hL0'def
  have hL0'nn : 0 ≤ L0' := by rw [hL0'def]; positivity
  set L0 : ℝ := L0' + 2 * M0 with hL0def
  have hL0nn : 0 ≤ L0 := by rw [hL0def]; linarith
  set Φ : ((Fin d → ℝ) → ℝ) → ℝ := liftPhiOn K (Phi0 K h F) (NiceOnK K) L0 with hΦdef
  have hΦ0 : ∀ G, |Phi0 K h F G| ≤ M0 := fun G => abs_Phi0_le K h hFb G
  have hG0 : NiceOnK K (fun _ : Fin d → ℝ => (0 : ℝ)) :=
    ⟨measurable_const, ⟨0, fun x _ => by simp⟩⟩
  obtain ⟨B, hB⟩ := hK.isBounded.subset_closedBall (0 : Fin d → ℝ)
  have hBnn : 0 ≤ B := by
    obtain ⟨x0, hx0⟩ := hKne
    have hmem := hB hx0
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact le_trans (norm_nonneg _) hmem
  have hΦcoeBarDivisible : ∀ w R, 0 ≤ R →
      Φ (fun z => barDivisible w R t z) = Phi0 K h F (fun z => barDivisible w R t z) := by
    intro w R hR
    have hnice : NiceOnK K (fun z => barDivisible w R t z) :=
      niceOnK_mono hB (niceOnK_barDivisible hd w R t B hR ht.le)
    refine liftPhiOn_eq_of_nice K (Phi0 K h F) (NiceOnK K) hΦ0 hnice ?_ hL0'nn
    intro G hG
    exact abs_Phi0_sub_le hK hKne hh hFlip hMh0 hhb hnice hG
  have hΦcoeUc : ∀ ω, Φ (fun z => Uc ω t z) = Phi0 K h F (fun z => Uc ω t z) := by
    intro ω
    have hnice : NiceOnK K (fun z => Uc ω t z) :=
      niceOnK_mono hB (niceOnK_Uc Uc ω t B hBnn (hUccont ω))
    refine liftPhiOn_eq_of_nice K (Phi0 K h F) (NiceOnK K) hΦ0 hnice ?_ hL0'nn
    intro G hG
    exact abs_Phi0_sub_le hK hKne hh hFlip hMh0 hhb hnice hG
  have hΦb : ∀ v, |Φ v| ≤ M0 + L0 :=
    fun v => abs_liftPhiOn_le K (Phi0 K h F) (NiceOnK K) hG0 hΦ0 hL0nn v
  have hΦu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v w : (Fin d → ℝ) → ℝ,
      (∀ z ∈ K, |v z - w z| ≤ δ) → |Φ v - Φ w| ≤ ε :=
    hΦu_of_lipschitz K (Phi0 K h F) (NiceOnK K) hΦ0 hL0nn hG0
  have hfm : ∀ᶠ R : ℝ in atTop, ∀ z : Fin d → ℝ, Measurable (fun w => barDivisible w R t z) :=
    Filter.Eventually.of_forall fun R z => measurable_barDivisible R t z
  have hgm : ∀ z, Measurable fun ω => Uc ω t z := fun z => hUcmeas t z
  have hgc : ∀ ω, ContinuousOn (fun z => Uc ω t z) K := fun ω =>
    ((hUccont ω).comp (Continuous.prodMk continuous_const continuous_id)).continuousOn
  have hFcont : Continuous F := by
    have hLip : LipschitzWith LF.toNNReal F := by
      apply LipschitzWith.of_dist_le_mul
      intro y z
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal LF hLF]
      exact hFlip y z
    exact hLip.continuous
  have hfΦm : ∀ᶠ R : ℝ in atTop, Measurable fun w => Φ (fun z => barDivisible w R t z) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    have heq : (fun w => Φ (fun z => barDivisible w R t z))
        = fun w => F (∫ x in K, barDivisible w R t x * h x) := by
      funext w
      rw [hΦcoeBarDivisible w R hR]
      rfl
    rw [heq]
    exact hFcont.measurable.comp (measurable_integral_barDivisible_mul R t K hK h hh)
  have hfdd : ∀ (m : ℕ) (x : Fin m → (Fin d → ℝ)), (∀ k, x k ∈ K) →
      TendstoInDistribution (fun R ω k => barDivisible ω R t (x k)) atTop
        (fun ω k => Uc ω t (x k)) (fun _ : ℝ => law d ν) Q :=
    fun m x _ => tendstoInDistribution_barDivisible_fdd hd ν hUcmeas hjointFDD t ht m x
  have htight : ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ R : ℝ in atTop,
      (law d ν) {w | ∃ z ∈ K, ∃ y ∈ K, dist z y < δ ∧
          η < |barDivisible w R t z - barDivisible w R t y|} ≤ ENNReal.ofReal ε :=
    htight_barDivisible_fixedTime hd ν hequicont t ht K hK
  set f' : ℝ → (Fin d → ℝ) → Data d → ℝ := fun R z w => barDivisible w R t z with hf'def
  set g' : (Fin d → ℝ) → Ω → ℝ := fun z ω => Uc ω t z with hg'def
  haveI hPconst : ∀ _ : ℝ, IsProbabilityMeasure (law d ν) := fun _ => inferInstance
  have hconv : Tendsto (fun R : ℝ => ∫ w, Φ (fun z => f' R z w) ∂(law d ν)) atTop
      (𝓝 (∫ ω, Φ (fun z => g' z ω) ∂Q)) :=
    @LatticeProb.tendsto_integral_of_fdd_of_equicontinuous'
      (Fin d → ℝ) inferInstance ℝ (fun _ => Data d) (fun _ => inferInstance) Ω inferInstance
      (fun _ => law d ν) hPconst Q inferInstance atTop f' g' K hK Φ
      hfm hgm hgc hfΦm hfdd htight (M0 + L0) hΦb hΦu
  have heqL : (fun R : ℝ => ∫ w, Φ (fun z => barDivisible w R t z) ∂(law d ν))
      =ᶠ[atTop] fun R : ℝ => ∫ w, F (∫ x in K, barDivisible w R t x * h x) ∂(law d ν) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact integral_congr_ae
      (Filter.Eventually.of_forall fun w => (hΦcoeBarDivisible w R hR).trans rfl)
  have heqR : (∫ ω, Φ (fun z => Uc ω t z) ∂Q) = ∫ ω, F (∫ x in K, Uc ω t x * h x) ∂Q :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => (hΦcoeUc ω).trans rfl)
  rw [heqR] at hconv
  exact hconv.congr' heqL

/-! ### The bootstrap: from bounded Lipschitz `F` to every bounded continuous `F`, and to
`TendstoInDistribution` -/

/-- **The pairing convergence, `TendstoInDistribution` form.**  `barDivisible`'s pairing against
a fixed continuous test function on a compact set converges in distribution to `Uc`'s. -/
theorem tendstoInDistribution_barDivisible_pairing {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {W : ((Fin d → ℝ) → ℝ) → Ω → ℝ} {Uc : Ω → ℝ → (Fin d → ℝ) → ℝ}
    (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure (law d ν)]
    (hUccont : ∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2)
    (hUcmeas : ∀ s x, Measurable fun ω => Uc ω s x)
    (hjointFDD : ∀ (m p' : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ) (sp : Fin p' → ℝ × (Fin d → ℝ)),
      (∀ i, IsTestFun (φ i)) → (∀ j, 0 < (sp j).1) →
      ∀ F : BoundedContinuousFunction ((Fin m → ℝ) × (Fin p' → ℝ)) ℝ,
        Tendsto (fun R : ℝ => ∫ w, F (fun i => scenePair w R (φ i),
              fun j => barDivisible w R (sp j).1 (sp j).2) ∂(law d ν)) atTop
          (𝓝 (∫ ω, F (fun i => W (φ i) ω, fun j => Uc ω (sp j).1 (sp j).2) ∂Q)))
    (hequicont : ∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → (∀ p ∈ K, 0 < p.1) → ∀ ε : ℝ, 0 < ε →
      ∀ ε' : ℝ, 0 < ε' → ∃ δ : ℝ, 0 < δ ∧ ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
        ((law d ν) {w | ε < ⨆ p ∈ K, ⨆ q ∈ K, ⨆ _ : dist p q ≤ δ,
            |barDivisible w R p.1 p.2 - barDivisible w R q.1 q.2|}).toReal ≤ ε')
    (t : ℝ) (ht : 0 < t) (K : Set (Fin d → ℝ)) (hK : IsCompact K) (hKne : K.Nonempty)
    (h : (Fin d → ℝ) → ℝ) (hh : Continuous h) :
    TendstoInDistribution (fun R w => ∫ x in K, barDivisible w R t x * h x) atTop
      (fun ω => ∫ x in K, Uc ω t x * h x) (fun _ : ℝ => law d ν) Q := by
  set μs : ℝ → ProbabilityMeasure ℝ := fun R =>
    ⟨(law d ν).map (fun w => ∫ x in K, barDivisible w R t x * h x),
      Measure.isProbabilityMeasure_map
        (measurable_integral_barDivisible_mul R t K hK h hh).aemeasurable⟩ with hμsdef
  set μ : ProbabilityMeasure ℝ := ⟨Q.map (fun ω => ∫ x in K, Uc ω t x * h x),
      Measure.isProbabilityMeasure_map
        (measurable_integral_Uc_mul hUcmeas hUccont t K hK h hh).aemeasurable⟩ with hμdef
  have hmapL : ∀ (R : ℝ) (g : ℝ → ℝ), Continuous g →
      ∫ y, g y ∂(μs R : Measure ℝ) = ∫ w, g (∫ x in K, barDivisible w R t x * h x) ∂(law d ν) :=
    fun R g hg => by
      simpa [hμsdef] using
        integral_map (measurable_integral_barDivisible_mul R t K hK h hh).aemeasurable
          hg.aestronglyMeasurable
  have hmapR : ∀ g : ℝ → ℝ, Continuous g →
      ∫ y, g y ∂(μ : Measure ℝ) = ∫ ω, g (∫ x in K, Uc ω t x * h x) ∂Q :=
    fun g hg => by
      simpa [hμdef] using
        integral_map (measurable_integral_Uc_mul hUcmeas hUccont t K hK h hh).aemeasurable
          hg.aestronglyMeasurable
  have hconv : Tendsto μs atTop (𝓝 μ) := by
    rw [tendsto_iff_forall_lipschitz_integral_tendsto]
    intro f hfb hflip
    obtain ⟨M0, hM0⟩ := hfb
    obtain ⟨LF, hLF⟩ := hflip
    have hΦ0 : ∀ y, |f y| ≤ M0 + |f 0| := by
      intro y
      have hd0 := hM0 y 0
      rw [Real.dist_eq] at hd0
      have h2 := abs_sub_abs_le_abs_sub (f y) (f 0)
      linarith
    have hFlip' : ∀ y z, |f y - f z| ≤ (LF : ℝ) * |y - z| := by
      intro y z
      have h := hLF.dist_le_mul y z
      rwa [Real.dist_eq, Real.dist_eq] at h
    have hcore := tendsto_integral_barDivisible_pairing_of_lipschitz hd ν hUccont hUcmeas
      hjointFDD hequicont t ht K hK hKne h hh hΦ0 hFlip'
    have heqfun : (fun R : ℝ => ∫ y, f y ∂(μs R : Measure ℝ))
        =ᶠ[atTop] fun R => ∫ w, f (∫ x in K, barDivisible w R t x * h x) ∂(law d ν) :=
      Filter.Eventually.of_forall fun R => hmapL R f hLF.continuous
    have heqR : (∫ y, f y ∂(μ : Measure ℝ)) = ∫ ω, f (∫ x in K, Uc ω t x * h x) ∂Q :=
      hmapR f hLF.continuous
    rw [heqR]
    exact hcore.congr' heqfun.symm
  have hres := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv
  refine Parking.Generic.Slutsky.tendstoInDistribution_of_tendsto_integral
    (fun R => (measurable_integral_barDivisible_mul R t K hK h hh).aemeasurable)
    (measurable_integral_Uc_mul hUcmeas hUccont t K hK h hh).aemeasurable ?_
  intro F
  have h1 := hres F
  have heqfun : (fun R : ℝ => ∫ y, F y ∂(μs R : Measure ℝ))
      = fun R => ∫ w, F (∫ x in K, barDivisible w R t x * h x) ∂(law d ν) :=
    funext fun R => hmapL R F F.continuous
  rw [heqfun, hmapR F F.continuous] at h1
  exact h1

end Parking
end
