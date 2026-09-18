/-
`hlaw` (`parking.tex:3199-3203`): the discrete box-reward law converges weakly to the
continuum box-reward law on `C(rewardBox T A, ℝ)`.

`Parking.tendsto_integral_boxRewardLaw_of_lipschitz` is the Lipschitz-tested core: for a
bounded, Lipschitz `Φ0 : C(rewardBox T A, ℝ) → ℝ`, its McShane lift `Parking.liftPhi Φ0 L0`
(`Parking.Support.TightLiftPhi`) is fed to `LatticeProb.tendsto_integral_of_fdd_of_equicontinuous'`
with the finite-dimensional convergence `Parking.Support.TightHlawFdd`'s `hfdd` and
equicontinuity `htight`, at `K := Set.univ` (the box itself, via `Parking.boxToFin`); the exact
recovery `Parking.liftPhi_coe_eq` rewrites both sides of the conclusion back to genuine
`Φ0`-integrals against `Parking.boxRewardLaw`/`Parking.contBoxRewardLaw` via `integral_map`.

`Parking.hlaw_orientedBoxReward` bootstraps this to every bounded CONTINUOUS `Φ0`, exactly as
`Parking.exists_weak_limit` (`Parking.Support.WeakLimit`) bootstraps the real-line case: weak
convergence of probability measures is equivalent to convergence against every bounded
Lipschitz function (`tendsto_iff_forall_lipschitz_integral_tendsto`), and then automatically
holds against every bounded continuous function
(`ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`).
-/
import Parking.Support.TightLiftPhi
import Parking.Support.TightHlawFdd
import Parking.Support.TightContBoxLimit
import Mathlib.MeasureTheory.Measure.Portmanteau

open MeasureTheory LatticeProb Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace Parking

local instance (T A : ℝ) : MeasurableSpace C(rewardBox T A, ℝ) := borel _
local instance (T A : ℝ) : BorelSpace C(rewardBox T A, ℝ) := ⟨rfl⟩

variable {T A : ℝ}

/-- **The Lipschitz-tested core of `hlaw`.**  For `Φ0` bounded by `M0` and `L0'`-Lipschitz for
the sup metric on `C(rewardBox T A, ℝ)`, the expectations of `Φ0` under the discrete box-reward
law converge to its expectation under the continuum box-reward law. -/
theorem tendsto_integral_boxRewardLaw_of_lipschitz (ν : Measure ℤ) (hν : CriticalLaw ν)
    (hBinomial : External.BinomialLocalCLT) (hT : 0 ≤ T) (hA : 0 ≤ A)
    {Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ} (hYmeas : ∀ z, Measurable (Y z))
    (hYcont : ∀ ω, ContinuousOn (fun z => Y z ω) (orientedBox T A))
    (hYmod : ∀ z ∈ orientedBox T A,
      contZ (∫ x : ℝ, x ^ 2 ∂(realLaw ν)) T (z 0) (z 1) =ᵐ[contNoiseLaw] Y z)
    {Φ0 : C(rewardBox T A, ℝ) → ℝ} {M0 : ℝ} (hΦ0 : ∀ G, |Φ0 G| ≤ M0)
    {L0' : ℝ≥0} (hΦ0lip : LipschitzWith L0' Φ0) :
    Tendsto (fun n => ∫ G, Φ0 G ∂(boxRewardLaw T ν hT A hA n)) atTop
      (𝓝 (∫ G, Φ0 G ∂(contBoxRewardLaw T hT A hA Y hYmeas hYcont))) := by
  haveI : IsProbabilityMeasure ν := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI : IsProbabilityMeasure (iidLaw 2 (realLaw ν)) := by unfold iidLaw; infer_instance
  haveI hne : Nonempty (rewardBox T A) :=
    ⟨⟨⟨0, Set.left_mem_Icc.mpr hT⟩, ⟨-(2 * A), Set.left_mem_Icc.mpr (by linarith)⟩⟩⟩
  have hΦ0lip' : ∀ G G' : C(rewardBox T A, ℝ), |Φ0 G - Φ0 G'| ≤ (L0' : ℝ) * dist G G' := by
    intro G G'
    have h := hΦ0lip.dist_le_mul G G'
    rwa [Real.dist_eq] at h
  have hM0nn : 0 ≤ M0 := le_trans (abs_nonneg _) (hΦ0 0)
  set L0 : ℝ := (L0' : ℝ) + 2 * M0 with hL0def
  have hL0 : 0 ≤ L0 := by rw [hL0def]; positivity
  set Φ : (rewardBox T A → ℝ) → ℝ := liftPhi Φ0 L0 with hΦdef
  have hΦcoe : ∀ H : C(rewardBox T A, ℝ), Φ (⇑H) = Φ0 H := by
    intro H
    rw [hΦdef, hL0def]
    exact liftPhi_coe_eq hΦ0 hΦ0lip' L0'.coe_nonneg H
  have hK : IsCompact (Set.univ : Set (rewardBox T A)) := isCompact_univ
  have hfm : ∀ᶠ n : ℕ in atTop, ∀ z : rewardBox T A,
      Measurable (fun ω : Site 2 → ℝ => orientedBoxReward T n ω (boxToFin T A z)) :=
    Filter.Eventually.of_forall fun n z => measurable_orientedBoxReward T n (boxToFin T A z)
  have hgm : ∀ z : rewardBox T A, Measurable (fun ω : contNoiseSpace => Y (boxToFin T A z) ω) :=
    fun z => hYmeas (boxToFin T A z)
  have hgc : ∀ ω : contNoiseSpace, ContinuousOn (fun z : rewardBox T A => Y (boxToFin T A z) ω)
      (Set.univ : Set (rewardBox T A)) := fun ω =>
    (contBoxLimitMap T hT A hA Y hYcont ω).continuous.continuousOn
  have hfΦm : ∀ᶠ n : ℕ in atTop, Measurable fun ω : Site 2 → ℝ =>
      Φ (fun z : rewardBox T A => orientedBoxReward T n ω (boxToFin T A z)) := by
    refine Filter.Eventually.of_forall fun n => ?_
    have heq : (fun ω : Site 2 → ℝ =>
        Φ (fun z : rewardBox T A => orientedBoxReward T n ω (boxToFin T A z)))
        = fun ω => Φ0 (boxRewardMap T hT A hA n ω) := by
      funext ω
      have hc : (fun z : rewardBox T A => orientedBoxReward T n ω (boxToFin T A z))
          = ⇑(boxRewardMap T hT A hA n ω) := rfl
      rw [hc]; exact hΦcoe _
    rw [heq]
    exact hΦ0lip.continuous.measurable.comp (measurable_boxRewardMap T hT A hA n)
  have hfdd : ∀ (m : ℕ) (x : Fin m → rewardBox T A),
      (∀ k, x k ∈ (Set.univ : Set (rewardBox T A))) →
      TendstoInDistribution (fun n ω k => orientedBoxReward T n ω (boxToFin T A (x k))) atTop
        (fun ω k => Y (boxToFin T A (x k)) ω) (fun _ : ℕ => iidLaw 2 (realLaw ν)) contNoiseLaw :=
    fun _ x _ => tendstoInDistribution_orientedBoxReward_boxToFin ν hν hBinomial hT hA hYmod x
  have htight : ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      iidLaw 2 (realLaw ν) {ω : Site 2 → ℝ | ∃ z ∈ (Set.univ : Set (rewardBox T A)),
        ∃ y ∈ (Set.univ : Set (rewardBox T A)), dist z y < δ ∧
          η < |orientedBoxReward T n ω (boxToFin T A z) -
            orientedBoxReward T n ω (boxToFin T A y)|} ≤ ENNReal.ofReal ε :=
    fun ε η hε hη => htight_orientedBoxReward_boxToFin ν hν 16 (by norm_num) hT hA ε η hε hη
  have hΦb : ∀ v, |Φ v| ≤ M0 + L0 := by
    intro v; rw [hΦdef]; exact abs_liftPhi_le hΦ0 hL0 v
  have hΦu : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v w : rewardBox T A → ℝ,
      (∀ z ∈ (Set.univ : Set (rewardBox T A)), |v z - w z| ≤ δ) → |Φ v - Φ w| ≤ ε := by
    intro ε hε
    refine ⟨min 1 (ε / (L0 + 1)), lt_min one_pos (by positivity), fun v w hvw => ?_⟩
    have hcap : capDist v w ≤ min 1 (ε / (L0 + 1)) :=
      ciSup_le fun z => le_trans (min_le_right 1 _) (hvw z (Set.mem_univ z))
    have hb : |Φ v - Φ w| ≤ L0 * capDist v w := by
      rw [hΦdef]; exact abs_liftPhi_sub_le hΦ0 hL0 v w
    have h1 : L0 * min 1 (ε / (L0 + 1)) ≤ L0 * (ε / (L0 + 1)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hL0
    have h2 : L0 * (ε / (L0 + 1)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0:ℝ) < L0 + 1)]
      nlinarith
    calc |Φ v - Φ w| ≤ L0 * capDist v w := hb
      _ ≤ L0 * min 1 (ε / (L0 + 1)) := mul_le_mul_of_nonneg_left hcap hL0
      _ ≤ ε := le_trans h1 h2
  have hconv := tendsto_integral_of_fdd_of_equicontinuous'
      (f := fun (n : ℕ) (z : rewardBox T A) (ω : Site 2 → ℝ) =>
        orientedBoxReward T n ω (boxToFin T A z))
      (g := fun (z : rewardBox T A) (ω : contNoiseSpace) => Y (boxToFin T A z) ω)
      (P := fun _ : ℕ => iidLaw 2 (realLaw ν)) (Q := contNoiseLaw) (L := (atTop : Filter ℕ))
      (Φ := Φ) hK hfm hgm hgc hfΦm hfdd htight hΦb hΦu
  have hlhs : ∀ n, (∫ ω, Φ (fun z => orientedBoxReward T n ω (boxToFin T A z))
      ∂(iidLaw 2 (realLaw ν))) = ∫ G, Φ0 G ∂(boxRewardLaw T ν hT A hA n) := by
    intro n
    have hpt : ∀ ω, Φ (fun z : rewardBox T A => orientedBoxReward T n ω (boxToFin T A z))
        = Φ0 (boxRewardMap T hT A hA n ω) := by
      intro ω
      have hc : (fun z : rewardBox T A => orientedBoxReward T n ω (boxToFin T A z))
          = ⇑(boxRewardMap T hT A hA n ω) := rfl
      rw [hc]; exact hΦcoe _
    rw [integral_congr_ae (ae_of_all _ hpt)]
    exact (integral_map (measurable_boxRewardMap T hT A hA n).aemeasurable
      hΦ0lip.continuous.aestronglyMeasurable).symm
  have hrhs : (∫ ω, Φ (fun z => Y (boxToFin T A z) ω) ∂contNoiseLaw)
      = ∫ G, Φ0 G ∂(contBoxRewardLaw T hT A hA Y hYmeas hYcont) := by
    have hpt : ∀ ω, Φ (fun z : rewardBox T A => Y (boxToFin T A z) ω)
        = Φ0 (contBoxLimitMap T hT A hA Y hYcont ω) := by
      intro ω
      have hc : (fun z : rewardBox T A => Y (boxToFin T A z) ω)
          = ⇑(contBoxLimitMap T hT A hA Y hYcont ω) := rfl
      rw [hc]; exact hΦcoe _
    rw [integral_congr_ae (ae_of_all _ hpt)]
    exact (integral_map (measurable_contBoxLimitMap T hT A hA Y hYmeas hYcont).aemeasurable
      hΦ0lip.continuous.aestronglyMeasurable).symm
  have hfeq : (fun n => ∫ ω, Φ (fun z => orientedBoxReward T n ω (boxToFin T A z))
      ∂(iidLaw 2 (realLaw ν))) = fun n => ∫ G, Φ0 G ∂(boxRewardLaw T ν hT A hA n) :=
    funext hlhs
  rw [hfeq, hrhs] at hconv
  exact hconv

/-- **`hlaw`**: the discrete box-reward law converges weakly, against every bounded continuous
test functional, to the continuum box-reward law. -/
theorem hlaw_orientedBoxReward (ν : Measure ℤ) (hν : CriticalLaw ν)
    (hBinomial : External.BinomialLocalCLT) (hT : 0 ≤ T) (hA : 0 ≤ A)
    {Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ} (hYmeas : ∀ z, Measurable (Y z))
    (hYcont : ∀ ω, ContinuousOn (fun z => Y z ω) (orientedBox T A))
    (hYmod : ∀ z ∈ orientedBox T A,
      contZ (∫ x : ℝ, x ^ 2 ∂(realLaw ν)) T (z 0) (z 1) =ᵐ[contNoiseLaw] Y z) :
    ∀ Φ0 : BoundedContinuousFunction C(rewardBox T A, ℝ) ℝ,
      Tendsto (fun n => ∫ G, Φ0 G ∂(boxRewardLaw T ν hT A hA n)) atTop
        (𝓝 (∫ G, Φ0 G ∂(contBoxRewardLaw T hT A hA Y hYmeas hYcont))) := by
  haveI : IsProbabilityMeasure ν := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI : IsProbabilityMeasure (iidLaw 2 (realLaw ν)) := by unfold iidLaw; infer_instance
  set μs : ℕ → ProbabilityMeasure C(rewardBox T A, ℝ) := fun n =>
    ⟨boxRewardLaw T ν hT A hA n, inferInstance⟩ with hμs
  set μ : ProbabilityMeasure C(rewardBox T A, ℝ) :=
    ⟨contBoxRewardLaw T hT A hA Y hYmeas hYcont, inferInstance⟩ with hμdef
  have hconv : Tendsto μs atTop (𝓝 μ) := by
    rw [tendsto_iff_forall_lipschitz_integral_tendsto]
    intro f hfb hflip
    obtain ⟨M0, hM0⟩ := hfb
    obtain ⟨L0', hL0'⟩ := hflip
    have hΦ0 : ∀ G, |f G| ≤ M0 + |f 0| := by
      intro G
      have h := hM0 G 0
      rw [Real.dist_eq] at h
      have h2 := abs_sub_abs_le_abs_sub (f G) (f 0)
      linarith
    exact tendsto_integral_boxRewardLaw_of_lipschitz ν hν hBinomial hT hA hYmeas hYcont hYmod
      hΦ0 hL0'
  have hres := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv
  intro Φ0
  exact hres Φ0

end Parking

end
