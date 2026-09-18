/-
The Lyapunov `L^p → L²` step (task item (c)'s completion): from `Parking.
exists_yfieldSup3_moment`'s bound `E[yfieldSup3^p] ≤ D·(R+1)²`, Jensen's inequality at the
concave map `t ↦ t^(2/p)` (`Real.concaveOn_rpow`, `ConcaveOn.le_map_integral`, both already in
Mathlib) gives `E[yfieldSup3²] ≤ (D·(R+1)²)^(2/p)`.
-/
import Parking.Support.TightBoxSupSup3Moment

open MeasureTheory LatticeProb Filter Topology

noncomputable section

namespace Parking

/-- **`yfieldSup3` itself (not just its `p`-th power) is `AEStronglyMeasurable`.** -/
theorem aestronglyMeasurable_yfieldSup3 (ν : Measure ℤ) (hν : CriticalLaw ν) {A : ℝ} (hA : 0 ≤ A)
    (R n : ℕ) (hn : 1 ≤ n) :
    AEStronglyMeasurable (fun η : Site 2 → ℝ => yfieldSup3 A hA R n η) (iidLaw 2 (realLaw ν)) := by
  haveI : IsProbabilityMeasure ν := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI : IsProbabilityMeasure (iidLaw 2 (realLaw ν)) := by unfold iidLaw; infer_instance
  set G1 : (Site 2 → ℝ) → ℝ := fun η => ∑ s ∈ Finset.range R, levelIncFixed A hA R n (s+1) η
    with hG1def
  set G2 : (Site 2 → ℝ) → ℝ := fun η => LatticeProb.dtail (fun m => levelInc A hA n m η) R
    with hG2def
  set G0 : (Site 2 → ℝ) → ℝ := fun η => level0Max A hA R n η with hG0def
  have heqY : (fun η => yfieldSup3 A hA R n η) = fun η => G0 η + 2 * G1 η + 2 * G2 η := by
    funext η; rw [yfieldSup3]
  rw [heqY]
  have hG0meas : Measurable G0 := measurable_level0Max A hA R n
  have hG1meas : Measurable G1 :=
    Finset.measurable_fun_sum _ fun k _ => measurable_levelIncFixed A hA R n (k+1)
  have hG2aesm : AEStronglyMeasurable G2 (iidLaw 2 (realLaw ν)) := by
    set T : ℕ → (Site 2 → ℝ) → ℝ :=
      fun N η => ∑ k ∈ Finset.range (N+1), levelInc A hA n (R + 1 + k) η with hTdef
    have hTmeas : ∀ N, Measurable (T N) :=
      fun N => Finset.measurable_fun_sum _ fun k _ => measurable_levelInc A hA n (R+1+k)
    have hae_tendsto : ∀ᵐ η ∂(iidLaw 2 (realLaw ν)),
        Tendsto (fun N => T N η) atTop (𝓝 (G2 η)) := by
      filter_upwards [ae_summable_levelInc ν hν hA n hn R] with η hsum
      have hshift : Summable (fun k : ℕ => levelInc A hA n (R + 1 + k) η) := by
        have hs := (summable_nat_add_iff (R + 1)).mpr hsum
        refine hs.congr fun k => ?_
        congr 1
        omega
      have htendsto := hshift.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
      have hG2eq : G2 η = ∑' k : ℕ, levelInc A hA n (R + 1 + k) η := by
        show LatticeProb.dtail (fun m => levelInc A hA n m η) R = _
        simp only [LatticeProb.dtail]
        apply tsum_congr
        intro i
        congr 1
        omega
      rwa [hG2eq]
    exact aestronglyMeasurable_of_tendsto_ae atTop
      (fun N => (hTmeas N).aestronglyMeasurable) hae_tendsto
  exact (hG0meas.aestronglyMeasurable.add
    ((hG1meas.const_mul 2).aestronglyMeasurable)).add (hG2aesm.const_mul 2)

/-- **`E[yfieldSup3²] ≤ (D·(R+1)²)^(2/p)`, uniform in the scale `n`, for every `p > 12`, with `D`
itself bounded by `K * (1 + A) ^ (p / 2)` for a SINGLE constant `K`, chosen before `A` and
independent of it. -/
theorem exists_yfieldSup3_L2_moment (ν : Measure ℤ) (hν : CriticalLaw ν) (p : ℝ) (hp : 12 < p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ℝ) (hA : 0 ≤ A), ∃ D : ℝ, 0 ≤ D ∧ D ≤ K * (1 + A) ^ (p / 2) ∧
      ∀ (R n : ℕ), 1 ≤ n →
      Integrable (fun η : Site 2 → ℝ => (yfieldSup3 A hA R n η) ^ 2) (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, (yfieldSup3 A hA R n η) ^ 2 ∂(iidLaw 2 (realLaw ν))) ≤
        (D * (((R : ℝ) + 1) ^ 2)) ^ (2 / p) := by
  haveI : IsProbabilityMeasure ν := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI : IsProbabilityMeasure (iidLaw 2 (realLaw ν)) := by unfold iidLaw; infer_instance
  obtain ⟨K, hKnn, hKall⟩ := exists_yfieldSup3_moment ν hν p hp
  refine ⟨K, hKnn, fun A hA => ?_⟩
  obtain ⟨D, hDnn, hDbd, hbound⟩ := hKall A hA
  refine ⟨D, hDnn, hDbd, fun R n hn => ?_⟩
  obtain ⟨hYpint, hYpbound⟩ := hbound R n hn
  set Y : (Site 2 → ℝ) → ℝ := fun η => yfieldSup3 A hA R n η with hYdef
  have hYnn : ∀ η, 0 ≤ Y η := fun η => yfieldSup3_nonneg A hA R n η
  have hYaesm : AEStronglyMeasurable Y (iidLaw 2 (realLaw ν)) :=
    aestronglyMeasurable_yfieldSup3 ν hν hA R n hn
  have hp2 : (0:ℝ) ≤ 2 / p := by positivity
  have hp1 : 2 / p ≤ 1 := by
    rw [div_le_one (by linarith : (0:ℝ) < p)]; linarith
  have hg : ConcaveOn ℝ (Set.Ici (0:ℝ)) (fun y : ℝ => y ^ (2/p)) := Real.concaveOn_rpow hp2 hp1
  have hgc : ContinuousOn (fun y : ℝ => y ^ (2/p)) (Set.Ici (0:ℝ)) :=
    continuousOn_id.rpow_const (fun x _ => Or.inr hp2)
  have hp0 : p ≠ 0 := by linarith
  have hsq_eq : ∀ η, (Y η ^ p) ^ (2/p) = (Y η) ^ 2 := by
    intro η
    rw [← Real.rpow_natCast (Y η) 2, ← Real.rpow_mul (hYnn η)]
    congr 1
    push_cast
    field_simp
  have hYpmem : ∀ᵐ η ∂(iidLaw 2 (realLaw ν)), (Y η) ^ p ∈ Set.Ici (0:ℝ) := by
    filter_upwards with η
    exact Real.rpow_nonneg (hYnn η) p
  have hYsq_le_aux : ∀ η, (Y η) ^ 2 ≤ 1 + (Y η) ^ p := by
    intro η
    rcases le_total (Y η) (1:ℝ) with h | h
    · have h1 : (Y η) ^ 2 ≤ 1 := by nlinarith [hYnn η, sq_nonneg (Y η - 1), sq_nonneg (Y η)]
      have h2 : (0:ℝ) ≤ (Y η) ^ p := Real.rpow_nonneg (hYnn η) p
      linarith
    · have hcast : (Y η) ^ (2:ℝ) = (Y η) ^ (2:ℕ) := by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      have h2' : (Y η) ^ (2:ℝ) ≤ (Y η) ^ p :=
        Real.rpow_le_rpow_of_exponent_le h (by linarith)
      rw [hcast] at h2'
      have h3 : (0:ℝ) ≤ (Y η) ^ p := Real.rpow_nonneg (hYnn η) p
      linarith
  have hYsq_int : Integrable (fun η => (Y η) ^ 2) (iidLaw 2 (realLaw ν)) := by
    have hmeas : AEStronglyMeasurable (fun η => (Y η) ^ 2) (iidLaw 2 (realLaw ν)) :=
      (continuous_pow 2).comp_aestronglyMeasurable hYaesm
    refine Integrable.mono' ((integrable_const (1:ℝ)).add hYpint) hmeas ?_
    filter_upwards with η
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Y η))]
    exact hYsq_le_aux η
  refine ⟨hYsq_int, ?_⟩
  have hgi : Integrable ((fun y : ℝ => y ^ (2/p)) ∘ (fun η => (Y η) ^ p))
      (iidLaw 2 (realLaw ν)) := by
    have heq : ((fun y : ℝ => y ^ (2/p)) ∘ (fun η => (Y η) ^ p)) = fun η => (Y η) ^ 2 := by
      funext η; exact hsq_eq η
    rw [heq]; exact hYsq_int
  have hjensen := hg.le_map_integral hgc (isClosed_Ici) hYpmem hYpint hgi
  have heq2 : (∫ η, (Y η ^ p) ^ (2/p) ∂(iidLaw 2 (realLaw ν))) =
      ∫ η, (Y η) ^ 2 ∂(iidLaw 2 (realLaw ν)) := by
    apply integral_congr_ae
    filter_upwards with η
    exact hsq_eq η
  rw [heq2] at hjensen
  refine hjensen.trans ?_
  have hYpnn : (0:ℝ) ≤ ∫ η, (Y η) ^ p ∂(iidLaw 2 (realLaw ν)) :=
    integral_nonneg fun η => Real.rpow_nonneg (hYnn η) p
  exact Real.rpow_le_rpow hYpnn hYpbound hp2

end Parking

end
