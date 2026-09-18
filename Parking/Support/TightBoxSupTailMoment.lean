/-
An INTEGRAL bound `E[dtail(levelInc, n1)^p] ≤ C` on `Parking.levelInc`'s dyadic tail, not just
the a.e. finiteness `Parking.ae_summable_levelInc` gives.  The integral form is what the
Lyapunov and Cauchy-Schwarz step downstream needs.  Same Fatou/monotone-convergence
technique as `TightBoxSupChain.lean`'s `ae_summable_levelInc`, carried one step further: since
the partial sums `T_N` are monotone and converge a.e. to `dtail`, `⨆_N T_N^p` equals `dtail^p`
a.e., so the ALREADY-PROVEN uniform-in-`N` lintegral bound on `T_N^p` transfers to `dtail^p`.
-/
import Parking.Support.TightBoxSupChain

open MeasureTheory LatticeProb Filter Topology
open scoped ENNReal

noncomputable section

namespace Parking

/-- **The `p`-th moment of `Parking.levelInc`'s dyadic tail is bounded, uniformly in the scale
`n`**, with the constant itself bounded by `K * (1 + A) ^ (p / 2)` for a SINGLE constant `K`,
chosen before `A` and independent of it. -/
theorem exists_dtail_moment (ν : Measure ℤ) (hν : CriticalLaw ν) (n1 : ℕ) (p : ℝ) (hp : 12 < p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ℝ) (hA : 0 ≤ A), ∃ C : ℝ, 0 ≤ C ∧ C ≤ K * (1 + A) ^ (p / 2) ∧
      ∀ (n : ℕ), 1 ≤ n →
      Integrable (fun η : Site 2 → ℝ =>
          (LatticeProb.dtail (fun m => levelInc A hA n m η) n1) ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, (LatticeProb.dtail (fun m => levelInc A hA n m η) n1) ^ p
          ∂(iidLaw 2 (realLaw ν))) ≤ C := by
  haveI : IsProbabilityMeasure ν := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI : IsProbabilityMeasure (iidLaw 2 (realLaw ν)) := by unfold iidLaw; infer_instance
  obtain ⟨K, hKnn, hKall⟩ := exists_levelInc_tail_moment ν hν p (by linarith) n1
  refine ⟨K, hKnn, fun A hA => ?_⟩
  obtain ⟨C, hCnn, hCbd, hbound⟩ := hKall A hA
  refine ⟨C, hCnn, hCbd, fun n hn => ?_⟩
  set T : ℕ → (Site 2 → ℝ) → ℝ :=
      fun N η => ∑ k ∈ Finset.range (N + 1), levelInc A hA n (n1 + 1 + k) η with hTdef
  set D : (Site 2 → ℝ) → ℝ := fun η => LatticeProb.dtail (fun m => levelInc A hA n m η) n1
    with hDdef
  have hDeq : ∀ η, D η = ∑' k : ℕ, levelInc A hA n (n1 + 1 + k) η := by
    intro η
    simp only [hDdef, LatticeProb.dtail]
    apply tsum_congr
    intro i
    congr 1
    omega
  have hDnn : ∀ η, 0 ≤ D η := by
    intro η
    rw [hDdef]
    exact LatticeProb.dtail_nonneg (fun m => levelInc_nonneg A hA n m η) n1
  have hTnn : ∀ N η, 0 ≤ T N η :=
    fun N η => Finset.sum_nonneg fun k _ => levelInc_nonneg A hA n (n1 + 1 + k) η
  have hTmono : ∀ η, Monotone (fun N => T N η) := by
    intro η N1 N2 hle
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (show N1 + 1 ≤ N2 + 1 by omega))
      (fun k _ _ => levelInc_nonneg A hA n (n1 + 1 + k) η)
  have hTmeas : ∀ N, Measurable (T N) :=
    fun N => Finset.measurable_fun_sum _ fun k _ => measurable_levelInc A hA n (n1 + 1 + k)
  have hae_tendsto : ∀ᵐ η ∂(iidLaw 2 (realLaw ν)), Tendsto (fun N => T N η) atTop (𝓝 (D η)) := by
    filter_upwards [ae_summable_levelInc ν hν hA n hn n1] with η hsummable
    have hshift : Summable (fun k : ℕ => levelInc A hA n (n1 + 1 + k) η) := by
      have hs := (summable_nat_add_iff (n1 + 1)).mpr hsummable
      refine hs.congr fun k => ?_
      congr 1
      omega
    have htendsto := hshift.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    rwa [← hDeq η] at htendsto
  have hae_pow_tendsto : ∀ᵐ η ∂(iidLaw 2 (realLaw ν)),
      Tendsto (fun N => (T N η) ^ p) atTop (𝓝 ((D η) ^ p)) := by
    filter_upwards [hae_tendsto] with η hη
    exact (Real.continuousAt_rpow_const (D η) p (Or.inr (by linarith))).tendsto.comp hη
  set G : ℕ → (Site 2 → ℝ) → ℝ≥0∞ := fun N η => ENNReal.ofReal ((T N η) ^ p) with hGdef
  have hGmeas : ∀ N, Measurable (G N) := by
    intro N
    have heq : G N = fun η => ENNReal.ofReal (|T N η| ^ p) := by
      funext η
      rw [hGdef, abs_of_nonneg (hTnn N η)]
    rw [heq]
    exact ENNReal.measurable_ofReal.comp (LatticeProb.measurable_abs_rpow (hTmeas N) p)
  have hGmono : Monotone G := by
    intro N1 N2 hle η
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (hTnn N1 η) (hTmono η hle) (by linarith))
  have hae_iSup : ∀ᵐ η ∂(iidLaw 2 (realLaw ν)), (⨆ N, G N η) = ENNReal.ofReal ((D η) ^ p) := by
    filter_upwards [hae_pow_tendsto] with η hη
    have hGtendsto : Tendsto (fun N => G N η) atTop (𝓝 (ENNReal.ofReal ((D η) ^ p))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp hη
    have hGmonoη : Monotone (fun N => G N η) := fun N1 N2 hle => hGmono hle η
    exact tendsto_nhds_unique (tendsto_atTop_iSup hGmonoη) hGtendsto
  have hlint_bound : ∀ N, (∫⁻ η, G N η ∂(iidLaw 2 (realLaw ν))) ≤ ENNReal.ofReal C := by
    intro N
    obtain ⟨hTint, hTintegral_bound⟩ := hbound n N hn
    have heq : (∫⁻ η, G N η ∂(iidLaw 2 (realLaw ν))) =
        ENNReal.ofReal (∫ η, (T N η) ^ p ∂(iidLaw 2 (realLaw ν))) := by
      rw [hGdef]
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hTint
        (Filter.Eventually.of_forall fun η => Real.rpow_nonneg (hTnn N η) p)).symm
    rw [heq]
    exact ENNReal.ofReal_le_ofReal hTintegral_bound
  have hlint_iSup : (∫⁻ η, (⨆ N, G N η) ∂(iidLaw 2 (realLaw ν))) ≤ ENNReal.ofReal C := by
    rw [MeasureTheory.lintegral_iSup hGmeas hGmono]
    exact iSup_le hlint_bound
  have hlint_D : (∫⁻ η, ENNReal.ofReal ((D η) ^ p) ∂(iidLaw 2 (realLaw ν))) ≤ ENNReal.ofReal C := by
    have hcongr : (∫⁻ η, ENNReal.ofReal ((D η) ^ p) ∂(iidLaw 2 (realLaw ν))) =
        ∫⁻ η, (⨆ N, G N η) ∂(iidLaw 2 (realLaw ν)) := by
      apply lintegral_congr_ae
      filter_upwards [hae_iSup] with η hη
      rw [hη]
    rw [hcongr]
    exact hlint_iSup
  have hTpowMeas : ∀ N, Measurable (fun η => (T N η) ^ p) := by
    intro N
    have heq : (fun η => (T N η) ^ p) = (fun η => |T N η| ^ p) := by
      funext η; rw [abs_of_nonneg (hTnn N η)]
    rw [heq]
    exact LatticeProb.measurable_abs_rpow (hTmeas N) p
  have haesm : AEStronglyMeasurable (fun η => (D η) ^ p) (iidLaw 2 (realLaw ν)) :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun N => (hTpowMeas N).aestronglyMeasurable) hae_pow_tendsto
  have hfnn : 0 ≤ᵐ[iidLaw 2 (realLaw ν)] fun η => (D η) ^ p :=
    Filter.Eventually.of_forall fun η => Real.rpow_nonneg (hDnn η) p
  have hDintPow : Integrable (fun η => (D η) ^ p) (iidLaw 2 (realLaw ν)) :=
    ⟨haesm, (MeasureTheory.hasFiniteIntegral_iff_ofReal hfnn).mpr
      (lt_of_le_of_lt hlint_D ENNReal.ofReal_lt_top)⟩
  refine ⟨hDintPow, ?_⟩
  have heq : (∫⁻ η, ENNReal.ofReal ((D η) ^ p) ∂(iidLaw 2 (realLaw ν))) =
      ENNReal.ofReal (∫ η, (D η) ^ p ∂(iidLaw 2 (realLaw ν))) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hDintPow hfnn).symm
  rw [heq] at hlint_D
  exact (ENNReal.ofReal_le_ofReal_iff hCnn).mp hlint_D

end Parking

end
