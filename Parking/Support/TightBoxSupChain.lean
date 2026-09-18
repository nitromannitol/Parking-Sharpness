/-
The a.e. summability of `Parking.levelInc`'s dyadic increments, from
`Parking/Support/TightBoxSupTail.lean`'s geometric-tail moment bound.  This is the
prerequisite for applying the library's telescoping lemmas
(`LatticeProb.dtruncPi_step`, `LatticeProb.dlimPi_sub_dtruncPi_le`,
`LatticeProb.dlimPi_eq_of_continuous`): they need `Summable a` for the level
sequence `a`, and the only way to get that from a UNIFORM (in the range `N`) `L^p` bound is a
Fatou/monotone-convergence argument, not a Borel-Cantelli one.

The route: `T_N(η) := ∑_{k < N+1} levelInc(n1+1+k, η)` is monotone nondecreasing and nonnegative
in `N`, with `E[(T_N)^{16}] ≤ C` UNIFORM IN `N`
(`Parking.exists_levelInc_tail_moment`).  Monotone convergence for the lintegral
(`MeasureTheory.lintegral_iSup`) gives `∫⁻ (⨆_N ofReal(T_N^{16})) ≤ ofReal C < ∞`, so
`MeasureTheory.ae_lt_top` gives `⨆_N T_N(η)^{16} < ∞` for a.e. `η` — i.e. the partial sums
`T_N(η)` are (for a.e. `η`) bounded by a SINGLE finite constant, uniformly in `N`, which is
exactly what `summable_of_sum_range_le` needs.
-/
import Parking.Support.TightBoxSupTail

open MeasureTheory LatticeProb Filter Topology
open scoped ENNReal

noncomputable section

namespace Parking

/-- **`Parking.levelInc` is measurable in the scenery, at every scale and level.** -/
theorem measurable_levelInc (A : ℝ) (hA : 0 ≤ A) (n m : ℕ) :
    Measurable (fun η : Site 2 → ℝ => levelInc A hA n m η) := by
  have heq : (fun η : Site 2 → ℝ => levelInc A hA n m η) =
      (levelPairs m).sup' (levelPairs_nonempty m)
        (fun idx (η : Site 2 → ℝ) => levelIncTerm A hA n m η idx) := by
    funext η
    simp only [levelInc_eq_sup', Finset.sup'_apply]
  rw [heq]
  apply Finset.measurable_sup'
  intro idx _
  exact ((measurable_Yfield hA n
    (LatticeProb.gridPt m (idx.1 + Pi.single idx.2 1))).sub
    (measurable_Yfield hA n (LatticeProb.gridPt m idx.1))).abs

/-- **The dyadic increment sequence of `Yfield`, starting after any fixed level `n1`, is
SUMMABLE for a.e. scenery `η`, uniformly in the scale `n`.** -/
theorem ae_summable_levelInc (ν : Measure ℤ) (hν : CriticalLaw ν) {A : ℝ} (hA : 0 ≤ A)
    (n : ℕ) (hn : 1 ≤ n) (n1 : ℕ) :
    ∀ᵐ η ∂(iidLaw 2 (realLaw ν)), Summable (fun m : ℕ => levelInc A hA n m η) := by
  haveI : IsProbabilityMeasure ν := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI : IsProbabilityMeasure (iidLaw 2 (realLaw ν)) := by unfold iidLaw; infer_instance
  obtain ⟨K, _hKnn, hKall⟩ := exists_levelInc_tail_moment ν hν 16 (by norm_num) n1
  obtain ⟨C, _hCnn, _hCbd, hbound⟩ := hKall A hA
  set T : ℕ → (Site 2 → ℝ) → ℝ :=
      fun N η => ∑ k ∈ Finset.range (N + 1), levelInc A hA n (n1 + 1 + k) η with hTdef
  have hTnn : ∀ N η, 0 ≤ T N η :=
    fun N η => Finset.sum_nonneg fun k _ => levelInc_nonneg A hA n (n1 + 1 + k) η
  have hTmono : ∀ η, Monotone (fun N => T N η) := by
    intro η N1 N2 hle
    show (∑ k ∈ Finset.range (N1 + 1), levelInc A hA n (n1 + 1 + k) η) ≤
      ∑ k ∈ Finset.range (N2 + 1), levelInc A hA n (n1 + 1 + k) η
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (show N1 + 1 ≤ N2 + 1 by omega))
      (fun k _ _ => levelInc_nonneg A hA n (n1 + 1 + k) η)
  have hTmeas : ∀ N, Measurable (T N) :=
    fun N => Finset.measurable_fun_sum _ fun k _ => measurable_levelInc A hA n (n1 + 1 + k)
  set G : ℕ → (Site 2 → ℝ) → ℝ≥0∞ := fun N η => ENNReal.ofReal ((T N η) ^ (16 : ℝ)) with hGdef
  have hGmeas : ∀ N, Measurable (G N) := by
    intro N
    have heq : G N = fun η => ENNReal.ofReal (|T N η| ^ (16 : ℝ)) := by
      funext η
      rw [hGdef, abs_of_nonneg (hTnn N η)]
    rw [heq]
    exact ENNReal.measurable_ofReal.comp (LatticeProb.measurable_abs_rpow (hTmeas N) 16)
  have hGmono : Monotone G := by
    intro N1 N2 hle η
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (hTnn N1 η) (hTmono η hle) (by norm_num))
  have hlint_bound : ∀ N, (∫⁻ η, G N η ∂(iidLaw 2 (realLaw ν))) ≤ ENNReal.ofReal C := by
    intro N
    obtain ⟨hTint, hTintegral_bound⟩ := hbound n N hn
    have heq : (∫⁻ η, G N η ∂(iidLaw 2 (realLaw ν))) =
        ENNReal.ofReal (∫ η, (T N η) ^ (16 : ℝ) ∂(iidLaw 2 (realLaw ν))) := by
      rw [hGdef]
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hTint
        (Filter.Eventually.of_forall fun η => Real.rpow_nonneg (hTnn N η) 16)).symm
    rw [heq]
    exact ENNReal.ofReal_le_ofReal hTintegral_bound
  have hlint_iSup : (∫⁻ η, (⨆ N, G N η) ∂(iidLaw 2 (realLaw ν))) ≤ ENNReal.ofReal C := by
    rw [MeasureTheory.lintegral_iSup hGmeas hGmono]
    exact iSup_le hlint_bound
  have hne : (∫⁻ η, (⨆ N, G N η) ∂(iidLaw 2 (realLaw ν))) ≠ ⊤ :=
    (lt_of_le_of_lt hlint_iSup ENNReal.ofReal_lt_top).ne
  have hae_finite : ∀ᵐ η ∂(iidLaw 2 (realLaw ν)), (⨆ N, G N η) < ⊤ :=
    MeasureTheory.ae_lt_top (Measurable.iSup hGmeas) hne
  filter_upwards [hae_finite] with η hη
  set M : ℝ≥0∞ := ⨆ N, G N η with hMdef
  have hMbound : ∀ N, G N η ≤ M := fun N => le_iSup (fun N => G N η) N
  have hL : ∀ N, (T N η) ^ (16 : ℝ) ≤ M.toReal := by
    intro N
    have h1 := hMbound N
    rw [hGdef] at h1
    exact (ENNReal.ofReal_le_iff_le_toReal hη.ne).mp h1
  set L : ℝ := M.toReal ^ ((1 : ℝ) / 16) with hLdef
  have hLbound : ∀ N, T N η ≤ L := by
    intro N
    have hnn16 : (0 : ℝ) ≤ (T N η) ^ (16 : ℝ) := Real.rpow_nonneg (hTnn N η) 16
    have hstep : ((T N η) ^ (16 : ℝ)) ^ ((1 : ℝ) / 16) ≤ M.toReal ^ ((1 : ℝ) / 16) :=
      Real.rpow_le_rpow hnn16 (hL N) (by norm_num)
    rw [hLdef]
    refine le_trans (le_of_eq ?_) hstep
    rw [← Real.rpow_mul (hTnn N η), show (16:ℝ) * ((1:ℝ)/16) = 1 by norm_num, Real.rpow_one]
  have hsummable_shift : Summable (fun k : ℕ => levelInc A hA n (n1 + 1 + k) η) := by
    apply summable_of_sum_range_le (fun k => levelInc_nonneg A hA n (n1 + 1 + k) η)
    intro N
    calc ∑ k ∈ Finset.range N, levelInc A hA n (n1 + 1 + k) η
        ≤ ∑ k ∈ Finset.range (N + 1), levelInc A hA n (n1 + 1 + k) η :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.mpr (show N ≤ N + 1 by omega))
            (fun k _ _ => levelInc_nonneg A hA n (n1 + 1 + k) η)
      _ = T N η := rfl
      _ ≤ L := hLbound N
  have hshift_eq : (fun k : ℕ => levelInc A hA n (n1 + 1 + k) η) =
      (fun k : ℕ => (fun m => levelInc A hA n m η) (k + (n1 + 1))) := by
    funext k
    congr 1
    omega
  rw [hshift_eq] at hsummable_shift
  exact (summable_nat_add_iff (n1 + 1)).mp hsummable_shift

end Parking

end
