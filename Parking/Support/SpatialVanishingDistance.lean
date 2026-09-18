/-
The vanishing-distance clause of `prop:spatial-scaling` (`parking.tex:1712-1714`,
the mutual local uniform closeness of the two rescaled odometers), proved by a union
bound over a finite space-time mesh transferring the sealed `prop:discrepancy` (a tail
bound at the single site `0`) to every point of a compact set of positive times, via
`Parking.law_discrepancy_shift` (`UDivisibleShift.lean`) and
`Parking.exists_meanu_growth_bounds` (`MeanuGrowthBounds.lean`).  It needs
`Parking.External.GreenNorms`, the same input carried by `prop:discrepancy` itself.
-/
import Parking.Support.SpatialTightnessBridge
import Parking.Support.UDivisibleShift
import Parking.Support.MeanuGrowthBounds
import Parking.Support.BoxTranslation
import Parking.Support.MatchedUniform
import Parking.Frozen.Discrepancy
import Parking.Support.NearestLimit

noncomputable section

namespace Parking

open MeasureTheory LatticeProb Finset Filter Topology

variable {d : ℕ}

/-! ### A real-variable estimate: polynomial growth is beaten by the log-Gaussian tail -/

/-- For any real exponent `k` and any `c > 0`, `x ^ k` is eventually dominated by
`exp(-c(log x)^2)`'s reciprocal decay: the product tends to `0`. -/
theorem tendsto_rpow_mul_exp_neg_log_sq_atTop (k c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => x ^ k * Real.exp (-(c * Real.log x ^ 2))) atTop (𝓝 0) := by
  have hbound : ∀ᶠ x : ℝ in atTop, x ^ k * Real.exp (-(c * Real.log x ^ 2)) ≤ x ^ (-2 : ℝ) := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop ((k + 2) / c),
      eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hxc : (k + 2) ≤ c * Real.log x := by
      rw [div_le_iff₀ hc] at hx; linarith
    have hstep : (k + 2) * Real.log x ≤ c * Real.log x ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hxc hlog0
      nlinarith [h]
    have hexp : Real.exp (-(c * Real.log x ^ 2)) ≤ Real.exp (-((k + 2) * Real.log x)) :=
      Real.exp_le_exp.mpr (by linarith)
    have heq : Real.exp (-((k + 2) * Real.log x)) = x ^ (-(k + 2)) := by
      rw [Real.rpow_def_of_pos hx0]; ring_nf
    have hxk : x ^ k * x ^ (-(k + 2) : ℝ) = x ^ (-2 : ℝ) := by
      rw [← Real.rpow_add hx0]; ring_nf
    calc x ^ k * Real.exp (-(c * Real.log x ^ 2))
        ≤ x ^ k * Real.exp (-((k + 2) * Real.log x)) :=
          mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hx0.le _)
      _ = x ^ k * x ^ (-(k + 2) : ℝ) := by rw [heq]
      _ = x ^ (-2 : ℝ) := hxk
  apply tendsto_order.mpr
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx1
    exact ha.trans_le (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hx1) _) (Real.exp_pos _).le)
  · have hlt : ∀ᶠ x : ℝ in atTop, x ^ (-2 : ℝ) < b :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).eventually (Iio_mem_nhds hb)
    filter_upwards [hbound, hlt] with x h1 h2
    exact lt_of_le_of_lt h1 h2

/-! ### A uniform positive lower bound on the time coordinate of a compact set -/

/-- A compact set of positive times has a positive uniform lower time bound, no larger
than the set's own bounding radius `max C 1`. -/
theorem exists_time_bounds (K : Set (ℝ × (Fin d → ℝ))) (hK : IsCompact K)
    (hpos : ∀ p ∈ K, 0 < p.1) (C : ℝ) (hKC : ∀ p ∈ K, |p.1| ≤ C) :
    ∃ s : ℝ, 0 < s ∧ s ≤ max C 1 ∧ ∀ p ∈ K, s ≤ p.1 := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨1, one_pos, le_max_right _ _, fun p hp => absurd hp (hKe ▸ Set.notMem_empty p)⟩
  · obtain ⟨p₀, hp₀, hmin⟩ := hK.exists_isMinOn hKne continuous_fst.continuousOn
    rw [isMinOn_iff] at hmin
    refine ⟨p₀.1, hpos p₀ hp₀, ?_, hmin⟩
    exact (le_abs_self _).trans (hKC p₀ hp₀) |>.trans (le_max_left _ _)

/-! ### The mesh membership of a single point of a compact set -/

/-- A point `p` of a compact set `K`, bounded by `C`, lands at time `⌊p.1 R²⌋₊` in the
mesh's time range, for `R ≥ 0` and `s ≤ p.1 ≤ Cs`. -/
theorem floor_mul_sq_mem_Icc {s p1 Cs R : ℝ} (hs : s ≤ p1) (hp1C : p1 ≤ Cs) :
    ⌊s * R ^ 2⌋₊ ≤ ⌊p1 * R ^ 2⌋₊ ∧ ⌊p1 * R ^ 2⌋₊ ≤ ⌈Cs * R ^ 2⌉₊ := by
  have hR2 : (0 : ℝ) ≤ R ^ 2 := sq_nonneg R
  exact ⟨Nat.floor_le_floor (by nlinarith),
    (Nat.floor_le_floor (by nlinarith)).trans (Nat.floor_le_ceil _)⟩

/-- A spatial point bounded by `C` lands, after rescaling by `R ≥ 0`, in the sup-norm box
of radius `⌈C R⌉₊ + 1` about the origin. -/
theorem latticePoint_mem_boxFinset {C R : ℝ} (hR : 0 ≤ R) {x : Fin d → ℝ}
    (hx : ∀ i, |x i| ≤ C) :
    latticePoint R x ∈ boxFinset (0 : Site d) (⌈C * R⌉₊ + 1) := by
  rw [mem_boxFinset_iff]
  intro i
  have hxi : |R * x i| ≤ C * R := by
    rw [abs_mul, abs_of_nonneg hR, mul_comm]
    exact mul_le_mul_of_nonneg_right (hx i) hR
  have h1 : (⌊R * x i⌋ : ℝ) ≤ C * R := le_trans (Int.floor_le _) (le_trans (le_abs_self _) hxi)
  have h2 : -(C * R) - 1 ≤ (⌊R * x i⌋ : ℝ) := by
    have := Int.sub_one_lt_floor (R * x i)
    have h3 : -(C * R) ≤ R * x i := neg_le_of_abs_le hxi
    linarith
  have hcr : (C * R : ℝ) ≤ ((⌈C * R⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  simp only [latticePoint, Pi.zero_apply, sub_zero]
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have : -(((⌈C * R⌉₊ + 1 : ℕ) : ℝ)) ≤ (⌊R * x i⌋ : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have : (⌊R * x i⌋ : ℝ) ≤ ((⌈C * R⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

/-! ### The mesh cardinality, as a polynomial in `R` -/

/-- The space-time mesh's cardinality, `R ≥ 1`, is bounded by a constant times `R^{d+2}`,
for ANY lower time endpoint `nMin` (the bound drops the `- nMin` term, so it holds
regardless of `nMin`'s value). -/
theorem mesh_card_le (nMin : ℕ) (Cs R : ℝ) (hCs1 : 1 ≤ Cs) (hR1 : 1 ≤ R) :
    (((Finset.Icc nMin (⌈Cs * R ^ 2⌉₊)) ×ˢ
        (boxFinset (0 : Site d) (⌈Cs * R⌉₊ + 1))).card : ℝ)
      ≤ (Cs + 2) * (2 * Cs + 5) ^ d * R ^ (d + 2) := by
  have hR0 : (0:ℝ) ≤ R := zero_le_one.trans hR1
  have hCs0 : (0:ℝ) ≤ Cs := zero_le_one.trans hCs1
  rw [Finset.card_product, card_boxFinset, Nat.card_Icc, Nat.cast_mul, Nat.cast_pow]
  have hfact1 : ((⌈Cs * R ^ 2⌉₊ + 1 - nMin : ℕ) : ℝ) ≤ (Cs + 2) * R ^ 2 := by
    have hle : ⌈Cs * R ^ 2⌉₊ + 1 - nMin ≤ ⌈Cs * R ^ 2⌉₊ + 1 := Nat.sub_le _ _
    have hcast : ((⌈Cs * R ^ 2⌉₊ + 1 - nMin : ℕ) : ℝ)
        ≤ ((⌈Cs * R ^ 2⌉₊ : ℕ) : ℝ) + 1 := by exact_mod_cast hle
    have hnmax : ((⌈Cs * R ^ 2⌉₊ : ℕ) : ℝ) < Cs * R ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    have hR2 : (1:ℝ) ≤ R ^ 2 := one_le_pow₀ hR1
    nlinarith [hcast, hnmax]
  have hfact2 : (((2 * (⌈Cs * R⌉₊ + 1) + 1 : ℕ)) : ℝ) ^ d ≤ ((2 * Cs + 5) * R) ^ d := by
    have hmmax : ((⌈Cs * R⌉₊ : ℕ) : ℝ) < Cs * R + 1 := Nat.ceil_lt_add_one (by positivity)
    have hb : ((2 * (⌈Cs * R⌉₊ + 1) + 1 : ℕ) : ℝ) ≤ (2 * Cs + 5) * R := by
      push_cast; nlinarith [hmmax, hR1]
    exact pow_le_pow_left₀ (by positivity) hb d
  calc (((⌈Cs * R ^ 2⌉₊ + 1 - nMin : ℕ)) : ℝ)
        * (((2 * (⌈Cs * R⌉₊ + 1) + 1 : ℕ)) : ℝ) ^ d
      ≤ (Cs + 2) * R ^ 2 * ((2 * Cs + 5) * R) ^ d :=
        mul_le_mul hfact1 hfact2 (by positivity) (by positivity)
    _ = (Cs + 2) * (2 * Cs + 5) ^ d * R ^ (d + 2) := by
        rw [mul_pow, pow_add]; ring

/-! ### The main theorem: the vanishing-distance clause, via a union bound over the mesh -/

/-- **The mutual local uniform closeness, in probability, of the two rescaled odometers**
(`parking.tex:1712-1714`, the vanishing-distance clause of `prop:spatial-scaling`), via a
union bound over a finite space-time mesh, transferring the sealed `prop:discrepancy`. -/
theorem exists_spatial_vanishing_distance (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : Parking.External.SandpileGrowth) (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration) (hGreenNorms : Parking.External.GreenNorms)
    (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    ∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → (∀ p ∈ K, 0 < p.1) → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun R : ℝ => ((Parking.law d ν) {w | ε < ⨆ p ∈ K,
          |Parking.barOdometer w R p.1 p.2 - Parking.barDivisible w R p.1 p.2|}).toReal)
        atTop (𝓝 0) := by
  intro K hK hKpos ε hε
  haveI := hν.prob
  haveI := Parking.law_isProb hd ν
  obtain ⟨C, hC0, hKC⟩ := exists_radius_of_isCompact K hK
  obtain ⟨s_min, hs_min_pos, hs_minCs, hs_min⟩ :=
    exists_time_bounds K hK hKpos C (fun p hp => (hKC p hp).1)
  set Cs : ℝ := max C 1 with hCs_def
  have hCs1 : (1 : ℝ) ≤ Cs := le_max_right _ _
  have hCs0 : (0 : ℝ) ≤ Cs := zero_le_one.trans hCs1
  have hCsC : C ≤ Cs := le_max_left _ _
  obtain ⟨b, B, hb, hB, hgrowth⟩ := exists_meanu_growth_bounds hGrowth d hd hd3 ν hν
  have hmonoM := meanu_monotone d hd ν hν
  have hexppos : (0 : ℝ) < (Cs + 1) ^ ((4 - (d : ℝ)) / 4) := Real.rpow_pos_of_pos (by linarith) _
  set ε'' : ℝ := ε / (B * (Cs + 1) ^ ((4 - (d : ℝ)) / 4)) with hε''_def
  have hε''pos : 0 < ε'' := div_pos hε (mul_pos hB hexppos)
  obtain ⟨Cdisc, hCdiscpos, hmomdisc, htaildisc⟩ :=
    Parking.Frozen.discrepancy hGrowth hBernstein hConcentration hGreenNorms d hd hd3 ν hν
  obtain ⟨c, hc, N, hdisc⟩ := htaildisc ε'' hε''pos
  set D1 : ℝ := (Cs + 2) * (2 * Cs + 5) ^ d with hD1_def
  have hD1pos : 0 < D1 := by positivity
  apply Parking.tendsto_zero_of_eventual_small _ _ (fun _ => ENNReal.toReal_nonneg)
  intro ε' hε'
  have hεD1 : 0 < ε' / D1 := div_pos hε' hD1pos
  set k : ℝ := (((d : ℕ) + 2 : ℕ) : ℝ) with hk_def
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_mul_exp_neg_log_sq_atTop k c hc).eventually (Iio_mem_nhds hεD1))
  set R₀ : ℝ := max 2 (max (4 / s_min) (max x₀ (N : ℝ))) with hR₀_def
  filter_upwards [eventually_ge_atTop R₀] with R hR
  have hR2 : (2:ℝ) ≤ R := le_trans (le_max_left _ _) hR
  have hR1 : (1:ℝ) ≤ R := le_trans (by norm_num) hR2
  have hR4 : 4 / s_min ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR
  have hRx0 : x₀ ≤ R := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hR
  have hRN : (N:ℝ) ≤ R := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hR
  have hR0 : (0:ℝ) ≤ R := zero_le_one.trans hR1
  have hs4 : (4:ℝ) ≤ s_min * R := by
    rw [mul_comm]; exact (div_le_iff₀ hs_min_pos).mp hR4
  have hRpos : (0:ℝ) < R := lt_of_lt_of_le one_pos hR1
  have hpow_pos : (0:ℝ) < R ^ ((d:ℝ) / 2 - 2) := Real.rpow_pos_of_pos hRpos _
  set nMin : ℕ := ⌊s_min * R ^ 2⌋₊ with hnMin_def
  set nMax : ℕ := ⌈Cs * R ^ 2⌉₊ with hnMax_def
  set mMax : ℕ := ⌈Cs * R⌉₊ + 1 with hmMax_def
  set mesh : Finset (ℕ × Site d) := Finset.Icc nMin nMax ×ˢ boxFinset (0 : Site d) mMax
    with hmesh_def
  have hnMinR : R ≤ (nMin : ℝ) := by
    have h1 : s_min * R ^ 2 < (nMin : ℝ) + 1 := Nat.lt_floor_add_one _
    nlinarith [h1, hs4, hR1]
  have hnMinx0 : x₀ ≤ (nMin : ℝ) := hRx0.trans hnMinR
  have hnMinN : N ≤ nMin := by
    have h : (N : ℝ) ≤ (nMin : ℝ) := hRN.trans hnMinR
    exact_mod_cast h
  have hnMin1 : 1 ≤ nMin := by
    have h : (1 : ℝ) ≤ (nMin : ℝ) := hR1.trans hnMinR
    exact_mod_cast h
  have hnMin2 : 2 ≤ nMin := by
    have h : (2 : ℝ) ≤ (nMin : ℝ) := hR2.trans hnMinR
    exact_mod_cast h
  have hnMinnMax : nMin ≤ nMax :=
    ((floor_mul_sq_mem_Icc hs_minCs (le_refl Cs)).1).trans
      ((floor_mul_sq_mem_Icc hs_minCs (le_refl Cs)).2)
  have hmesh_ne : mesh.Nonempty := by
    apply Finset.Nonempty.product
    · exact Finset.nonempty_Icc.mpr hnMinnMax
    · exact ⟨0, mem_boxFinset_iff.mpr (fun i => by simp)⟩
  have hsub : {w : Data d | ε < ⨆ p ∈ K,
        |barOdometer w R p.1 p.2 - barDivisible w R p.1 p.2|}
      ⊆ ⋃ q ∈ mesh, {w : Data d |
          ε / R ^ ((d : ℝ) / 2 - 2) < |(U w q.1 q.2 : ℝ) - uOf w q.1 q.2|} := by
    intro w hw
    simp only [Set.mem_setOf_eq] at hw
    set g : ℕ × Site d → ℝ := fun q => |(U w q.1 q.2 : ℝ) - uOf w q.1 q.2| with hg_def
    set M : ℝ := mesh.sup' hmesh_ne g with hM_def
    have hmesh_ne' := hmesh_ne
    obtain ⟨q1, hq1mem⟩ := hmesh_ne'
    have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (Finset.le_sup' g hq1mem)
    have hbound : ∀ p ∈ K, |barOdometer w R p.1 p.2 - barDivisible w R p.1 p.2|
        ≤ R ^ ((d : ℝ) / 2 - 2) * M := by
      intro p hp
      have hp1C : p.1 ≤ Cs := (le_trans (le_abs_self p.1) (hKC p hp).1).trans hCsC
      obtain ⟨hnp1, hnp2⟩ := floor_mul_sq_mem_Icc (hs_min p hp) hp1C
      have hmem_box : latticePoint R p.2 ∈ boxFinset (0 : Site d) mMax :=
        latticePoint_mem_boxFinset hRpos.le (fun i => ((hKC p hp).2 i).trans hCsC)
      have hqmem : (⌊p.1 * R ^ 2⌋₊, latticePoint R p.2) ∈ mesh :=
        Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hnp1, hnp2⟩, hmem_box⟩
      have hgle : g (⌊p.1 * R ^ 2⌋₊, latticePoint R p.2) ≤ M := Finset.le_sup' g hqmem
      have heq : |barOdometer w R p.1 p.2 - barDivisible w R p.1 p.2|
          = R ^ ((d : ℝ) / 2 - 2) * g (⌊p.1 * R ^ 2⌋₊, latticePoint R p.2) := by
        show |barOdometer w R p.1 p.2 - barDivisible w R p.1 p.2| = _
        unfold barOdometer barDivisible
        rw [← mul_sub, abs_mul, abs_of_nonneg hpow_pos.le]
      rw [heq]
      exact mul_le_mul_of_nonneg_left hgle hpow_pos.le
    have hsupbound : (⨆ p ∈ K, |barOdometer w R p.1 p.2 - barDivisible w R p.1 p.2|)
        ≤ R ^ ((d : ℝ) / 2 - 2) * M :=
      Real.iSup_le (fun p => Real.iSup_le (fun hp => hbound p hp)
        (mul_nonneg hpow_pos.le hMnn)) (mul_nonneg hpow_pos.le hMnn)
    have hlt : ε / R ^ ((d : ℝ) / 2 - 2) < M := by
      rw [div_lt_iff₀ hpow_pos]
      calc ε < ⨆ p ∈ K, |barOdometer w R p.1 p.2 - barDivisible w R p.1 p.2| := hw
        _ ≤ R ^ ((d : ℝ) / 2 - 2) * M := hsupbound
        _ = M * R ^ ((d : ℝ) / 2 - 2) := mul_comm _ _
    obtain ⟨q0, hq0mem, hq0eq⟩ := Finset.exists_mem_eq_sup' hmesh_ne g
    have hMeq : M = |(U w q0.1 q0.2 : ℝ) - uOf w q0.1 q0.2| := by
      rw [hM_def, hq0eq, hg_def]
    rw [Set.mem_iUnion₂]
    exact ⟨q0, hq0mem, by rw [Set.mem_setOf_eq, ← hMeq]; exact hlt⟩
  have hmeasure_le : (law d ν) {w : Data d | ε < ⨆ p ∈ K,
        |barOdometer w R p.1 p.2 - barDivisible w R p.1 p.2|}
      ≤ ∑ q ∈ mesh, (law d ν) {w : Data d |
          ε / R ^ ((d : ℝ) / 2 - 2) < |(U w q.1 q.2 : ℝ) - uOf w q.1 q.2|} :=
    (measure_mono hsub).trans (measure_biUnion_finset_le mesh _)
  have hterm_le : ∀ q ∈ mesh, (law d ν) {w : Data d |
        ε / R ^ ((d : ℝ) / 2 - 2) < |(U w q.1 q.2 : ℝ) - uOf w q.1 q.2|}
      ≤ ENNReal.ofReal (Real.exp (-(c * Real.log (nMin : ℝ) ^ 2))) := by
    intro q hq
    obtain ⟨hq1, _hq2⟩ := Finset.mem_product.mp hq
    have hqn1 : nMin ≤ q.1 := (Finset.mem_Icc.mp hq1).1
    have hqn2 : q.1 ≤ nMax := (Finset.mem_Icc.mp hq1).2
    rw [law_discrepancy_shift hd ν q.2 q.1 (ε / R ^ ((d : ℝ) / 2 - 2))]
    have hthresh : ε'' * meanu (law d ν) q.1 ≤ ε / R ^ ((d : ℝ) / 2 - 2) := by
      have hnMaxR : (nMax : ℝ) ≤ (Cs + 1) * R ^ 2 := by
        have h2 : (nMax : ℝ) < Cs * R ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
        nlinarith [h2, one_le_pow₀ hR1 (n := 2)]
      have hexprate : (0:ℝ) ≤ (4 - (d:ℝ)) / 4 := by
        have : (d:ℝ) ≤ 3 := by exact_mod_cast hd3
        linarith
      have hqmono : meanu (law d ν) q.1 ≤ meanu (law d ν) nMax := hmonoM hqn2
      have hnMaxupper : meanu (law d ν) nMax ≤ B * (nMax : ℝ) ^ ((4 - (d:ℝ)) / 4) :=
        (hgrowth nMax (hnMin2.trans hnMinnMax)).2
      have hratepow : (nMax : ℝ) ^ ((4 - (d:ℝ)) / 4) ≤ ((Cs + 1) * R ^ 2) ^ ((4 - (d:ℝ)) / 4) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hnMaxR hexprate
      have hsplit : ((Cs + 1) * R ^ 2) ^ ((4 - (d:ℝ)) / 4)
          = (Cs + 1) ^ ((4 - (d:ℝ)) / 4) * (R ^ 2) ^ ((4 - (d:ℝ)) / 4) :=
        Real.mul_rpow (by linarith) (by positivity)
      have hcancel : ε'' * (B * (Cs + 1) ^ ((4 - (d:ℝ)) / 4)) = ε := by
        rw [hε''_def]; field_simp
      have hexp_eq : ε * (R ^ 2) ^ ((4 - (d:ℝ)) / 4) = ε / R ^ ((d : ℝ) / 2 - 2) := by
        rw [eq_div_iff hpow_pos.ne']
        have hprod : (R ^ 2) ^ ((4 - (d:ℝ)) / 4) * R ^ ((d:ℝ) / 2 - 2) = 1 := by
          rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hR0, ← Real.rpow_add hRpos]
          have hz : ((2:ℕ):ℝ) * ((4 - (d:ℝ)) / 4) + ((d:ℝ) / 2 - 2) = 0 := by push_cast; ring
          rw [hz, Real.rpow_zero]
        rw [mul_assoc, hprod, mul_one]
      calc ε'' * meanu (law d ν) q.1
          ≤ ε'' * meanu (law d ν) nMax := by
            exact mul_le_mul_of_nonneg_left hqmono hε''pos.le
        _ ≤ ε'' * (B * (nMax : ℝ) ^ ((4 - (d:ℝ)) / 4)) :=
            mul_le_mul_of_nonneg_left hnMaxupper hε''pos.le
        _ ≤ ε'' * (B * ((Cs + 1) * R ^ 2) ^ ((4 - (d:ℝ)) / 4)) := by
            apply mul_le_mul_of_nonneg_left _ hε''pos.le
            exact mul_le_mul_of_nonneg_left hratepow hB.le
        _ = ε'' * (B * (Cs + 1) ^ ((4 - (d:ℝ)) / 4)) * (R ^ 2) ^ ((4 - (d:ℝ)) / 4) := by
            rw [hsplit]; ring
        _ = ε * (R ^ 2) ^ ((4 - (d:ℝ)) / 4) := by rw [hcancel]
        _ = ε / R ^ ((d : ℝ) / 2 - 2) := hexp_eq
    have hstep1 : (law d ν)
          {w : Data d | ε'' * meanu (law d ν) q.1 < |(U w q.1 (0:Site d) : ℝ) - uOf w q.1 0|}
        ≤ ENNReal.ofReal (Real.exp (-(c * Real.log (q.1:ℝ) ^ 2))) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top (law d ν) _)]
      exact ENNReal.ofReal_le_ofReal (hdisc q.1 (hnMinN.trans hqn1))
    have hstep2 : ENNReal.ofReal (Real.exp (-(c * Real.log (q.1:ℝ) ^ 2)))
        ≤ ENNReal.ofReal (Real.exp (-(c * Real.log (nMin:ℝ) ^ 2))) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hlog_mono : Real.log (nMin : ℝ) ≤ Real.log (q.1 : ℝ) :=
        Real.log_le_log (by exact_mod_cast hnMin1) (by exact_mod_cast hqn1)
      have hlognn : 0 ≤ Real.log (nMin : ℝ) := Real.log_nonneg (by exact_mod_cast hnMin1)
      have hsq : Real.log (nMin : ℝ) ^ 2 ≤ Real.log (q.1 : ℝ) ^ 2 := by
        nlinarith [hlog_mono, hlognn]
      nlinarith [mul_le_mul_of_nonneg_left hsq hc.le]
    exact (measure_mono (fun w hw => lt_of_le_of_lt hthresh hw)).trans (hstep1.trans hstep2)
  have hsum_le : ∑ q ∈ mesh, (law d ν) {w : Data d |
        ε / R ^ ((d : ℝ) / 2 - 2) < |(U w q.1 q.2 : ℝ) - uOf w q.1 q.2|}
      ≤ mesh.card • ENNReal.ofReal (Real.exp (-(c * Real.log (nMin : ℝ) ^ 2))) :=
    Finset.sum_le_card_nsmul mesh _ _ hterm_le
  have hfin : (law d ν) {w : Data d | ε < ⨆ p ∈ K,
        |barOdometer w R p.1 p.2 - barDivisible w R p.1 p.2|}
      ≤ mesh.card • ENNReal.ofReal (Real.exp (-(c * Real.log (nMin : ℝ) ^ 2))) :=
    hmeasure_le.trans hsum_le
  have hRHSne : mesh.card • ENNReal.ofReal (Real.exp (-(c * Real.log (nMin : ℝ) ^ 2))) ≠ ⊤ := by
    rw [nsmul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  have htoreal : ((law d ν) {w : Data d | ε < ⨆ p ∈ K,
        |barOdometer w R p.1 p.2 - barDivisible w R p.1 p.2|}).toReal
      ≤ (mesh.card • ENNReal.ofReal (Real.exp (-(c * Real.log (nMin : ℝ) ^ 2)))).toReal :=
    ENNReal.toReal_mono hRHSne hfin
  have hnsmul_eq : (mesh.card • ENNReal.ofReal (Real.exp (-(c * Real.log (nMin : ℝ) ^ 2)))).toReal
      = (mesh.card : ℝ) * Real.exp (-(c * Real.log (nMin : ℝ) ^ 2)) := by
    rw [nsmul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rw [hnsmul_eq] at htoreal
  have hcardbound : (mesh.card : ℝ) ≤ D1 * R ^ (d + 2) := by
    rw [hmesh_def]; exact mesh_card_le nMin Cs R hCs1 hR1
  have hpow_bound : R ^ (d + 2) ≤ (nMin : ℝ) ^ (d + 2) := pow_le_pow_left₀ hR0 hnMinR (d + 2)
  have hcardbound2 : (mesh.card : ℝ) ≤ D1 * (nMin : ℝ) ^ (d + 2) :=
    hcardbound.trans (mul_le_mul_of_nonneg_left hpow_bound hD1pos.le)
  have hkeq : (nMin : ℝ) ^ (d + 2) = (nMin : ℝ) ^ k := by rw [hk_def, Real.rpow_natCast]
  have hfinal : (nMin : ℝ) ^ k * Real.exp (-(c * Real.log (nMin : ℝ) ^ 2)) < ε' / D1 :=
    hx₀ (nMin : ℝ) hnMinx0
  calc ((law d ν) {w : Data d | ε < ⨆ p ∈ K,
          |barOdometer w R p.1 p.2 - barDivisible w R p.1 p.2|}).toReal
      ≤ (mesh.card : ℝ) * Real.exp (-(c * Real.log (nMin : ℝ) ^ 2)) := htoreal
    _ ≤ D1 * (nMin : ℝ) ^ (d + 2) * Real.exp (-(c * Real.log (nMin : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right hcardbound2 (Real.exp_pos _).le
    _ = D1 * ((nMin : ℝ) ^ k * Real.exp (-(c * Real.log (nMin : ℝ) ^ 2))) := by
        rw [hkeq]; ring
    _ ≤ D1 * (ε' / D1) := mul_le_mul_of_nonneg_left hfinal.le hD1pos.le
    _ = ε' := by field_simp

end Parking

end
