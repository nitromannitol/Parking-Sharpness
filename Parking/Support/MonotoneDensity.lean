/- The monotone density step of the last paragraph of Step 3 of the proof of
`thm:oriented-walk` (`parking.tex:3324-3331`).

The activity decreases and the mean is its partial sum, `E U⃗_n(0) = ∑_{s<n} S⃗_s`, so the
asymptotic `E U⃗_n(0) ∼ μ n^{1/4}` of the mean forces the asymptotic `S⃗_t ∼ (μ/4)t^{-3/4}`
of the activity.  The paper compares `S⃗_t` with the increment of the mean over the two
windows `[t, (1+ε)t]` and `[(1-ε)t, t]`.  Dividing by the window length and letting
`t → ∞` turns each comparison into a difference quotient of `x ↦ x^{1/4}` at `1`, and
those converge to the derivative `1/4` as `ε → 0`.
-/
import Parking.Support.MeanUniformInt
import Parking.Support.ScalParabolicScaling

open Filter Topology Finset

noncomputable section
namespace Parking

/-! ### The two window inequalities -/

/-- Over a window to the right of `t`, the increment of the partial sums of a decreasing
sequence is at most the window length times the value at `t`. -/
theorem sum_sub_le_mul (S : ℕ → ℝ) (hSanti : Antitone S) {t m : ℕ} (h : t ≤ m) :
    (∑ s ∈ Finset.range m, S s) - (∑ s ∈ Finset.range t, S s) ≤ ((m : ℝ) - t) * S t := by
  have hIco : ∑ s ∈ Finset.Ico t m, S s
      = (∑ s ∈ Finset.range m, S s) - (∑ s ∈ Finset.range t, S s) :=
    Finset.sum_Ico_eq_sub S h
  rw [← hIco]
  have hcard : (Finset.Ico t m).card = m - t := Nat.card_Ico t m
  have hbound : ∑ s ∈ Finset.Ico t m, S s ≤ (Finset.Ico t m).card • S t := by
    refine Finset.sum_le_card_nsmul _ _ _ ?_
    intro x hx
    exact hSanti (Finset.mem_Ico.mp hx).1
  rw [hcard, nsmul_eq_mul] at hbound
  have hcast : ((m - t : ℕ) : ℝ) = (m : ℝ) - (t : ℝ) := Nat.cast_sub h
  rwa [hcast] at hbound

/-- Over a window to the left of `t`, the increment of the partial sums of a decreasing
sequence is at least the window length times the value at `t`. -/
theorem mul_le_sum_sub (S : ℕ → ℝ) (hSanti : Antitone S) {k t : ℕ} (h : k ≤ t) :
    ((t : ℝ) - k) * S t ≤ (∑ s ∈ Finset.range t, S s) - (∑ s ∈ Finset.range k, S s) := by
  have hIco : ∑ s ∈ Finset.Ico k t, S s
      = (∑ s ∈ Finset.range t, S s) - (∑ s ∈ Finset.range k, S s) :=
    Finset.sum_Ico_eq_sub S h
  rw [← hIco]
  have hcard : (Finset.Ico k t).card = t - k := Nat.card_Ico k t
  have hbound : (Finset.Ico k t).card • S t ≤ ∑ s ∈ Finset.Ico k t, S s := by
    refine Finset.card_nsmul_le_sum _ _ _ ?_
    intro x hx
    exact hSanti (le_of_lt (Finset.mem_Ico.mp hx).2)
  rw [hcard, nsmul_eq_mul] at hbound
  have hcast : ((t - k : ℕ) : ℝ) = (t : ℝ) - (k : ℝ) := Nat.cast_sub h
  rwa [hcast] at hbound

/-! ### The difference quotient of the quarter power at one -/

/-- The difference quotient of `x ↦ x^{1/4}` at `1` converges to the derivative `1/4`. -/
theorem tendsto_slope_quarter :
    Tendsto (fun y : ℝ => (y ^ ((1:ℝ)/4) - 1) / (y - 1)) (𝓝[≠] 1) (𝓝 ((1:ℝ)/4)) := by
  have hd : HasDerivAt (fun x : ℝ => x ^ ((1:ℝ)/4)) ((1:ℝ)/4) 1 := by
    have h := Real.hasDerivAt_rpow_const (x := (1:ℝ)) (p := (1:ℝ)/4) (Or.inl one_ne_zero)
    simpa using h
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd
  refine hslope.congr fun y => ?_
  rw [slope_def_field, Real.one_rpow]

/-! ### The window limit -/

/-- **The increment of the mean over a window, divided by the window length.**  If
`a n ∼ μ n^{1/4}` and the window endpoint `m t` satisfies `m t / t → c`, the rescaled
increment converges to the difference quotient of `x ↦ x^{1/4}` at `1` evaluated at `c`,
times `μ`.  Both windows of the paper are this lemma, at `c = 1 + ε` and at `c = 1 - ε`. -/
theorem tendsto_window_quotient (a : ℕ → ℝ) (μ : ℝ)
    (hA : Tendsto (fun n : ℕ => a n / (n : ℝ) ^ ((1:ℝ)/4)) atTop (𝓝 μ))
    (c : ℝ) (hc : 0 < c) (hc1 : c ≠ 1)
    (m : ℕ → ℕ) (hminf : Tendsto m atTop atTop)
    (hmt : Tendsto (fun t : ℕ => (m t : ℝ) / t) atTop (𝓝 c)) :
    Tendsto (fun t : ℕ => ((t : ℝ) ^ ((3:ℝ)/4) * (a (m t) - a t)) / ((m t : ℝ) - t)) atTop
      (𝓝 (μ * (c ^ ((1:ℝ)/4) - 1) / (c - 1))) := by
  have hpow : Tendsto (fun t : ℕ => ((m t : ℝ) / t) ^ ((1:ℝ)/4)) atTop
      (𝓝 (c ^ ((1:ℝ)/4))) :=
    ((Real.continuousAt_rpow_const c ((1:ℝ)/4) (Or.inl (ne_of_gt hc))).tendsto).comp hmt
  have hAm : Tendsto (fun t : ℕ => a (m t) / (m t : ℝ) ^ ((1:ℝ)/4)) atTop (𝓝 μ) :=
    hA.comp hminf
  have hne : ∀ᶠ t : ℕ in atTop, (m t : ℝ) / t ≠ 1 :=
    hmt.eventually (eventually_ne_nhds hc1)
  have hden : Tendsto (fun t : ℕ => (t : ℝ) / ((m t : ℝ) - t)) atTop (𝓝 (1 / (c - 1))) := by
    have h1 : Tendsto (fun t : ℕ => (m t : ℝ) / t - 1) atTop (𝓝 (c - 1)) :=
      hmt.sub_const 1
    have h2 := h1.inv₀ (sub_ne_zero.mpr hc1)
    rw [← one_div] at h2
    refine h2.congr' ?_
    filter_upwards [hne, eventually_ge_atTop 1] with t hnt ht
    have ht0 : (0:ℝ) < t := by exact_mod_cast ht
    have hsub : (m t : ℝ) - t ≠ 0 := by
      intro h
      apply hnt
      have hmt' : (m t : ℝ) = t := by linarith
      rw [hmt', div_self (ne_of_gt ht0)]
    field_simp
  have hcomb := ((hAm.mul hpow).sub hA).mul hden
  have hval : (μ * c ^ ((1:ℝ)/4) - μ) * (1 / (c - 1))
      = μ * (c ^ ((1:ℝ)/4) - 1) / (c - 1) := by
    field_simp
  rw [hval] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [hne, eventually_ge_atTop 1, hminf.eventually_ge_atTop 1] with t hnt ht hmt1
  have ht0 : (0:ℝ) < t := by exact_mod_cast ht
  have hm0 : (0:ℝ) < (m t : ℝ) := by exact_mod_cast hmt1
  have hsub : (m t : ℝ) - t ≠ 0 := by
    intro h
    apply hnt
    have hmt' : (m t : ℝ) = t := by linarith
    rw [hmt', div_self (ne_of_gt ht0)]
  have hq : ((m t : ℝ) / t) ^ ((1:ℝ)/4)
      = (m t : ℝ) ^ ((1:ℝ)/4) / (t : ℝ) ^ ((1:ℝ)/4) :=
    Real.div_rpow hm0.le ht0.le _
  have hmq : (0:ℝ) < (m t : ℝ) ^ ((1:ℝ)/4) := Real.rpow_pos_of_pos hm0 _
  have htq : (0:ℝ) < (t : ℝ) ^ ((1:ℝ)/4) := Real.rpow_pos_of_pos ht0 _
  have ht34 : (t : ℝ) ^ ((3:ℝ)/4) = (t : ℝ) / (t : ℝ) ^ ((1:ℝ)/4) := by
    rw [eq_div_iff (ne_of_gt htq), ← Real.rpow_add ht0]
    norm_num
  rw [hq, ht34]
  field_simp

/-! ### The monotone density theorem in the form the paper uses -/

/-- **From the asymptotic of the mean to the asymptotic of the activity.** -/
theorem tendsto_activity_of_mean (S : ℕ → ℝ) (hSanti : Antitone S)
    (a : ℕ → ℝ) (hsum : ∀ n : ℕ, a n = ∑ s ∈ Finset.range n, S s)
    (μ : ℝ)
    (hA : Tendsto (fun n : ℕ => a n / (n : ℝ) ^ ((1:ℝ)/4)) atTop (𝓝 μ)) :
    Tendsto (fun t : ℕ => (t : ℝ) ^ ((3:ℝ)/4) * S t) atTop (𝓝 (μ / 4)) := by
  have hQ : Tendsto (fun c : ℝ => μ * (c ^ ((1:ℝ)/4) - 1) / (c - 1)) (𝓝[≠] 1)
      (𝓝 (μ / 4)) := by
    have h := tendsto_slope_quarter.const_mul μ
    rw [show μ * ((1:ℝ)/4) = μ / 4 by ring] at h
    refine h.congr fun y => ?_
    ring
  have hplus : Tendsto (fun e : ℝ => (1:ℝ) + e) (𝓝[>] 0) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun e : ℝ => (1:ℝ) + e) (𝓝 0) (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add tendsto_id
      rw [add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with e he
      have he' : (0:ℝ) < e := he
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      linarith
  have hminus : Tendsto (fun e : ℝ => (1:ℝ) - e) (𝓝[>] 0) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun e : ℝ => (1:ℝ) - e) (𝓝 0) (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub tendsto_id
      rw [sub_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with e he
      have he' : (0:ℝ) < e := he
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      linarith
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hδ2 : (0:ℝ) < δ / 2 := by linarith
  have hevp := Metric.tendsto_nhds.mp (hQ.comp hplus) (δ / 2) hδ2
  have hevm := Metric.tendsto_nhds.mp (hQ.comp hminus) (δ / 2) hδ2
  have hev1 : ∀ᶠ e in 𝓝[>] (0:ℝ), e < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))
  obtain ⟨ε, ⟨hQp, hQm, hε1⟩, hεmem⟩ :=
    ((hevp.and (hevm.and hev1)).and self_mem_nhdsWithin).exists
  have hε : (0:ℝ) < ε := hεmem
  simp only [Function.comp_apply] at hQp hQm
  rw [Real.dist_eq, abs_lt] at hQp hQm
  have hcp : (0:ℝ) < 1 + ε := by linarith
  have hcm : (0:ℝ) < 1 - ε := by linarith
  have hmle : ∀ t : ℕ, t ≤ ⌊(t : ℝ) * (1 + ε)⌋₊ := by
    intro t
    refine Nat.le_floor ?_
    have h0 : (0:ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    nlinarith
  have hkle : ∀ t : ℕ, ⌊(t : ℝ) * (1 - ε)⌋₊ ≤ t := by
    intro t
    have h1 : (t : ℝ) * (1 - ε) ≤ (t : ℝ) := by
      have h0 : (0:ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
      nlinarith
    calc ⌊(t : ℝ) * (1 - ε)⌋₊ ≤ ⌊(t : ℝ)⌋₊ := Nat.floor_mono h1
      _ = t := Nat.floor_natCast t
  have hminf : Tendsto (fun t : ℕ => ⌊(t : ℝ) * (1 + ε)⌋₊) atTop atTop :=
    tendsto_atTop_mono hmle tendsto_id
  have hkinf : Tendsto (fun t : ℕ => ⌊(t : ℝ) * (1 - ε)⌋₊) atTop atTop := by
    refine Filter.tendsto_atTop_atTop.mpr fun N => ?_
    refine ⟨⌈(N : ℝ) / (1 - ε)⌉₊, fun t ht => ?_⟩
    have h1 : (N : ℝ) / (1 - ε) ≤ (t : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast ht)
    rw [div_le_iff₀ hcm] at h1
    exact Nat.le_floor h1
  have hmt : Tendsto (fun t : ℕ => ((⌊(t : ℝ) * (1 + ε)⌋₊ : ℕ) : ℝ) / t) atTop
      (𝓝 (1 + ε)) := by
    have h := (tendsto_floor_mul_div (1 + ε) hcp).mul_const (1 + ε)
    rw [one_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    have ht0 : (0:ℝ) < t := by exact_mod_cast ht
    field_simp
  have hkt : Tendsto (fun t : ℕ => ((⌊(t : ℝ) * (1 - ε)⌋₊ : ℕ) : ℝ) / t) atTop
      (𝓝 (1 - ε)) := by
    have h := (tendsto_floor_mul_div (1 - ε) hcm).mul_const (1 - ε)
    rw [one_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    have ht0 : (0:ℝ) < t := by exact_mod_cast ht
    field_simp
  have hlow := tendsto_window_quotient a μ hA (1 + ε) hcp (ne_of_gt (by linarith))
    (fun t : ℕ => ⌊(t : ℝ) * (1 + ε)⌋₊) hminf hmt
  have hhigh := tendsto_window_quotient a μ hA (1 - ε) hcm (ne_of_lt (by linarith))
    (fun t : ℕ => ⌊(t : ℝ) * (1 - ε)⌋₊) hkinf hkt
  have hevL := Metric.tendsto_nhds.mp hlow (δ / 2) hδ2
  have hevH := Metric.tendsto_nhds.mp hhigh (δ / 2) hδ2
  have hbig : ∀ᶠ t : ℕ in atTop, (1:ℝ) ≤ ε * t :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hε).eventually_ge_atTop 1
  filter_upwards [hevL, hevH, eventually_ge_atTop 1, hbig] with t hL hH ht htb
  rw [Real.dist_eq, abs_lt] at hL hH
  have ht0 : (0:ℝ) < t := by exact_mod_cast ht
  have ht34 : (0:ℝ) ≤ (t : ℝ) ^ ((3:ℝ)/4) := Real.rpow_nonneg ht0.le _
  have hmgt : (t : ℝ) < ((⌊(t : ℝ) * (1 + ε)⌋₊ : ℕ) : ℝ) := by
    have hfl : t + 1 ≤ ⌊(t : ℝ) * (1 + ε)⌋₊ := by
      refine Nat.le_floor ?_
      push_cast
      nlinarith
    have : ((t + 1 : ℕ) : ℝ) ≤ ((⌊(t : ℝ) * (1 + ε)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hfl
    push_cast at this
    linarith
  have hklt : ((⌊(t : ℝ) * (1 - ε)⌋₊ : ℕ) : ℝ) < (t : ℝ) := by
    have h1 : ((⌊(t : ℝ) * (1 - ε)⌋₊ : ℕ) : ℝ) ≤ (t : ℝ) * (1 - ε) :=
      Nat.floor_le (by nlinarith)
    nlinarith
  have hDm : (0:ℝ) < ((⌊(t : ℝ) * (1 + ε)⌋₊ : ℕ) : ℝ) - t := by linarith
  have hDk : (0:ℝ) < (t : ℝ) - ((⌊(t : ℝ) * (1 - ε)⌋₊ : ℕ) : ℝ) := by linarith
  have hsl := sum_sub_le_mul S hSanti (hmle t)
  rw [← hsum, ← hsum] at hsl
  have hsu := mul_le_sum_sub S hSanti (hkle t)
  rw [← hsum, ← hsum] at hsu
  have hineqL : ((t : ℝ) ^ ((3:ℝ)/4) * (a ⌊(t : ℝ) * (1 + ε)⌋₊ - a t))
      / (((⌊(t : ℝ) * (1 + ε)⌋₊ : ℕ) : ℝ) - t) ≤ (t : ℝ) ^ ((3:ℝ)/4) * S t := by
    rw [div_le_iff₀ hDm]
    calc (t : ℝ) ^ ((3:ℝ)/4) * (a ⌊(t : ℝ) * (1 + ε)⌋₊ - a t)
        ≤ (t : ℝ) ^ ((3:ℝ)/4) *
          ((((⌊(t : ℝ) * (1 + ε)⌋₊ : ℕ) : ℝ) - t) * S t) :=
          mul_le_mul_of_nonneg_left hsl ht34
      _ = (t : ℝ) ^ ((3:ℝ)/4) * S t * (((⌊(t : ℝ) * (1 + ε)⌋₊ : ℕ) : ℝ) - t) := by ring
  have hrwH : ((t : ℝ) ^ ((3:ℝ)/4) * (a ⌊(t : ℝ) * (1 - ε)⌋₊ - a t))
      / (((⌊(t : ℝ) * (1 - ε)⌋₊ : ℕ) : ℝ) - t)
      = ((t : ℝ) ^ ((3:ℝ)/4) * (a t - a ⌊(t : ℝ) * (1 - ε)⌋₊))
        / ((t : ℝ) - ((⌊(t : ℝ) * (1 - ε)⌋₊ : ℕ) : ℝ)) := by
    rw [div_eq_div_iff (by linarith) (ne_of_gt hDk)]
    ring
  have hineqH : (t : ℝ) ^ ((3:ℝ)/4) * S t
      ≤ ((t : ℝ) ^ ((3:ℝ)/4) * (a ⌊(t : ℝ) * (1 - ε)⌋₊ - a t))
        / (((⌊(t : ℝ) * (1 - ε)⌋₊ : ℕ) : ℝ) - t) := by
    rw [hrwH, le_div_iff₀ hDk]
    calc (t : ℝ) ^ ((3:ℝ)/4) * S t * ((t : ℝ) - ((⌊(t : ℝ) * (1 - ε)⌋₊ : ℕ) : ℝ))
        = (t : ℝ) ^ ((3:ℝ)/4) *
          (((t : ℝ) - ((⌊(t : ℝ) * (1 - ε)⌋₊ : ℕ) : ℝ)) * S t) := by ring
      _ ≤ (t : ℝ) ^ ((3:ℝ)/4) * (a t - a ⌊(t : ℝ) * (1 - ε)⌋₊) :=
          mul_le_mul_of_nonneg_left hsu ht34
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith [hL.1, hQp.1, hineqL]
  · linarith [hH.2, hQm.2, hineqH]

end Parking
end
