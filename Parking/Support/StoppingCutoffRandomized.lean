/-
**The randomized discrete cutoff-to-true limit for the stopping-value summand.**

The pathwise cutoff comparison `Parking.abs_stoppingSup_sub_cutoffStoppingSup_pathwise`
(`Parking/Support/StoppingCutoffPathwise.lean`) needs its bounding constant `M` supplied by a
TAIL-CONTROLLED quantity, not an arbitrary hypothesis, before it becomes a statement about
probability rather than about one fixed realization. This module supplies that: `M` is
instantiated at the `Finset.sup'` of `|Parking.linPotential η · ·|` over the finite time-space
grid `(Finset.range (n₀+1)) ×ˢ (Parking.boxFinset 0 A₂)` (`Parking.gridSup`), which bounds the
cutoff reward everywhere by construction (`Parking.abs_cutoffReward_shift_le_gridSup`); the
event where this bound EXCEEDS a chosen threshold `M₀` is exactly the maximal-inequality event
of `Parking.exists_linPotential_maximal_tail_time_shift`
(`Parking/Support/LinPotentialMaximalTime.lean`) with the `m = 0` slice discarded
(`Parking.gridSup_lt_imp_maximal_event`, via `Finset.lt_sup'_iff` and
`Parking.linPotential_zero`), so its probability is tail-controlled at the SAME rate.

**The concrete rate choice**: horizon `n₀(R) := ⌊sR²⌋₊`
(`Parking.barPotential`/`Parking.barDivisible`'s own horizon, `Parking/Support/BarPotential.lean`,
`Parking/Support/Continuum.lean`), target cutoff radius `A(R) := ⌈R³⌉₊`, reachability radius
`A₂(R) := n₀(R) + A(R)` (so `A₂(R) ≥ n₀(R)` and `A₂(R) ≥ A(R)` UNCONDITIONALLY, no eventual
reasoning needed for either inequality), and threshold `M₀(R) := n₀(R)·R`. Splitting on whether
`Parking.gridSup` at these parameters exceeds `M₀(R)`:

- on the complement, the pathwise bound applies deterministically at `M := M₀(R)`, giving
  `|stoppingSup ... - cutoffStoppingSup ...| ≤ M₀(R)·n₀(R)·d²/A(R)² = O(1/R) → 0`
  (`Parking.tendsto_pathwiseErrorRate_zero`, a direct squeeze);
- the exceptional event has probability `≤ C·n₀(R)·(2·A₂(R)+1)^d·exp(-c·R)`, which `→ 0` since
  `n₀(R)·(2·A₂(R)+1)^d` is polynomial in `R` (degrees `2` and `3` respectively) and
  `exp(-c·R)` beats every polynomial (`tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`,
  `Parking.tendsto_maximalTailBound_zero`).

Once the pathwise error rate is eventually `< ε`, `{ε < |diff|}` is contained in the exceptional
event, so the final `Tendsto ... (𝓝 0)`
(`Parking.tendsto_measure_stoppingSup_sub_cutoffStoppingSup_zero`) follows by the squeeze
theorem. No `External` is registered or consumed: every theorem here is proved, not cited.
-/
import Parking.Support.LinPotentialMaximalTime
import Parking.Support.StoppingCutoffPathwise
import Parking.Support.Continuum
import Parking.Support.ThreeShellSum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-! ### The bounding grid-sup, and its discharge of `hM` -/

/-- The base point `(0,0)` always lies in the grid, so `Finset.sup'` never hits the junk
value of an empty supremum. -/
theorem gridSup_finset_nonempty (n0 A2 : ℕ) :
    ((0 : ℕ), (0 : Site d)) ∈ Finset.range (n0 + 1) ×ˢ boxFinset (0 : Site d) A2 :=
  Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (by omega),
      mem_box_zero_of_graphNorm_le (le_of_eq_of_le graphNorm_zero (Nat.zero_le A2))⟩

/-- **The finite time-space grid sup bounding the cutoff reward.** The `Finset.sup'` of
`|Parking.linPotential η · ·|`, shifted to start at `z0`, over the time range
`Finset.range (n0+1)` and the box `Parking.boxFinset 0 A2`. -/
def gridSup (η : Site d → ℝ) (z0 : Site d) (n0 A2 : ℕ) : ℝ :=
  (Finset.range (n0 + 1) ×ˢ boxFinset (0 : Site d) A2).sup'
    ⟨(0, (0 : Site d)), gridSup_finset_nonempty n0 A2⟩
    (fun p : ℕ × Site d => |linPotential η p.1 (z0 + p.2)|)

theorem gridSup_nonneg (η : Site d → ℝ) (z0 : Site d) (n0 A2 : ℕ) : 0 ≤ gridSup η z0 n0 A2 := by
  unfold gridSup
  calc (0 : ℝ) ≤ |linPotential η 0 (z0 + 0)| := abs_nonneg _
    _ ≤ _ := Finset.le_sup' (fun p : ℕ × Site d => |linPotential η p.1 (z0 + p.2)|)
        (gridSup_finset_nonempty n0 A2)

/-- **The cutoff reward, shifted to start at `z0` and truncated at `A2`, is bounded by
`Parking.gridSup`.** The case split is exactly `Parking.cutoffReward`'s own `if`: outside the
box the cutoff is `0 ≤ gridSup` (`Parking.gridSup_nonneg`); inside, `Parking.
mem_box_zero_of_graphNorm_le` places `y` in `Parking.boxFinset 0 A2` and `n0 - k` (truncated
`ℕ`-subtraction) is always in `Finset.range (n0+1)`, so `Finset.le_sup'` applies directly. -/
theorem abs_cutoffReward_shift_le_gridSup (η : Site d → ℝ) (z0 : Site d) (n0 A2 : ℕ)
    (k : ℕ) (y : Site d) :
    |cutoffReward (fun k y => -linPotential η (n0 - k) (z0 + y)) (A2 : ℝ) k y|
      ≤ gridSup η z0 n0 A2 := by
  unfold cutoffReward
  split_ifs with hy
  · have hyle : graphNorm y ≤ A2 := by exact_mod_cast hy
    have hpmem : (n0 - k, y) ∈ Finset.range (n0 + 1) ×ˢ boxFinset (0 : Site d) A2 :=
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), mem_box_zero_of_graphNorm_le hyle⟩
    rw [abs_neg]
    exact Finset.le_sup' (fun p : ℕ × Site d => |linPotential η p.1 (z0 + p.2)|) hpmem
  · rw [abs_zero]
    exact gridSup_nonneg η z0 n0 A2

/-! ### The deterministic error bound, once `Parking.gridSup` is controlled -/

/-- **The pathwise cutoff-to-true bound, at a bounding constant supplied by `Parking.gridSup`.**
`Parking.abs_stoppingSup_sub_cutoffStoppingSup_pathwise`'s `hM` hypothesis, discharged by
`Parking.abs_cutoffReward_shift_le_gridSup` and a hypothesis that `Parking.gridSup` itself is
`≤ M`. -/
theorem abs_stoppingSup_sub_cutoffStoppingSup_of_gridSup_le
    (hd1 : 1 ≤ d) (η : Site d → ℝ) (z0 : Site d) (n0 A2 : ℕ) {A : ℝ}
    (hA : 0 < A) (hnA2 : (n0 : ℝ) ≤ (A2 : ℝ)) (hAA2 : A ≤ (A2 : ℝ)) {M : ℝ}
    (hle : gridSup η z0 n0 A2 ≤ M) :
    |stoppingSup d (fun k y => -linPotential η (n0 - k) y) n0 z0
        - cutoffStoppingSup (fun k y => -linPotential η (n0 - k) (z0 + y)) A n0|
      ≤ M * ((n0 : ℝ) * (d : ℝ) ^ 2 / A ^ 2) := by
  have hM : ∀ k y, |cutoffReward (fun k y => -linPotential η (n0 - k) (z0 + y)) (A2 : ℝ) k y|
      ≤ M := fun k y => le_trans (abs_cutoffReward_shift_le_gridSup η z0 n0 A2 k y) hle
  exact abs_stoppingSup_sub_cutoffStoppingSup_pathwise hd1
    (fun k y => -linPotential η (n0 - k) y) z0 hA hnA2 hAA2 hM

/-! ### Connecting the exceptional event to the maximal inequality's own event -/

theorem gridSup_gt_iff (η : Site d → ℝ) (z0 : Site d) (n0 A2 : ℕ) (t : ℝ) :
    t < gridSup η z0 n0 A2 ↔
      ∃ m ∈ Finset.range (n0 + 1), ∃ y ∈ boxFinset (0 : Site d) A2,
        t < |linPotential η m (z0 + y)| := by
  unfold gridSup
  rw [Finset.lt_sup'_iff]
  constructor
  · rintro ⟨⟨m, y⟩, hmem, hlt⟩
    obtain ⟨hm, hy⟩ := Finset.mem_product.mp hmem
    exact ⟨m, hm, y, hy, hlt⟩
  · rintro ⟨m, hm, y, hy, hlt⟩
    exact ⟨(m, y), Finset.mem_product.mpr ⟨hm, hy⟩, hlt⟩

/-- **The exceptional event `Parking.gridSup > t` is contained in the maximal inequality's own
event**, for `t ≥ 0`: `Parking.linPotential_zero` kills the `m = 0` slice of the grid (its value
is identically `0`, so it can never exceed a nonnegative threshold), leaving exactly
`Finset.Icc 1 n0`. -/
theorem gridSup_lt_imp_maximal_event (η : Site d → ℝ) (z0 : Site d) (n0 A2 : ℕ) {t : ℝ}
    (ht : 0 ≤ t) (h : t < gridSup η z0 n0 A2) :
    ∃ m ∈ Finset.Icc 1 n0, ∃ y ∈ boxFinset (0 : Site d) A2, t ≤ |linPotential η m (y + z0)| := by
  rw [gridSup_gt_iff] at h
  obtain ⟨m, hm, y, hy, hlt⟩ := h
  rw [Finset.mem_range] at hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [linPotential_zero, abs_zero] at hlt
    exact absurd hlt (not_lt.mpr ht)
  refine ⟨m, Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hm0, by omega⟩, y, hy, ?_⟩
  have hlt' : t < |linPotential η m (y + z0)| := by rw [add_comm y z0]; exact hlt
  exact hlt'.le

/-! ### The two asymptotic rates, at the concrete choice `A(R) := ⌈R³⌉₊`, `M₀(R) := n₀(R)·R` -/

/-- **The deterministic pathwise error rate `M₀(R)·n₀(R)·d²/A(R)²` vanishes.** -/
theorem tendsto_pathwiseErrorRate_zero (s : ℝ) (hs : 0 < s) (d : ℕ) :
    Tendsto (fun R : ℝ =>
        ((⌊s * R ^ 2⌋₊ : ℝ) * R) * (⌊s * R ^ 2⌋₊ : ℝ) * (d : ℝ) ^ 2 / (⌈R ^ 3⌉₊ : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hbound : ∀ᶠ R : ℝ in atTop,
      ((⌊s * R ^ 2⌋₊ : ℝ) * R) * (⌊s * R ^ 2⌋₊ : ℝ) * (d : ℝ) ^ 2 / (⌈R ^ 3⌉₊ : ℝ) ^ 2
        ≤ s ^ 2 * (d : ℝ) ^ 2 / R := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR0
    set n0R : ℝ := (⌊s * R ^ 2⌋₊ : ℝ)
    set AR : ℝ := (⌈R ^ 3⌉₊ : ℝ)
    have hn0nonneg : 0 ≤ n0R := Nat.cast_nonneg _
    have hn0le : n0R ≤ s * R ^ 2 := Nat.floor_le (by positivity)
    have hAge : R ^ 3 ≤ AR := Nat.le_ceil _
    have hR3pos : (0 : ℝ) < R ^ 3 := by positivity
    have hApos : 0 < AR := lt_of_lt_of_le hR3pos hAge
    have hkey : n0R * R ≤ s * AR := by
      calc n0R * R ≤ (s * R ^ 2) * R := mul_le_mul_of_nonneg_right hn0le hR0.le
        _ = s * R ^ 3 := by ring
        _ ≤ s * AR := mul_le_mul_of_nonneg_left hAge hs.le
    have hsq : (n0R * R) ^ 2 ≤ (s * AR) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hn0nonneg hR0.le) hkey 2
    have hsq' : n0R ^ 2 * R ^ 2 ≤ s ^ 2 * AR ^ 2 := by
      have he1 : (n0R * R) ^ 2 = n0R ^ 2 * R ^ 2 := by ring
      have he2 : (s * AR) ^ 2 = s ^ 2 * AR ^ 2 := by ring
      rw [he1, he2] at hsq
      exact hsq
    rw [div_le_div_iff₀ (by positivity) hR0]
    calc n0R * R * n0R * (d : ℝ) ^ 2 * R = n0R ^ 2 * R ^ 2 * (d : ℝ) ^ 2 := by ring
      _ ≤ s ^ 2 * AR ^ 2 * (d : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hsq' (sq_nonneg (d : ℝ))
      _ = s ^ 2 * (d : ℝ) ^ 2 * AR ^ 2 := by ring
  have htail : Tendsto (fun R : ℝ => s ^ 2 * (d : ℝ) ^ 2 / R) atTop (𝓝 0) := by
    have h1 := tendsto_inv_atTop_zero (𝕜 := ℝ)
    have h2 := h1.const_mul (s ^ 2 * (d : ℝ) ^ 2)
    simp only [mul_zero] at h2
    simpa [div_eq_mul_inv] using h2
  have hnonneg : ∀ᶠ R : ℝ in atTop,
      (0 : ℝ) ≤ ((⌊s * R ^ 2⌋₊ : ℝ) * R) * (⌊s * R ^ 2⌋₊ : ℝ) * (d : ℝ) ^ 2 / (⌈R ^ 3⌉₊ : ℝ) ^ 2 := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR0
    positivity
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htail hnonneg hbound

/-- **The exceptional-event tail bound `C·n₀(R)·(2·A₂(R)+1)^d·exp(-c·R)` vanishes**: the
prefactor is polynomial of degree `3d+3` in `R` (`n₀(R) = O(R²)`, `A₂(R) = O(R³)`), which
`exp(-c·R)` beats (`tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`). -/
theorem tendsto_maximalTailBound_zero (s c C : ℝ) (hs : 0 < s) (hc : 0 < c) (hC : 0 < C)
    (d : ℕ) :
    Tendsto (fun R : ℝ =>
        C * (⌊s * R ^ 2⌋₊ : ℝ) * (2 * ((⌊s * R ^ 2⌋₊ + ⌈R ^ 3⌉₊ : ℕ) : ℝ) + 1) ^ d
          * Real.exp (-(c * R)))
      atTop (𝓝 0) := by
  have hbound : ∀ᶠ R : ℝ in atTop,
      C * (⌊s * R ^ 2⌋₊ : ℝ) * (2 * ((⌊s * R ^ 2⌋₊ + ⌈R ^ 3⌉₊ : ℕ) : ℝ) + 1) ^ d
          * Real.exp (-(c * R))
        ≤ (C * s * (2 * s + 5) ^ d) * (R ^ ((3 * d + 3 : ℕ) : ℝ) * Real.exp (-(c * R))) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR1
    have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
    have hR3ge1 : (1 : ℝ) ≤ R ^ 3 := by
      have h := pow_le_pow_left₀ (zero_le_one) hR1 3
      simpa using h
    have hn0nonneg : (0 : ℝ) ≤ (⌊s * R ^ 2⌋₊ : ℝ) := Nat.cast_nonneg _
    have hn0le : (⌊s * R ^ 2⌋₊ : ℝ) ≤ s * R ^ 2 := Nat.floor_le (by positivity)
    have hR2leR3 : R ^ 2 ≤ R ^ 3 := by
      have h : R ^ 2 * 1 ≤ R ^ 2 * R := mul_le_mul_of_nonneg_left hR1 (sq_nonneg R)
      calc R ^ 2 = R ^ 2 * 1 := (mul_one _).symm
        _ ≤ R ^ 2 * R := h
        _ = R ^ 3 := by ring
    have hn0leR3 : (⌊s * R ^ 2⌋₊ : ℝ) ≤ s * R ^ 3 := by
      calc (⌊s * R ^ 2⌋₊ : ℝ) ≤ s * R ^ 2 := hn0le
        _ ≤ s * R ^ 3 := mul_le_mul_of_nonneg_left hR2leR3 hs.le
    have hAlt : (⌈R ^ 3⌉₊ : ℝ) < R ^ 3 + 1 := Nat.ceil_lt_add_one (by positivity)
    have hAle : (⌈R ^ 3⌉₊ : ℝ) ≤ 2 * R ^ 3 := by
      calc (⌈R ^ 3⌉₊ : ℝ) ≤ R ^ 3 + 1 := hAlt.le
        _ ≤ R ^ 3 + R ^ 3 := by linarith [hR3ge1]
        _ = 2 * R ^ 3 := by ring
    have hA2cast : ((⌊s * R ^ 2⌋₊ + ⌈R ^ 3⌉₊ : ℕ) : ℝ)
        = (⌊s * R ^ 2⌋₊ : ℝ) + (⌈R ^ 3⌉₊ : ℝ) := by push_cast; ring
    have hA2le : ((⌊s * R ^ 2⌋₊ + ⌈R ^ 3⌉₊ : ℕ) : ℝ) ≤ (s + 2) * R ^ 3 := by
      rw [hA2cast]
      calc (⌊s * R ^ 2⌋₊ : ℝ) + (⌈R ^ 3⌉₊ : ℝ) ≤ s * R ^ 3 + 2 * R ^ 3 :=
            add_le_add hn0leR3 hAle
        _ = (s + 2) * R ^ 3 := by ring
    have hboxle : 2 * ((⌊s * R ^ 2⌋₊ + ⌈R ^ 3⌉₊ : ℕ) : ℝ) + 1 ≤ (2 * s + 5) * R ^ 3 := by
      calc 2 * ((⌊s * R ^ 2⌋₊ + ⌈R ^ 3⌉₊ : ℕ) : ℝ) + 1
          ≤ 2 * ((s + 2) * R ^ 3) + 1 := by linarith [hA2le]
        _ ≤ 2 * ((s + 2) * R ^ 3) + R ^ 3 := by linarith [hR3ge1]
        _ = (2 * s + 5) * R ^ 3 := by ring
    have hboxnonneg : (0 : ℝ) ≤ 2 * ((⌊s * R ^ 2⌋₊ + ⌈R ^ 3⌉₊ : ℕ) : ℝ) + 1 := by positivity
    have hboxpow : (2 * ((⌊s * R ^ 2⌋₊ + ⌈R ^ 3⌉₊ : ℕ) : ℝ) + 1) ^ d
        ≤ ((2 * s + 5) * R ^ 3) ^ d := pow_le_pow_left₀ hboxnonneg hboxle d
    have hstep : (⌊s * R ^ 2⌋₊ : ℝ) * (2 * ((⌊s * R ^ 2⌋₊ + ⌈R ^ 3⌉₊ : ℕ) : ℝ) + 1) ^ d
        ≤ s * R ^ 3 * ((2 * s + 5) * R ^ 3) ^ d :=
      mul_le_mul hn0leR3 hboxpow (pow_nonneg hboxnonneg d) (by positivity)
    have hexppos : (0 : ℝ) < Real.exp (-(c * R)) := Real.exp_pos _
    have hCmul : C * ((⌊s * R ^ 2⌋₊ : ℝ) * (2 * ((⌊s * R ^ 2⌋₊ + ⌈R ^ 3⌉₊ : ℕ) : ℝ) + 1) ^ d)
        ≤ C * (s * R ^ 3 * ((2 * s + 5) * R ^ 3) ^ d) :=
      mul_le_mul_of_nonneg_left hstep hC.le
    have heq1 : s * R ^ 3 * ((2 * s + 5) * R ^ 3) ^ d
        = s * (2 * s + 5) ^ d * R ^ (3 * d + 3) := by
      rw [mul_pow, ← pow_mul]
      ring
    have heq2 : R ^ (3 * d + 3) = R ^ ((3 * d + 3 : ℕ) : ℝ) := (Real.rpow_natCast R (3*d+3)).symm
    calc C * (⌊s * R ^ 2⌋₊ : ℝ) * (2 * ((⌊s * R ^ 2⌋₊ + ⌈R ^ 3⌉₊ : ℕ) : ℝ) + 1) ^ d
          * Real.exp (-(c * R))
        = C * ((⌊s * R ^ 2⌋₊ : ℝ) * (2 * ((⌊s * R ^ 2⌋₊ + ⌈R ^ 3⌉₊ : ℕ) : ℝ) + 1) ^ d)
          * Real.exp (-(c * R)) := by ring
      _ ≤ (C * (s * R ^ 3 * ((2 * s + 5) * R ^ 3) ^ d)) * Real.exp (-(c * R)) :=
          mul_le_mul_of_nonneg_right hCmul hexppos.le
      _ = (C * s * (2 * s + 5) ^ d) * (R ^ ((3 * d + 3 : ℕ) : ℝ) * Real.exp (-(c * R))) := by
          rw [heq1, heq2]; ring
  have hrate : Tendsto (fun R : ℝ => (C * s * (2 * s + 5) ^ d)
      * (R ^ ((3 * d + 3 : ℕ) : ℝ) * Real.exp (-(c * R)))) atTop (𝓝 0) := by
    have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((3 * d + 3 : ℕ) : ℝ) c hc
    simp only [neg_mul] at h1
    have h2 := h1.const_mul (C * s * (2 * s + 5) ^ d)
    simpa using h2
  have hnonneg : ∀ᶠ R : ℝ in atTop,
      (0 : ℝ) ≤ C * (⌊s * R ^ 2⌋₊ : ℝ) * (2 * ((⌊s * R ^ 2⌋₊ + ⌈R ^ 3⌉₊ : ℕ) : ℝ) + 1) ^ d
          * Real.exp (-(c * R)) := by
    filter_upwards with R
    positivity
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrate hnonneg hbound

/-! ### The final assembly -/

/-- **The randomized discrete cutoff-to-true limit.** At the horizon
`n₀(R) := ⌊sR²⌋₊` (`Parking.barPotential`'s own horizon) and starting site `z0(R) :=
Parking.latticePoint R x`, the TRUE stopping value of the reward `-Parking.linPotential η
(n₀(R) - ·) ·` and its cutoff at radius `A(R) := ⌈R³⌉₊` agree in probability as `R → ∞`. -/
theorem tendsto_measure_stoppingSup_sub_cutoffStoppingSup_zero
    (hd1 : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν) (s : ℝ) (hs : 0 < s) (x : Fin d → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R : ℝ =>
        ((iidLaw d (realLaw ν)) {η : Site d → ℝ |
            ε < |stoppingSup d (fun k y => -linPotential η (⌊s * R ^ 2⌋₊ - k) y)
                    ⌊s * R ^ 2⌋₊ (latticePoint R x)
                - cutoffStoppingSup
                    (fun k y => -linPotential η (⌊s * R ^ 2⌋₊ - k) (latticePoint R x + y))
                    (⌈R ^ 3⌉₊ : ℝ) ⌊s * R ^ 2⌋₊|}).toReal)
      atTop (𝓝 0) := by
  haveI := hν.prob
  haveI hν0P : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI hμP : IsProbabilityMeasure (iidLaw d (realLaw ν)) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : Site d => realLaw ν))
  obtain ⟨c, C, hc, hC, hmax⟩ := exists_linPotential_maximal_tail_time_shift hd1 ν hν
  have hn0tendsto : Tendsto (fun R : ℝ => (⌊s * R ^ 2⌋₊ : ℕ)) atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_pow_atTop (two_ne_zero)).const_mul_atTop hs)
  have hev_n0 : ∀ᶠ R : ℝ in atTop, 1 ≤ ⌊s * R ^ 2⌋₊ := hn0tendsto.eventually_ge_atTop 1
  have hev_R1 : ∀ᶠ R : ℝ in atTop, (1 : ℝ) ≤ R := eventually_ge_atTop 1
  have hrateTendsto := tendsto_pathwiseErrorRate_zero s hs d
  have hev_rate : ∀ᶠ R : ℝ in atTop,
      ((⌊s * R ^ 2⌋₊ : ℝ) * R) * (⌊s * R ^ 2⌋₊ : ℝ) * (d : ℝ) ^ 2 / (⌈R ^ 3⌉₊ : ℝ) ^ 2 < ε :=
    hrateTendsto.eventually (Iio_mem_nhds hε)
  have htailTendsto := tendsto_maximalTailBound_zero s c C hs hc hC d
  -- The exceptional-event set inclusion, eventually in `R`.
  have hincl : ∀ᶠ R : ℝ in atTop,
      {η : Site d → ℝ | ε < |stoppingSup d (fun k y => -linPotential η (⌊s * R ^ 2⌋₊ - k) y)
              ⌊s * R ^ 2⌋₊ (latticePoint R x)
          - cutoffStoppingSup
              (fun k y => -linPotential η (⌊s * R ^ 2⌋₊ - k) (latticePoint R x + y))
              (⌈R ^ 3⌉₊ : ℝ) ⌊s * R ^ 2⌋₊|}
        ⊆ {η : Site d → ℝ | ∃ m ∈ Finset.Icc 1 (⌊s * R ^ 2⌋₊),
            ∃ y ∈ boxFinset (0 : Site d) (⌊s * R ^ 2⌋₊ + ⌈R ^ 3⌉₊),
              (⌊s * R ^ 2⌋₊ : ℝ) * R
                ≤ |linPotential η m (y + latticePoint R x)|} := by
    filter_upwards [hev_R1, hev_n0, hev_rate] with R hR1 hn0R hrateR
    intro η hη
    by_contra hnegRHS
    set n0 : ℕ := ⌊s * R ^ 2⌋₊
    set A : ℕ := ⌈R ^ 3⌉₊
    set A2 : ℕ := n0 + A
    set z0 : Site d := latticePoint R x
    have hM0nonneg : (0 : ℝ) ≤ (n0 : ℝ) * R := by positivity
    have hgridle : gridSup η z0 n0 A2 ≤ (n0 : ℝ) * R :=
      not_lt.mp (fun hgt => hnegRHS (gridSup_lt_imp_maximal_event η z0 n0 A2 hM0nonneg hgt))
    have hApos : (0 : ℝ) < (A : ℝ) := by
      have h3 : (0 : ℝ) < R ^ 3 := by positivity
      exact lt_of_lt_of_le h3 (Nat.le_ceil _)
    have hnA2 : (n0 : ℝ) ≤ (A2 : ℝ) := by exact_mod_cast Nat.le_add_right n0 A
    have hAA2 : (A : ℝ) ≤ (A2 : ℝ) := by exact_mod_cast Nat.le_add_left A n0
    have hbound := abs_stoppingSup_sub_cutoffStoppingSup_of_gridSup_le hd1 η z0 n0 A2
      hApos hnA2 hAA2 hgridle
    have hratesmall : (n0 : ℝ) * R * ((n0 : ℝ) * (d : ℝ) ^ 2 / (A : ℝ) ^ 2) < ε := by
      have heq : (n0 : ℝ) * R * ((n0 : ℝ) * (d : ℝ) ^ 2 / (A : ℝ) ^ 2)
          = ((n0 : ℝ) * R) * (n0 : ℝ) * (d : ℝ) ^ 2 / (A : ℝ) ^ 2 := by ring
      rw [heq]; exact hrateR
    exact absurd hη (not_lt.mpr (hbound.trans hratesmall.le))
  -- The exceptional event's own measure `→ 0`, via `hmax` at the concrete rate.
  have hmax_le : ∀ᶠ R : ℝ in atTop,
      ((iidLaw d (realLaw ν)) {η : Site d → ℝ | ∃ m ∈ Finset.Icc 1 (⌊s * R ^ 2⌋₊),
          ∃ y ∈ boxFinset (0 : Site d) (⌊s * R ^ 2⌋₊ + ⌈R ^ 3⌉₊),
            (⌊s * R ^ 2⌋₊ : ℝ) * R ≤ |linPotential η m (y + latticePoint R x)|}).toReal
        ≤ C * (⌊s * R ^ 2⌋₊ : ℝ) * (2 * ((⌊s * R ^ 2⌋₊ + ⌈R ^ 3⌉₊ : ℕ) : ℝ) + 1) ^ d
            * Real.exp (-(c * R)) := by
    filter_upwards [hev_R1, hev_n0] with R hR1 hn0R
    have hMpos : (0 : ℝ) < (⌊s * R ^ 2⌋₊ : ℝ) * R := by
      have h1 : (1 : ℝ) ≤ (⌊s * R ^ 2⌋₊ : ℝ) := by exact_mod_cast hn0R
      have h2 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
      nlinarith [h1, h2]
    have hb := hmax (latticePoint R x) (⌊s * R ^ 2⌋₊) hn0R (⌊s * R ^ 2⌋₊ + ⌈R ^ 3⌉₊)
      ((⌊s * R ^ 2⌋₊ : ℝ) * R) hMpos
    have hn0ne : (⌊s * R ^ 2⌋₊ : ℝ) ≠ 0 := by
      have h1 : (1 : ℝ) ≤ (⌊s * R ^ 2⌋₊ : ℝ) := by exact_mod_cast hn0R
      linarith
    have heqdiv : ((⌊s * R ^ 2⌋₊ : ℝ) * R) / (⌊s * R ^ 2⌋₊ : ℝ) = R := by field_simp
    have heqsq : ((⌊s * R ^ 2⌋₊ : ℝ) * R) ^ 2 / (⌊s * R ^ 2⌋₊ : ℝ) ^ 2 = R ^ 2 := by
      rw [div_eq_iff (by positivity)]; ring
    have hR2geR : R ≤ R ^ 2 := by nlinarith [hR1]
    have hmineq : min (((⌊s * R ^ 2⌋₊ : ℝ) * R) ^ 2 / (⌊s * R ^ 2⌋₊ : ℝ) ^ 2)
        (((⌊s * R ^ 2⌋₊ : ℝ) * R) / (⌊s * R ^ 2⌋₊ : ℝ)) = R := by
      rw [heqdiv, heqsq]
      exact min_eq_right hR2geR
    rwa [hmineq] at hb
  -- Combine: on the good rate range, the target set is contained in the exceptional event.
  have hincl2 : ∀ᶠ R : ℝ in atTop,
      ((iidLaw d (realLaw ν)) {η : Site d → ℝ |
          ε < |stoppingSup d (fun k y => -linPotential η (⌊s * R ^ 2⌋₊ - k) y)
                  ⌊s * R ^ 2⌋₊ (latticePoint R x)
              - cutoffStoppingSup
                  (fun k y => -linPotential η (⌊s * R ^ 2⌋₊ - k) (latticePoint R x + y))
                  (⌈R ^ 3⌉₊ : ℝ) ⌊s * R ^ 2⌋₊|}).toReal
        ≤ C * (⌊s * R ^ 2⌋₊ : ℝ) * (2 * ((⌊s * R ^ 2⌋₊ + ⌈R ^ 3⌉₊ : ℕ) : ℝ) + 1) ^ d
            * Real.exp (-(c * R)) := by
    filter_upwards [hincl, hmax_le] with R hRincl hRmax
    refine le_trans ?_ hRmax
    rw [← measureReal_def, ← measureReal_def]
    exact measureReal_mono hRincl (measure_ne_top _ _)
  have hnonneg : ∀ᶠ R : ℝ in atTop,
      (0 : ℝ) ≤ ((iidLaw d (realLaw ν)) {η : Site d → ℝ |
          ε < |stoppingSup d (fun k y => -linPotential η (⌊s * R ^ 2⌋₊ - k) y)
                  ⌊s * R ^ 2⌋₊ (latticePoint R x)
              - cutoffStoppingSup
                  (fun k y => -linPotential η (⌊s * R ^ 2⌋₊ - k) (latticePoint R x + y))
                  (⌈R ^ 3⌉₊ : ℝ) ⌊s * R ^ 2⌋₊|}).toReal := by
    filter_upwards with R
    exact ENNReal.toReal_nonneg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htailTendsto hnonneg hincl2

end Parking

end
