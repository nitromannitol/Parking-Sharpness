/-
**Sharpens the dimension-one space-direction `l2Norm` two-point comparison** of
`Parking.Support.SpatGreenShiftLowDim` from the crude rate `spatialStepRate 1 n = √(2n+3)`
(`O(n^{1/2})`) to the SHARP rate `O(n^{1/4}) = √κ_1(n)`.  The `d = 1` route of that module
uses a crude cardinality bound (`O(√n)`, matching `κ_1(n)` ITSELF rather than its square
root) rather than the sharp Chebyshev one that `sq_green_one_step_le`'s pointwise bound
already supports.

This module proves the sharp rate: `Parking.sq_green_one_step_le`'s own sharp, `min(|c|,|c+1|)`-
dependent pointwise bound (never used by `Parking.sum_green_one_step_sq_le`, which drops it for
the flat bound `Parking.sq_green_one_step_le_four`) is summed via the SAME shell-sum estimate
`Parking.sum_min_le_sqrt` that `Parking.Support.GammaSum`'s own dimension-one branch of
`gamma_sum_of_gradient` already uses for a different (but computationally identical) purpose,
after a reflection reindexing (`Finset.sum_nbij'` along `c ↦ -c`) that reduces the sum over the
whole box `Finset.Icc (-(n+1)) (n+1)` to twice the sum over the positive half plus the value at
`0`.

**Motivation.**  The rescaled Kolmogorov increment bound (the spatial analogue of the
hypothesis `happ` of the oriented scaling limit) needs `Parking.linHatInterp`'s two-point
comparison to be UNIFORM IN `R` at a FIXED continuum separation `|Δx|` (lattice separation
`graphNorm(x-y) ≈ R·|Δx|`, horizon `n = ⌊sR²⌋ ≈ R²`), after the `R^{d/2-2}` rescaling. At
`d = 1` (`R^{d/2-2} = R^{-3/2}`), the CRUDE rate leaves

  `R^{-3/2} · spatialStepRate 1 (R²) · graphNorm(x-y) ≈ R^{-3/2} · (R·√2) · (R·|Δx|)
    = √2 · R^{1/2} · |Δx| → ∞`,

a genuine, unbounded-in-`R` divergence — NOT uniform. The SHARP rate built here,
`O(n^{1/4})` at `n = R²` is `O(R^{1/2})`, giving instead

  `R^{-3/2} · O(R^{1/2}) · (R·|Δx|) = O(R^{-3/2+1/2+1}) = O(R^0)`,

which cancels EXACTLY: uniform in `R`, as `prop:spatial-scaling`'s own scaling limit requires.
This module establishes only the one-step-chained `l2Norm` bound (`d = 1`).  The box-supremum
moment bound itself (the analogue of `Parking.exists_yfieldSup3_L2_moment`) is a further step:
it needs the Kolmogorov-Chentsov dyadic-chaining construction
(`Parking.Support.TightKolmogorov`/`TightBoxSupMoment` through `TightBoxSupL2`, mirrored for the
interpolated field `Parking.linHatInterp`) built on TOP of a sharp two-point estimate such as
this one.  The same technique does not sharpen the cases `d = 2, 3`: there the limitation is a
genuine SATURATION obstruction, not a crude estimate.

The bound proved here is an independent, additive, strictly SHARPER alternative to
`exists_green_space_shift_l2_bound_full` of `Parking.Support.SpatGreenShiftLowDim` (and to the
rate `spatialStepRate`) for `d = 1` alone, under new names throughout (`_sharp` suffix), so
nothing that already consumes the existing (weaker) bound is affected.
-/
import Parking.Support.SpatGreenShiftLowDim

noncomputable section

namespace Parking

open LatticeProb Finset

/-! ### The sharp pointwise bound, reindexed by `max c.natAbs 1` -/

/-- **`max c.natAbs 1 ≤ min c.natAbs (c+1).natAbs + 1`, for every `c : ℤ`.**  Equality holds
for `c < 0`; for `c ≥ 0` the right side is one larger. -/
theorem max_natAbs_one_le_min_natAbs_succ (c : ℤ) :
    max c.natAbs 1 ≤ min c.natAbs (c + 1).natAbs + 1 := by
  omega

/-- **`x ↦ min 1 (n/x²)` is antitone on the positive reals.** -/
theorem min_one_div_sq_antitone {n x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hn : 0 ≤ n) :
    min 1 (n / y ^ 2) ≤ min 1 (n / x ^ 2) := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hsq : x ^ 2 ≤ y ^ 2 := by nlinarith
  have hdiv : n / y ^ 2 ≤ n / x ^ 2 :=
    div_le_div_of_nonneg_left hn (by positivity) hsq
  exact min_le_min le_rfl hdiv

/-- **The sharp one-step pointwise bound, reindexed**: `Parking.sq_green_one_step_le`'s bound
with the argument `min c.natAbs (c+1).natAbs + 1` replaced by `max c.natAbs 1`, which no longer
depends on the sign of `c` — the key step that lets the resulting sum be grouped by `|c|`. -/
theorem sq_green_one_step_le_sharp (n : ℕ) (c : ℤ) :
    (green 1 n ![c] - green 1 n ![c + 1]) ^ 2
      ≤ 4 * (min 1 ((n : ℝ) / ((max c.natAbs 1 : ℕ) : ℝ) ^ 2)) ^ 2 := by
  have hbase := sq_green_one_step_le n c
  have hle : max c.natAbs 1 ≤ min c.natAbs (c + 1).natAbs + 1 :=
    max_natAbs_one_le_min_natAbs_succ c
  have hleR : ((max c.natAbs 1 : ℕ) : ℝ) ≤ ((min c.natAbs (c + 1).natAbs : ℕ) : ℝ) + 1 := by
    have hcast : ((max c.natAbs 1 : ℕ) : ℝ) ≤ ((min c.natAbs (c + 1).natAbs + 1 : ℕ) : ℝ) :=
      Nat.cast_le.mpr hle
    rwa [Nat.cast_add, Nat.cast_one] at hcast
  have hpos : (0 : ℝ) < ((max c.natAbs 1 : ℕ) : ℝ) := by
    have h1 : 1 ≤ max c.natAbs 1 := le_max_right _ _
    have hcast : ((1 : ℕ) : ℝ) ≤ ((max c.natAbs 1 : ℕ) : ℝ) := Nat.cast_le.mpr h1
    simp only [Nat.cast_one] at hcast
    linarith
  have hanti := min_one_div_sq_antitone hpos hleR (Nat.cast_nonneg n)
  have h1nn : (0 : ℝ) ≤ min 1 ((n : ℝ) / (((min c.natAbs (c + 1).natAbs : ℕ) : ℝ) + 1) ^ 2) :=
    le_min (by norm_num) (by positivity)
  have h2nn : (0 : ℝ) ≤ min 1 ((n : ℝ) / ((max c.natAbs 1 : ℕ) : ℝ) ^ 2) :=
    le_min (by norm_num) (by positivity)
  have hmono : (min 1 ((n : ℝ) / (((min c.natAbs (c + 1).natAbs : ℕ) : ℝ) + 1) ^ 2)) ^ 2
      ≤ (min 1 ((n : ℝ) / ((max c.natAbs 1 : ℕ) : ℝ) ^ 2)) ^ 2 :=
    pow_le_pow_left₀ h1nn hanti 2
  linarith [hbase, hmono]

/-! ### Summing the sharp bound, by reflection -/

/-- The summand, named once. -/
def maxOneTerm (n : ℕ) (c : ℤ) : ℝ := (min 1 ((n : ℝ) / ((max c.natAbs 1 : ℕ) : ℝ) ^ 2)) ^ 2

theorem maxOneTerm_nonneg (n : ℕ) (c : ℤ) : 0 ≤ maxOneTerm n c := by
  unfold maxOneTerm
  positivity

theorem maxOneTerm_le_one (n : ℕ) (c : ℤ) : maxOneTerm n c ≤ 1 := by
  unfold maxOneTerm
  have h1 : min 1 ((n : ℝ) / ((max c.natAbs 1 : ℕ) : ℝ) ^ 2) ≤ 1 := min_le_left _ _
  have h0 : (0 : ℝ) ≤ min 1 ((n : ℝ) / ((max c.natAbs 1 : ℕ) : ℝ) ^ 2) :=
    le_min (by norm_num) (by positivity)
  nlinarith

theorem maxOneTerm_neg (n : ℕ) (c : ℤ) : maxOneTerm n (-c) = maxOneTerm n c := by
  unfold maxOneTerm
  rw [Int.natAbs_neg]

/-- **The reflection identity**: the sum over the negative half equals the sum over the
positive half. -/
theorem sum_maxOneTerm_neg_eq (n : ℕ) :
    ∑ c ∈ Finset.Icc (-(n : ℤ) - 1) (-1 : ℤ), maxOneTerm n c
      = ∑ c ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), maxOneTerm n c := by
  apply Finset.sum_nbij' (fun c => -c) (fun c => -c)
  · intro c hc
    simp only [Finset.mem_Icc] at hc ⊢
    omega
  · intro c hc
    simp only [Finset.mem_Icc] at hc ⊢
    omega
  · intro c _
    ring
  · intro c _
    ring
  · intro c _
    exact (maxOneTerm_neg n c).symm

/-- **The sum over the positive half, transported to a `ℕ`-indexed sum.** -/
theorem sum_maxOneTerm_pos_eq (n : ℕ) :
    ∑ c ∈ Finset.Icc (1 : ℤ) ((n : ℤ) + 1), maxOneTerm n c
      = ∑ k ∈ Finset.Icc 1 (n + 1), (min 1 ((n : ℝ) / (k : ℝ) ^ 2)) ^ 2 := by
  apply Finset.sum_nbij' (fun c : ℤ => c.toNat) (fun k : ℕ => (k : ℤ))
  · intro c hc
    simp only [Finset.mem_Icc] at hc ⊢
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro c hc
    simp only [Finset.mem_Icc] at hc
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    omega
  · intro c hc
    simp only [Finset.mem_Icc] at hc
    unfold maxOneTerm
    have hcnn : 0 ≤ c := by omega
    have heq : max c.natAbs 1 = c.toNat := by
      have : c.natAbs = c.toNat := by omega
      rw [this]
      have h1 : 1 ≤ c.toNat := by omega
      omega
    rw [heq]

/-- **The `ℕ`-indexed sum, extended by one extra (nonnegative, `≤ 1`) term, bounded via
`Parking.sum_min_le_sqrt`.** -/
theorem sum_min_sq_Icc_succ_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 (n + 1), (min 1 ((n : ℝ) / (k : ℝ) ^ 2)) ^ 2
      ≤ 5 * Real.sqrt (n : ℝ) + 1 := by
  have hstep : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hstep, Finset.sum_insert (by simp)]
  have hbase := sum_min_le_sqrt (n := n) hn
  have hextra : (min 1 ((n : ℝ) / (((n : ℕ) + 1 : ℕ) : ℝ) ^ 2)) ^ 2 ≤ 1 := by
    have h1 : min 1 ((n : ℝ) / (((n : ℕ) + 1 : ℕ) : ℝ) ^ 2) ≤ 1 := min_le_left _ _
    have h0 : (0 : ℝ) ≤ min 1 ((n : ℝ) / (((n : ℕ) + 1 : ℕ) : ℝ) ^ 2) :=
      le_min (by norm_num) (by positivity)
    nlinarith
  linarith

/-- **The whole box sum, sharp**: `Σ_{c ∈ Icc(-(n+1),n+1)} maxOneTerm n c ≤ 1 + 2·(5√n+1)`. -/
theorem sum_maxOneTerm_box_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ c ∈ Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1), maxOneTerm n c
      ≤ 1 + 2 * (5 * Real.sqrt (n : ℝ) + 1) := by
  have hsplit : ∑ c ∈ Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1), maxOneTerm n c
      = ∑ c ∈ Finset.Icc (-(n : ℤ) - 1) (-1 : ℤ), maxOneTerm n c
        + ∑ c ∈ Finset.Icc (0 : ℤ) ((n : ℤ) + 1), maxOneTerm n c := by
    have hunion : Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1)
        = Finset.Icc (-(n : ℤ) - 1) (-1 : ℤ) ∪ Finset.Icc (0 : ℤ) ((n : ℤ) + 1) := by
      ext c
      simp only [Finset.mem_Icc, Finset.mem_union]
      omega
    have hdisj : Disjoint (Finset.Icc (-(n : ℤ) - 1) (-1 : ℤ)) (Finset.Icc (0 : ℤ) ((n : ℤ) + 1)) := by
      rw [Finset.disjoint_left]
      intro c hc1 hc2
      simp only [Finset.mem_Icc] at hc1 hc2
      omega
    rw [hunion, Finset.sum_union hdisj]
  rw [hsplit]
  have hposSplit : Finset.Icc (0 : ℤ) ((n : ℤ) + 1) = insert (0 : ℤ) (Finset.Icc (1 : ℤ) ((n : ℤ) + 1)) := by
    ext c
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hposSplit, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
  rw [sum_maxOneTerm_neg_eq, sum_maxOneTerm_pos_eq]
  have h0 : maxOneTerm n 0 ≤ 1 := maxOneTerm_le_one n 0
  have hmain := sum_min_sq_Icc_succ_le n hn
  linarith

/-! ### The sharp finite-sum bound on the one-step forward-difference squared -/

/-- **The sharp finite-sum bound**, replacing `Parking.sum_green_one_step_sq_le`'s crude
`O(n)` bound with a genuine `O(√n)` one. -/
theorem sum_green_one_step_sq_le_sharp (n : ℕ) (hn : 1 ≤ n) :
    ∑ c ∈ Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1), (green 1 n ![c] - green 1 n ![c + 1]) ^ 2
      ≤ 4 * (1 + 2 * (5 * Real.sqrt (n : ℝ) + 1)) := by
  calc ∑ c ∈ Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1), (green 1 n ![c] - green 1 n ![c + 1]) ^ 2
      ≤ ∑ c ∈ Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1), 4 * maxOneTerm n c :=
        Finset.sum_le_sum fun c _ => sq_green_one_step_le_sharp n c
    _ = 4 * ∑ c ∈ Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1), maxOneTerm n c := by
        rw [Finset.mul_sum]
    _ ≤ 4 * (1 + 2 * (5 * Real.sqrt (n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (sum_maxOneTerm_box_le n hn) (by norm_num)

/-- **The `tsum` form.** -/
theorem tsum_green_one_step_sq_le_sharp (n : ℕ) (hn : 1 ≤ n) :
    ∑' c : ℤ, (green 1 n ![c] - green 1 n ![c + 1]) ^ 2
      ≤ 4 * (1 + 2 * (5 * Real.sqrt (n : ℝ) + 1)) := by
  rw [tsum_green_one_step_sq_eq]
  exact sum_green_one_step_sq_le_sharp n hn

/-- **The one-step `l2Norm` bound, sharp, at the forward neighbour.** -/
theorem exists_green_space_step_l2_bound_one_plus_sharp (n : ℕ) (hn : 1 ≤ n) (x : Site 1) :
    l2Norm (fun z => green 1 n (x - z) - green 1 n (x + unit 0 - z))
      ≤ 2 * Real.sqrt (1 + 2 * (5 * Real.sqrt (n : ℝ) + 1)) := by
  unfold l2Norm
  have hreidx : ∑' z : Site 1, (green 1 n (x - z) - green 1 n (x + unit 0 - z)) ^ 2
      = ∑' w : Site 1, (green 1 n w - green 1 n (w + unit 0)) ^ 2 := by
    rw [← tsum_comp_subLeft x (fun w => (green 1 n w - green 1 n (w + unit 0)) ^ 2)]
    refine tsum_congr fun z => ?_
    congr 2
    have : x + unit 0 - z = (x - z) + unit 0 := by abel
    rw [this]
  have hpt : ∀ w : Site 1, (green 1 n w - green 1 n (w + unit 0)) ^ 2
      = (green 1 n ![site1ToInt w] - green 1 n ![site1ToInt w + 1]) ^ 2 := by
    intro w
    show (green 1 n w - green 1 n (w + unit 0)) ^ 2
        = (green 1 n ![w 0] - green 1 n ![w 0 + 1]) ^ 2
    conv_lhs => rw [site_one_eq w, site_one_add_unit (w 0)]
  have hE : ∑' w : Site 1, (green 1 n ![site1ToInt w] - green 1 n ![site1ToInt w + 1]) ^ 2
      = ∑' c : ℤ, (green 1 n ![c] - green 1 n ![c + 1]) ^ 2 :=
    site1ToInt.tsum_eq (fun c => (green 1 n ![c] - green 1 n ![c + 1]) ^ 2)
  rw [hreidx, tsum_congr hpt, hE]
  calc Real.sqrt (∑' c : ℤ, (green 1 n ![c] - green 1 n ![c + 1]) ^ 2)
      ≤ Real.sqrt (4 * (1 + 2 * (5 * Real.sqrt (n : ℝ) + 1))) :=
        Real.sqrt_le_sqrt (tsum_green_one_step_sq_le_sharp n hn)
    _ = 2 * Real.sqrt (1 + 2 * (5 * Real.sqrt (n : ℝ) + 1)) := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
        congr 1
        rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]

/-- **The one-step `l2Norm` bound, sharp, at a fixed pair of neighbours.** -/
theorem exists_green_space_step_l2_bound_one_sharp (n : ℕ) (hn : 1 ≤ n) {x x' : Site 1}
    (hx' : x' ∈ nbrFinset x) :
    l2Norm (fun z => green 1 n (x - z) - green 1 n (x' - z))
      ≤ 2 * Real.sqrt (1 + 2 * (5 * Real.sqrt (n : ℝ) + 1)) := by
  obtain ⟨i, hcase⟩ := mem_nbrFinset_iff.mp hx'
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  rcases hcase with hcase | hcase
  · subst hcase
    exact exists_green_space_step_l2_bound_one_plus_sharp n hn x
  · subst hcase
    have hgoal := exists_green_space_step_l2_bound_one_plus_sharp n hn (x - unit 0)
    have heq : (fun z : Site 1 => green 1 n (x - unit 0 - z)
          - green 1 n (x - unit 0 + unit 0 - z))
        = (fun z : Site 1 => green 1 n (x - unit 0 - z) - green 1 n (x - z)) := by
      funext z
      have hcancel : x - unit 0 + unit 0 = x := by abel
      rw [hcancel]
    rw [heq] at hgoal
    rw [l2Norm_green_diff_symm]
    exact hgoal

/-- **The sharp `L`-step `l2Norm` comparison in dimension one**: `l2Norm(green diff) ≤
graphNorm(x-y) · O(n^{1/4})`, the sharp Chebyshev rate `O(n^{1/4}) = √κ_1(n)`, in place of
the `O(n^{1/2})` rate of `Parking.spatialStepRate`. -/
theorem exists_green_space_l2_bound_one_sharp (n : ℕ) (hn : 1 ≤ n) (x y : Site 1) :
    l2Norm (fun z => green 1 n (x - z) - green 1 n (y - z))
      ≤ (graphNorm (x - y) : ℝ) * (2 * Real.sqrt (1 + 2 * (5 * Real.sqrt (n : ℝ) + 1))) :=
  exists_green_space_l2_bound_of_step (n := n)
    (B := 2 * Real.sqrt (1 + 2 * (5 * Real.sqrt (n : ℝ) + 1))) (by positivity)
    (fun a b hb => exists_green_space_step_l2_bound_one_sharp n hn hb) (graphNorm (x - y)) x y rfl

end Parking

end
