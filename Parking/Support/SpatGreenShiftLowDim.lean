/-
**The SPACE-direction two-point comparison of the truncated Green function, dimensions one
and two.**  Extends `Parking.Support.SpatGreenShift` to the remaining dimensions: that
module proves the bound

    l2Norm (fun z => green d n (x - z) - green d n (y - z))
    supAbs (fun z => green d n (x - z) - green d n (y - z))

only for `d ≥ 3` (`l2Norm`) and `d ≥ 2` (`supAbs`), decaying linearly in
`graphNorm (x - y)`, UNIFORMLY in the horizon `n`.  This module supplies the missing
`d = 1, 2` cases, and assembles a SINGLE combined wrapper covering the whole range
`1 ≤ d ≤ 3` that `prop:spatial-scaling` needs, unconditionally (no `External` hypothesis):
for `d = 2, 3`, `Parking.External.GreenGradient` is not merely cited but PROVED in the
shared library (`Parking.External.greenGradient`), so it can be supplied directly rather
than carried as a hypothesis; for `d = 1` no such citation is used at all (exactly as
`Parking.External.GreenGradient`'s own docstring already notes: "in dimension one the
gradient is computed exactly").

Two genuinely different routes, matching `Parking.Support.GammaSum`'s own two branches for
a different quantity (`lem:gamma-sum`'s sum, not this two-point comparison):

- **Dimension one.**  The one-step forward difference `green 1 n ![c] - green 1 n ![c+1]`
  is computed EXACTLY, for every `c` (not merely `c ≥ 0`) by `Parking.green_one_sub'`
  (`c ≥ 0`) combined with the UNCONDITIONAL reflection symmetry `green_neg` (no sign
  restriction at all: `green 1 n ![c] = green 1 n ![-c]` for every `c`), which reduces the
  general case to the `c ≥ 0` one by the involution `c ↦ -c-1`.  Since `green 1 n`
  vanishes outside `[-n, n]`, the resulting `tsum` over `ℤ` (equivalently, over `Site 1`) is
  a finite sum, split into the nonnegative and negative halves by a `Finset.sum_nbij'`
  reindexing along that same involution (matching `Parking.Support.SpatGreenShift`'s own use
  of `Finset.sum_nbij'` for `sum_boxFinset_shift`), and bounded by
  `Parking.Support.Shells.sum_min_le_sqrt`, EXACTLY the series `Parking.Support.GammaSum`'s
  own dimension-one branch of `gamma_sum_of_gradient` sums.  The resulting one-step bound is
  `O(n^{1/4})` (`l2Norm`) — `Real.sqrt (Parking.kappa 1 n)`, `Parking.kappa` being the SAME
  dimension-dependent rate `Parking.Support.GammaSum`'s own `lem:gamma-sum` sum uses — not
  the `d ≥ 3` case's `n`-independent bound, exactly as `Parking.Support.SpatGreenShift`'s own
  docstring notes ("Dimensions one and two need the truncation-by-vanishing-support trick").
- **Dimension two.**  `Parking.External.GreenGradient 2` (PROVED, `Parking.External.
  greenGradient 2`) gives the pointwise radial bound `Parking.Support.GammaSum` uses; the
  same shell-sum machinery as `Parking.Support.SpatGreenShift`'s own `d ≥ 3` case
  (`sum_box_radial`, `shellCard_le`, `rpow_shell_combine`) applies, but the resulting series
  `Σ_k shellCard(2,k)(1+k)^{-2}` diverges logarithmically over the WHOLE lattice (unlike
  `d ≥ 3`, where it converges), so it is truncated at the horizon `n` (the box the truncated
  Green function is supported in) exactly as `Parking.Support.GammaSum`'s own
  `gamma_sum_of_gradient` dimension-two branch truncates, using
  `Parking.Support.Shells.sum_inv_succ_le_log`.  The resulting one-step bound is
  `O(√(log n))` (`l2Norm`) — again `Real.sqrt (Parking.kappa 2 n)`.

Both routes feed the SAME generic one-step-to-`L`-step chaining lemma
(`exists_green_space_l2_bound_of_step`/`exists_green_space_sup_bound_of_step`, this
module), which is the `Parking.Support.SpatGreenShift` induction (`l2Norm_add_le_of_support`
Minkowski chaining) abstracted away from HOW the one-step bound was derived, so it applies
uniformly to all three dimension routes without triplicating the induction.

The `supAbs` half needs no `kappa` factor in ANY dimension `1 ≤ d ≤ 3`: the pointwise bound
`|green d n y - green d n z| ≤ C(1+graphNorm y)^{1-d} ≤ C` (for `d ≥ 1`, since the exponent
`1-d ≤ 0` and the base `≥ 1`) already gives a horizon-independent one-step sup-bound for
`d = 2, 3` via `Parking.Support.SpatGreenShift.exists_green_space_step_sup_bound`, and
dimension one is `|green 1 n ![c] - green 1 n ![c+1]| = 2 * srwTail n c' ≤ 2` (`c'` the
nonnegative reduction of `c`), via `Parking.srwTail_le_one` alone, uniformly in `n`.
-/
import Parking.Support.SpatGreenShift

noncomputable section

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-! ### The generic one-step-to-`L`-step chaining lemma, independent of the route -/

/-- **Chaining a one-step comparison, bounded by a fixed `B` at every neighbour pair, into a
bound linear in the graph distance**: the SAME Minkowski induction
`Parking.Support.SpatGreenShift.exists_green_space_l2_bound` uses, abstracted away from how
the one-step bound `B` was derived. -/
theorem exists_green_space_l2_bound_of_step {n : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hstep : ∀ x x' : Site d, x' ∈ nbrFinset x →
      l2Norm (fun z => green d n (x - z) - green d n (x' - z)) ≤ B) :
    ∀ L : ℕ, ∀ x y : Site d, graphNorm (x - y) = L →
      l2Norm (fun z => green d n (x - z) - green d n (y - z)) ≤ (L : ℝ) * B := by
  intro L
  induction L with
  | zero =>
      intro x y hL
      have hxy : x = y := sub_eq_zero.mp (graphNorm_eq_zero_iff.mp hL)
      subst hxy
      have hz0 : (fun z => green d n (x - z) - green d n (x - z)) = fun _ : Site d => (0:ℝ) := by
        funext z; ring
      rw [hz0]
      have h0 : l2Norm (fun _ : Site d => (0:ℝ)) = 0 := by unfold l2Norm; simp
      rw [h0]; positivity
  | succ L ih =>
      intro x y hL
      have hxy : x ≠ y := by
        intro hcontra
        have hz0 : graphNorm (0 : Site d) = 0 := graphNorm_eq_zero_iff.mpr rfl
        rw [hcontra, sub_self, hz0] at hL
        omega
      obtain ⟨x', hx', hpred⟩ := exists_nbr_graphNorm_pred hxy
      have hLx' : graphNorm (x' - y) = L := by omega
      have hIH := ih x' y hLx'
      have hone := hstep x x' hx'
      set R : ℕ := n + L + 2 with hRdef
      have hS1 : ∀ z ∉ boxFinset x R, green d n (x - z) - green d n (x' - z) = 0 := by
        intro z hz
        refine green_diff_eq_zero_of_notMem_box ?_ ?_ hz
        · rw [sub_self, supNorm_zero']; omega
        · have := supNorm_sub_le_one_of_nbr hx'; omega
      have hS2 : ∀ z ∉ boxFinset x R, green d n (x' - z) - green d n (y - z) = 0 := by
        intro z hz
        refine green_diff_eq_zero_of_notMem_box ?_ ?_ hz
        · have hxx' := supNorm_sub_le_one_of_nbr hx'; omega
        · have hxy' : supNorm (x - y) ≤ L + 1 := by
            have := supNorm_le_graphNorm (x - y)
            omega
          omega
      have hcomb : l2Norm (fun z => green d n (x - z) - green d n (y - z))
          ≤ l2Norm (fun z => green d n (x - z) - green d n (x' - z))
            + l2Norm (fun z => green d n (x' - z) - green d n (y - z)) := by
        have heq : (fun z => (green d n (x - z) - green d n (x' - z))
              + (green d n (x' - z) - green d n (y - z)))
            = fun z => green d n (x - z) - green d n (y - z) := by
          funext z; ring
        calc l2Norm (fun z => green d n (x - z) - green d n (y - z))
            = l2Norm (fun z => (green d n (x - z) - green d n (x' - z))
                + (green d n (x' - z) - green d n (y - z))) := by rw [heq]
          _ ≤ l2Norm (fun z => green d n (x - z) - green d n (x' - z))
                + l2Norm (fun z => green d n (x' - z) - green d n (y - z)) :=
              l2Norm_add_le_of_support hS1 hS2
      calc l2Norm (fun z => green d n (x - z) - green d n (y - z))
          ≤ l2Norm (fun z => green d n (x - z) - green d n (x' - z))
              + l2Norm (fun z => green d n (x' - z) - green d n (y - z)) := hcomb
        _ ≤ B + (L : ℝ) * B := add_le_add hone hIH
        _ = ((L : ℝ) + 1) * B := by ring
        _ = ((L + 1 : ℕ) : ℝ) * B := by push_cast; ring

/-- The `supAbs` form of `exists_green_space_l2_bound_of_step`. -/
theorem exists_green_space_sup_bound_of_step {n : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hstep : ∀ x x' : Site d, x' ∈ nbrFinset x →
      supAbs (fun z => green d n (x - z) - green d n (x' - z)) ≤ B) :
    ∀ L : ℕ, ∀ x y : Site d, graphNorm (x - y) = L →
      supAbs (fun z => green d n (x - z) - green d n (y - z)) ≤ (L : ℝ) * B := by
  intro L
  induction L with
  | zero =>
      intro x y hL
      have hxy : x = y := sub_eq_zero.mp (graphNorm_eq_zero_iff.mp hL)
      subst hxy
      have hz0 : (fun z => green d n (x - z) - green d n (x - z)) = fun _ : Site d => (0:ℝ) := by
        funext z; ring
      rw [hz0]
      have h0 : supAbs (fun _ : Site d => (0:ℝ)) = 0 := by unfold supAbs; simp
      rw [h0]; positivity
  | succ L ih =>
      intro x y hL
      have hxy : x ≠ y := by
        intro hcontra
        have hz0 : graphNorm (0 : Site d) = 0 := graphNorm_eq_zero_iff.mpr rfl
        rw [hcontra, sub_self, hz0] at hL
        omega
      obtain ⟨x', hx', hpred⟩ := exists_nbr_graphNorm_pred hxy
      have hLx' : graphNorm (x' - y) = L := by omega
      have hIH := ih x' y hLx'
      have hone := hstep x x' hx'
      set R : ℕ := n + L + 2 with hRdef
      have hS1 : ∀ z ∉ boxFinset x R, green d n (x - z) - green d n (x' - z) = 0 := by
        intro z hz
        refine green_diff_eq_zero_of_notMem_box ?_ ?_ hz
        · rw [sub_self, supNorm_zero']; omega
        · have := supNorm_sub_le_one_of_nbr hx'; omega
      have hS2 : ∀ z ∉ boxFinset x R, green d n (x' - z) - green d n (y - z) = 0 := by
        intro z hz
        refine green_diff_eq_zero_of_notMem_box ?_ ?_ hz
        · have hxx' := supNorm_sub_le_one_of_nbr hx'; omega
        · have hxy' : supNorm (x - y) ≤ L + 1 := by
            have := supNorm_le_graphNorm (x - y)
            omega
          omega
      have hcomb : supAbs (fun z => green d n (x - z) - green d n (y - z))
          ≤ supAbs (fun z => green d n (x - z) - green d n (x' - z))
            + supAbs (fun z => green d n (x' - z) - green d n (y - z)) := by
        have heq : (fun z => (green d n (x - z) - green d n (x' - z))
              + (green d n (x' - z) - green d n (y - z)))
            = fun z => green d n (x - z) - green d n (y - z) := by
          funext z; ring
        calc supAbs (fun z => green d n (x - z) - green d n (y - z))
            = supAbs (fun z => (green d n (x - z) - green d n (x' - z))
                + (green d n (x' - z) - green d n (y - z))) := by rw [heq]
          _ ≤ supAbs (fun z => green d n (x - z) - green d n (x' - z))
                + supAbs (fun z => green d n (x' - z) - green d n (y - z)) :=
              supAbs_add_le_of_support hS1 hS2
      calc supAbs (fun z => green d n (x - z) - green d n (y - z))
          ≤ supAbs (fun z => green d n (x - z) - green d n (x' - z))
              + supAbs (fun z => green d n (x' - z) - green d n (y - z)) := hcomb
        _ ≤ B + (L : ℝ) * B := add_le_add hone hIH
        _ = ((L : ℝ) + 1) * B := by ring
        _ = ((L + 1 : ℕ) : ℝ) * B := by push_cast; ring

/-! ### Dimension one: the exact one-step bound via the tail identity -/

theorem graphNorm_one_eq (c : ℤ) : graphNorm (![c] : Site 1) = c.natAbs := by
  unfold graphNorm
  rw [show (Finset.univ : Finset (Fin 1)) = {0} from rfl]
  simp

/-- The unconditional reflection symmetry of the truncated Green function in dimension
one: `green 1 n ![c] = green 1 n ![-c]` for EVERY `c` (no sign restriction), unlike
`Parking.green_one_sub'` which needs `0 ≤ c`.  From `Parking.green_neg` alone. -/
theorem green_one_eq_neg (n : ℕ) (c : ℤ) :
    green 1 n (![c] : Site 1) = green 1 n (![-c] : Site 1) := by
  have hval : (![-c] : Site 1) = -(![c] : Site 1) := by
    funext i; fin_cases i; simp
  rw [hval, green_neg]

/-- The one-step forward difference reverses sign under the involution `c ↦ -c-1`, for
EVERY `c`: `Parking.green_one_eq_neg` applied to `c` and to `c+1`. -/
theorem green_one_step_diff_neg (n : ℕ) (c : ℤ) :
    green 1 n ![c] - green 1 n ![c + 1]
      = -(green 1 n ![-c - 1] - green 1 n ![-c - 1 + 1]) := by
  have h1 : green 1 n ![c] = green 1 n ![-c] := green_one_eq_neg n c
  have h2 : green 1 n ![c + 1] = green 1 n ![-(c + 1)] := green_one_eq_neg n (c + 1)
  have h3 : (![-(c + 1)] : Site 1) = ![-c - 1] := by
    funext i; fin_cases i; simp; ring
  have h4 : (-c - 1 + 1 : ℤ) = -c := by ring
  rw [h1, h2, h3, h4]
  ring

/-- **The one-step forward-difference squared is bounded by four times the square of the
tail at the nonnegative reduction of `c`, in every dimension-one case, no sign
restriction.** -/
theorem sq_green_one_step_le (n : ℕ) (c : ℤ) :
    (green 1 n ![c] - green 1 n ![c + 1]) ^ 2
      ≤ 4 * (min 1 ((n : ℝ) / (((min c.natAbs (c + 1).natAbs : ℕ) : ℝ) + 1) ^ 2)) ^ 2 := by
  by_cases hc : 0 ≤ c
  · have hmin : min c.natAbs (c + 1).natAbs = c.natAbs := by omega
    rw [hmin]
    have heq := green_one_sub' n hc
    have hcast : ((c.natAbs : ℕ) : ℝ) = (c : ℝ) := by
      have hna : c.natAbs = c.toNat := by omega
      rw [hna]
      have : ((c.toNat : ℕ) : ℤ) = c := by omega
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
    have h1 : LatticeProb.srwTail n c ≤ 1 := srwTail_le_one n c
    have h2 : LatticeProb.srwTail n c ≤ (n : ℝ) / (((c.natAbs : ℕ) : ℝ) + 1) ^ 2 := by
      rw [hcast]; exact srwTail_le_sq n hc
    have hmn : LatticeProb.srwTail n c ≤ min 1 ((n : ℝ) / (((c.natAbs : ℕ) : ℝ) + 1) ^ 2) :=
      le_min h1 h2
    have hnn : 0 ≤ LatticeProb.srwTail n c := by
      rw [LatticeProb.srwTail]
      exact Finset.sum_nonneg fun k _ => LatticeProb.srwHeat_nonneg _ _
    have hmnn : 0 ≤ min 1 ((n : ℝ) / (((c.natAbs : ℕ) : ℝ) + 1) ^ 2) :=
      le_min (by norm_num) (by positivity)
    rw [heq]
    nlinarith [hmn, hnn, hmnn]
  · have hc' : (0 : ℤ) ≤ -c - 1 := by omega
    have hmin : min c.natAbs (c + 1).natAbs = (-c - 1).natAbs := by omega
    rw [hmin]
    have hdiff := green_one_step_diff_neg n c
    have heq := green_one_sub' n hc'
    have hval : green 1 n ![c] - green 1 n ![c + 1] = -(2 * LatticeProb.srwTail n (-c - 1)) := by
      rw [hdiff, heq]
    have hcast : (((-c - 1).natAbs : ℕ) : ℝ) = ((-c - 1 : ℤ) : ℝ) := by
      have hna : (-c - 1).natAbs = (-c - 1).toNat := by omega
      rw [hna]
      have : (((-c - 1).toNat : ℕ) : ℤ) = -c - 1 := by omega
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
    have h1 : LatticeProb.srwTail n (-c - 1) ≤ 1 := srwTail_le_one n (-c - 1)
    have h2 : LatticeProb.srwTail n (-c - 1)
        ≤ (n : ℝ) / ((((-c - 1).natAbs : ℕ) : ℝ) + 1) ^ 2 := by
      rw [hcast]; exact srwTail_le_sq n hc'
    have hmn : LatticeProb.srwTail n (-c - 1)
        ≤ min 1 ((n : ℝ) / ((((-c - 1).natAbs : ℕ) : ℝ) + 1) ^ 2) := le_min h1 h2
    have hnn : 0 ≤ LatticeProb.srwTail n (-c - 1) := by
      rw [LatticeProb.srwTail]
      exact Finset.sum_nonneg fun k _ => LatticeProb.srwHeat_nonneg _ _
    have hmnn : 0 ≤ min 1 ((n : ℝ) / ((((-c - 1).natAbs : ℕ) : ℝ) + 1) ^ 2) :=
      le_min (by norm_num) (by positivity)
    rw [hval]
    nlinarith [hmn, hnn, hmnn]

/-- **The `tsum` of the one-step forward-difference squared, over `Site 1`, reduced to a
finite `Finset` sum over `[-n, n]`**: `green 1 n` vanishes outside radius `n`, and so does
its neighbour, once `|c| > n`. -/
theorem tsum_green_one_step_sq_eq (n : ℕ) :
    ∑' c : ℤ, (green 1 n ![c] - green 1 n ![c + 1]) ^ 2
      = ∑ c ∈ Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1),
          (green 1 n ![c] - green 1 n ![c + 1]) ^ 2 := by
  refine tsum_eq_sum fun c hc => ?_
  simp only [Finset.mem_Icc, not_and, not_le] at hc
  have hc1 : n ≤ (c : ℤ).natAbs := by omega
  have hc2 : n ≤ (c + 1 : ℤ).natAbs := by omega
  have hzero1 : green 1 n (![c] : Site 1) = 0 :=
    green_eq_zero_of_le (by rw [graphNorm_one_eq]; exact hc1)
  have hzero2 : green 1 n (![c + 1] : Site 1) = 0 :=
    green_eq_zero_of_le (by rw [graphNorm_one_eq]; exact hc2)
  rw [hzero1, hzero2]; ring

/-- **A crude, but unconditional, pointwise bound on the squared one-step forward
difference**, dropping the sharp `Chebyshev` refinement of `sq_green_one_step_le`: at most
`4`, at every `c` and every horizon, since `|h(c)| = 2 * srwTail n c' ≤ 2` for the
nonnegative reduction `c'` of `c`. -/
theorem sq_green_one_step_le_four (n : ℕ) (c : ℤ) :
    (green 1 n ![c] - green 1 n ![c + 1]) ^ 2 ≤ 4 := by
  have h := sq_green_one_step_le n c
  set K : ℝ := (n : ℝ) / (((min c.natAbs (c + 1).natAbs : ℕ) : ℝ) + 1) ^ 2 with hKdef
  have hm : min (1 : ℝ) K ≤ 1 := min_le_left _ _
  have hm0 : (0 : ℝ) ≤ min (1 : ℝ) K := le_min (by norm_num) (by rw [hKdef]; positivity)
  nlinarith [h, hm, hm0]

/-- **The finite-sum bound on the one-step forward-difference squared, over the box the
truncated Green function is supported in**: crude cardinality bound, `4` times the size of
`Finset.Icc (-(n+1)) (n+1)`. -/
theorem sum_green_one_step_sq_le (n : ℕ) :
    ∑ c ∈ Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1), (green 1 n ![c] - green 1 n ![c + 1]) ^ 2
      ≤ 4 * (2 * (n : ℝ) + 3) := by
  have hcard : (Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1)).card = 2 * n + 3 := by
    rw [Int.card_Icc]
    have heq : ((n : ℤ) + 1 + 1 - (-(n : ℤ) - 1)) = ((2 * n + 3 : ℕ) : ℤ) := by push_cast; ring
    rw [heq, Int.toNat_natCast]
  calc ∑ c ∈ Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1), (green 1 n ![c] - green 1 n ![c + 1]) ^ 2
      ≤ ∑ _c ∈ Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1), (4 : ℝ) :=
        Finset.sum_le_sum fun c _ => sq_green_one_step_le_four n c
    _ = (Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1)).card * 4 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (2 * n + 3 : ℕ) * (4 : ℝ) := by rw [hcard]
    _ = 4 * (2 * (n : ℝ) + 3) := by push_cast; ring

/-- **The `tsum` bound**, combining `tsum_green_one_step_sq_eq` and
`sum_green_one_step_sq_le`. -/
theorem tsum_green_one_step_sq_le (n : ℕ) :
    ∑' c : ℤ, (green 1 n ![c] - green 1 n ![c + 1]) ^ 2 ≤ 4 * (2 * (n : ℝ) + 3) := by
  rw [tsum_green_one_step_sq_eq]
  exact sum_green_one_step_sq_le n

/-! ### Transporting the `ℤ`-indexed one-step bound to `Site 1` and to a general neighbour
pair -/

/-- The `ℤ`-indexing equivalence of `Site 1`, via evaluation at the unique coordinate. -/
def site1ToInt : Site 1 ≃ ℤ := Equiv.funUnique (Fin 1) ℤ

theorem site1ToInt_apply (w : Site 1) : site1ToInt w = w 0 := rfl

/-- **The one-step `tsum` bound in dimension one, at the forward neighbour `x + unit 0`.** -/
theorem tsum_green_one_step_sq_plus_le (n : ℕ) (x : Site 1) :
    ∑' z : Site 1, (green 1 n (x - z) - green 1 n (x + unit 0 - z)) ^ 2
      ≤ 4 * (2 * (n : ℝ) + 3) := by
  have hreidx : ∑' z : Site 1, (green 1 n (x - z) - green 1 n (x + unit 0 - z)) ^ 2
      = ∑' w : Site 1, (green 1 n w - green 1 n (w + unit 0)) ^ 2 := by
    rw [← tsum_comp_subLeft x (fun w => (green 1 n w - green 1 n (w + unit 0)) ^ 2)]
    refine tsum_congr fun z => ?_
    congr 2
    have : x + unit 0 - z = (x - z) + unit 0 := by abel
    rw [this]
  rw [hreidx]
  have hpt : ∀ w : Site 1, (green 1 n w - green 1 n (w + unit 0)) ^ 2
      = (green 1 n ![site1ToInt w] - green 1 n ![site1ToInt w + 1]) ^ 2 := by
    intro w
    show (green 1 n w - green 1 n (w + unit 0)) ^ 2
        = (green 1 n ![w 0] - green 1 n ![w 0 + 1]) ^ 2
    conv_lhs => rw [site_one_eq w, site_one_add_unit (w 0)]
  rw [tsum_congr hpt]
  have hE : ∑' w : Site 1, (green 1 n ![site1ToInt w] - green 1 n ![site1ToInt w + 1]) ^ 2
      = ∑' c : ℤ, (green 1 n ![c] - green 1 n ![c + 1]) ^ 2 :=
    site1ToInt.tsum_eq (fun c => (green 1 n ![c] - green 1 n ![c + 1]) ^ 2)
  rw [hE]
  exact tsum_green_one_step_sq_le n

/-- **The one-step `l2Norm` bound in dimension one, at the forward neighbour.** -/
theorem exists_green_space_step_l2_bound_one_plus (n : ℕ) (x : Site 1) :
    l2Norm (fun z => green 1 n (x - z) - green 1 n (x + unit 0 - z))
      ≤ 2 * Real.sqrt (2 * (n : ℝ) + 3) := by
  unfold l2Norm
  calc Real.sqrt (∑' z : Site 1, (green 1 n (x - z) - green 1 n (x + unit 0 - z)) ^ 2)
      ≤ Real.sqrt (4 * (2 * (n : ℝ) + 3)) :=
        Real.sqrt_le_sqrt (tsum_green_one_step_sq_plus_le n x)
    _ = 2 * Real.sqrt (2 * (n : ℝ) + 3) := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
        congr 1
        rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]

/-- **`l2Norm` of a Green-kernel difference is symmetric under swapping the two sites**:
`(f)^2 = (-f)^2`. -/
theorem l2Norm_green_diff_symm (n : ℕ) (a b : Site 1) :
    l2Norm (fun z => green 1 n (a - z) - green 1 n (b - z))
      = l2Norm (fun z => green 1 n (b - z) - green 1 n (a - z)) := by
  unfold l2Norm
  congr 1
  refine tsum_congr fun z => ?_
  ring

/-- **The one-step `l2Norm` bound in dimension one, at a fixed pair of neighbours,
unconditional (no citation).**  The forward case is `exists_green_space_step_l2_bound_one_plus`
directly; the backward case (`x' = x - unit 0`) reduces to it applied at `(x', x)`, since
`x = x' + unit 0`, by the symmetry `l2Norm_green_diff_symm`. -/
theorem exists_green_space_step_l2_bound_one (n : ℕ) {x x' : Site 1} (hx' : x' ∈ nbrFinset x) :
    l2Norm (fun z => green 1 n (x - z) - green 1 n (x' - z))
      ≤ 2 * Real.sqrt (2 * (n : ℝ) + 3) := by
  obtain ⟨i, hcase⟩ := mem_nbrFinset_iff.mp hx'
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  rcases hcase with hcase | hcase
  · subst hcase
    exact exists_green_space_step_l2_bound_one_plus n x
  · subst hcase
    have hgoal := exists_green_space_step_l2_bound_one_plus n (x - unit 0)
    have heq : (fun z : Site 1 => green 1 n (x - unit 0 - z)
          - green 1 n (x - unit 0 + unit 0 - z))
        = (fun z : Site 1 => green 1 n (x - unit 0 - z) - green 1 n (x - z)) := by
      funext z
      have hcancel : x - unit 0 + unit 0 = x := by abel
      rw [hcancel]
    rw [heq] at hgoal
    rw [l2Norm_green_diff_symm]
    exact hgoal

/-- **The `L`-step `l2Norm` comparison in dimension one, chaining
`exists_green_space_step_l2_bound_one` by `exists_green_space_l2_bound_of_step`.** -/
theorem exists_green_space_l2_bound_one (n : ℕ) (x y : Site 1) :
    l2Norm (fun z => green 1 n (x - z) - green 1 n (y - z))
      ≤ (graphNorm (x - y) : ℝ) * (2 * Real.sqrt (2 * (n : ℝ) + 3)) :=
  exists_green_space_l2_bound_of_step (n := n)
    (B := 2 * Real.sqrt (2 * (n : ℝ) + 3)) (by positivity)
    (fun a b hb => exists_green_space_step_l2_bound_one n hb) (graphNorm (x - y)) x y rfl

/-! ### Dimension one, `supAbs`: a horizon-independent one-step bound -/

/-- **The squared one-step forward difference is at most `4`, unconditionally (dropping
`sq_green_one_step_le`'s sharper Chebyshev refinement), for every `c` and `n`.** -/
theorem abs_green_one_step_le_two (n : ℕ) (c : ℤ) :
    |green 1 n ![c] - green 1 n ![c + 1]| ≤ 2 := by
  have h := sq_green_one_step_le_four n c
  nlinarith [abs_nonneg (green 1 n ![c] - green 1 n ![c + 1]),
    sq_abs (green 1 n ![c] - green 1 n ![c + 1])]

theorem exists_green_space_step_sup_bound_one_plus (n : ℕ) (x : Site 1) :
    supAbs (fun z => green 1 n (x - z) - green 1 n (x + unit 0 - z)) ≤ 2 := by
  unfold supAbs
  refine ciSup_le fun z => ?_
  dsimp only
  have heq : x + unit 0 - z = (x - z) + unit 0 := by abel
  rw [heq]
  conv_lhs => rw [site_one_eq (x - z), site_one_add_unit ((x - z) 0)]
  exact abs_green_one_step_le_two n ((x - z) 0)

/-- **`supAbs` of a Green-kernel difference is symmetric under swapping the two sites.** -/
theorem supAbs_green_diff_symm (n : ℕ) (a b : Site 1) :
    supAbs (fun z => green 1 n (a - z) - green 1 n (b - z))
      = supAbs (fun z => green 1 n (b - z) - green 1 n (a - z)) := by
  unfold supAbs
  congr 1
  funext z
  rw [abs_sub_comm]

/-- **The one-step `supAbs` bound in dimension one, at a fixed pair of neighbours,
unconditional (no citation, no dependence on the horizon `n`).** -/
theorem exists_green_space_step_sup_bound_one (n : ℕ) {x x' : Site 1} (hx' : x' ∈ nbrFinset x) :
    supAbs (fun z => green 1 n (x - z) - green 1 n (x' - z)) ≤ 2 := by
  obtain ⟨i, hcase⟩ := mem_nbrFinset_iff.mp hx'
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  rcases hcase with hcase | hcase
  · subst hcase
    exact exists_green_space_step_sup_bound_one_plus n x
  · subst hcase
    have hgoal := exists_green_space_step_sup_bound_one_plus n (x - unit 0)
    have heq : (fun z : Site 1 => green 1 n (x - unit 0 - z)
          - green 1 n (x - unit 0 + unit 0 - z))
        = (fun z : Site 1 => green 1 n (x - unit 0 - z) - green 1 n (x - z)) := by
      funext z
      have hcancel : x - unit 0 + unit 0 = x := by abel
      rw [hcancel]
    rw [heq] at hgoal
    rw [supAbs_green_diff_symm]
    exact hgoal

/-- **The `L`-step `supAbs` comparison in dimension one.** -/
theorem exists_green_space_sup_bound_one (n : ℕ) (x y : Site 1) :
    supAbs (fun z => green 1 n (x - z) - green 1 n (y - z)) ≤ (graphNorm (x - y) : ℝ) * 2 :=
  exists_green_space_sup_bound_of_step (n := n) (B := (2 : ℝ)) (by norm_num)
    (fun a b hb => exists_green_space_step_sup_bound_one n hb) (graphNorm (x - y)) x y rfl

/-! ### Dimension two: the truncated shell sum, via the PROVED `GreenGradient 2` -/

/-- **The dimension-two analogue of `Parking.Support.SpatGreenShift.sum_sq_rpow_le`**: the
shell sum diverges logarithmically over the WHOLE lattice at `d = 2` (unlike `d ≥ 3`, where
it converges), so it is bounded here only up to the horizon `n`, exactly as
`Parking.Support.GammaSum.gamma_sum_of_gradient`'s own dimension-two branch. -/
theorem sum_sq_rpow_le_two (n : ℕ) :
    ∑ y ∈ boxFinset (0 : Site 2) n, ((1 + (supNorm y : ℝ)) ^ ((1 : ℝ) - ((2 : ℕ) : ℝ))) ^ 2
      ≤ 1 + 8 * Real.log ((n : ℝ) + 1) := by
  set f : ℕ → ℝ := fun k => ((1 + (k : ℝ)) ^ ((1 : ℝ) - ((2 : ℕ) : ℝ))) ^ 2 with hfdef
  have hradial : ∑ y ∈ boxFinset (0 : Site 2) n, f (supNorm y)
      = f 0 + ∑ k ∈ Finset.Icc 1 n, (shellCard 2 k : ℝ) * f k := sum_box_radial f n
  have hf0 : f 0 = 1 := by rw [hfdef]; norm_num
  set K : ℝ := 2 * ((2 : ℕ) : ℝ) * 2 ^ ((2 : ℕ) - 1) with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  have hterm : ∀ k ∈ Finset.Icc 1 n,
      (shellCard 2 k : ℝ) * f k ≤ K * (1 + (k : ℝ)) ^ ((1 : ℝ) - ((2 : ℕ) : ℝ)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have h1 : (shellCard 2 k : ℝ) * f k
        ≤ (2 * ((2 : ℕ) : ℝ) * (2 * (k : ℝ) + 1) ^ ((2 : ℕ) - 1)) * f k :=
      mul_le_mul_of_nonneg_right (shellCard_le 2 hk.1) (by rw [hfdef]; positivity)
    have h2 : (2 * (k : ℝ) + 1) ^ ((2 : ℕ) - 1)
        ≤ 2 ^ ((2 : ℕ) - 1) * (1 + (k : ℝ)) ^ ((2 : ℕ) - 1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have hfk : 0 ≤ f k := by rw [hfdef]; positivity
    have h3 : (2 * ((2 : ℕ) : ℝ) * (2 * (k : ℝ) + 1) ^ ((2 : ℕ) - 1)) * f k
        ≤ (2 * ((2 : ℕ) : ℝ) * (2 ^ ((2 : ℕ) - 1) * (1 + (k : ℝ)) ^ ((2 : ℕ) - 1))) * f k := by
      refine mul_le_mul_of_nonneg_right ?_ hfk
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : (2 * ((2 : ℕ) : ℝ) * (2 ^ ((2 : ℕ) - 1) * (1 + (k : ℝ)) ^ ((2 : ℕ) - 1))) * f k
        = K * (1 + (k : ℝ)) ^ ((1 : ℝ) - ((2 : ℕ) : ℝ)) := by
      rw [hfdef, hKdef, ← rpow_shell_combine (d := 2) (by norm_num) k]
      ring
    linarith
  have hsum_shell : ∑ k ∈ Finset.Icc 1 n, (shellCard 2 k : ℝ) * f k
      ≤ ∑ k ∈ Finset.Icc 1 n, K * (1 + (k : ℝ)) ^ ((1 : ℝ) - ((2 : ℕ) : ℝ)) :=
    Finset.sum_le_sum hterm
  have hpow : ∀ k : ℕ, (1 + (k : ℝ)) ^ ((1 : ℝ) - ((2 : ℕ) : ℝ)) = 1 / ((k : ℝ) + 1) := by
    intro k
    have hx : (0 : ℝ) < 1 + (k : ℝ) := by positivity
    rw [show (1 : ℝ) - ((2 : ℕ) : ℝ) = -1 by push_cast; ring, Real.rpow_neg_one]
    rw [one_div]; congr 1; ring
  have hlog : ∑ k ∈ Finset.Icc 1 n, K * (1 + (k : ℝ)) ^ ((1 : ℝ) - ((2 : ℕ) : ℝ))
      ≤ K * Real.log ((n : ℝ) + 1) := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hKnn
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => hpow k)) ?_
    exact sum_inv_succ_le_log n
  have hK8 : K = 8 := by rw [hKdef]; norm_num
  rw [hK8] at hlog hsum_shell
  rw [hradial, hf0]
  linarith [hsum_shell, hlog]

/-- **The one-step `l2Norm` bound in dimension two, at a FIXED constant `C` witnessing
`GreenGradient 2`** (mirroring `Parking.Support.SpatGreenShift.exists_green_space_step_l2_bound`'s
own parametrization by an explicit `C`, rather than re-deriving a fresh witness at every call,
so that the SAME `C` chains through the `L`-step induction). -/
theorem exists_green_space_step_l2_bound_two {C : ℝ} (hC : 0 < C)
    (hgradraw : ∀ m : ℕ, 1 ≤ m → ∀ y z : Site 2, z ∈ nbrFinset y →
      |green 2 m y - green 2 m z| ≤ C * (1 + (graphNorm y : ℝ)) ^ (1 - ((2:ℕ) : ℝ)))
    {n : ℕ} (hn : 1 ≤ n) {x x' : Site 2} (hx' : x' ∈ nbrFinset x) :
    l2Norm (fun z => green 2 n (x - z) - green 2 n (x' - z))
      ≤ C * Real.sqrt (1 + 8 * Real.log ((n : ℝ) + 2)) := by
  set f : Site 2 → ℝ := fun z => green 2 n (x - z) - green 2 n (x' - z) with hfdef
  have hzero : ∀ z ∉ boxFinset x (n + 1), f z = 0 := by
    intro z hz
    exact green_diff_eq_zero_of_notMem_box (by rw [sub_self, supNorm_zero']; omega)
      (by have := supNorm_sub_le_one_of_nbr hx'; omega) hz
  have hsq : ∀ z : Site 2,
      f z ^ 2 ≤ C ^ 2 * ((1 + (supNorm (x - z) : ℝ)) ^ ((1 : ℝ) - ((2 : ℕ) : ℝ))) ^ 2 := by
    intro z
    have h1 : |f z| ≤ C * (1 + (graphNorm (x - z) : ℝ)) ^ ((1 : ℝ) - ((2 : ℕ) : ℝ)) :=
      abs_green_nbr_diff_le hgradraw hn hx' z
    have hanti : (1 + (graphNorm (x - z) : ℝ)) ^ ((1 : ℝ) - ((2 : ℕ) : ℝ))
        ≤ (1 + (supNorm (x - z) : ℝ)) ^ ((1 : ℝ) - ((2 : ℕ) : ℝ)) :=
      rpow_radial_antitone (by norm_num) (supNorm_le_graphNorm (x - z))
    have h2 : |f z| ≤ C * (1 + (supNorm (x - z) : ℝ)) ^ ((1 : ℝ) - ((2 : ℕ) : ℝ)) :=
      le_trans h1 (mul_le_mul_of_nonneg_left hanti hC.le)
    have hsqle : f z ^ 2 ≤ (C * (1 + (supNorm (x - z) : ℝ)) ^ ((1 : ℝ) - ((2 : ℕ) : ℝ))) ^ 2 := by
      have := sq_abs (f z)
      nlinarith [abs_nonneg (f z), h2, hC.le,
        Real.rpow_pos_of_pos (show (0:ℝ) < 1 + (supNorm (x - z) : ℝ) by positivity)
          ((1 : ℝ) - ((2 : ℕ) : ℝ))]
    calc f z ^ 2 ≤ (C * (1 + (supNorm (x - z) : ℝ)) ^ ((1 : ℝ) - ((2 : ℕ) : ℝ))) ^ 2 := hsqle
      _ = C ^ 2 * ((1 + (supNorm (x - z) : ℝ)) ^ ((1 : ℝ) - ((2 : ℕ) : ℝ))) ^ 2 := by ring
  have hstep : (∑' z : Site 2, f z ^ 2) ≤ C ^ 2 * (1 + 8 * Real.log ((n : ℝ) + 2)) := by
    have heq : (∑' z : Site 2, f z ^ 2) = ∑ z ∈ boxFinset x (n + 1), f z ^ 2 :=
      tsum_eq_sum (fun z hz => by rw [hzero z hz]; ring)
    rw [heq]
    have hcast : (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by push_cast; ring
    calc ∑ z ∈ boxFinset x (n + 1), f z ^ 2
        ≤ ∑ z ∈ boxFinset x (n + 1),
            C ^ 2 * ((1 + (supNorm (x - z) : ℝ)) ^ ((1 : ℝ) - ((2 : ℕ) : ℝ))) ^ 2 :=
          Finset.sum_le_sum fun z _ => hsq z
      _ = C ^ 2 * ∑ z ∈ boxFinset x (n + 1),
            ((1 + (supNorm (x - z) : ℝ)) ^ ((1 : ℝ) - ((2 : ℕ) : ℝ))) ^ 2 := by
          rw [Finset.mul_sum]
      _ = C ^ 2 * ∑ w ∈ boxFinset (0 : Site 2) (n + 1),
            ((1 + (supNorm w : ℝ)) ^ ((1 : ℝ) - ((2 : ℕ) : ℝ))) ^ 2 := by
          rw [sum_boxFinset_shift x (n + 1)
            (fun k => ((1 + (k : ℝ)) ^ ((1 : ℝ) - ((2 : ℕ) : ℝ))) ^ 2)]
      _ ≤ C ^ 2 * (1 + 8 * Real.log (((n + 1 : ℕ) : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (sum_sq_rpow_le_two (n + 1)) (sq_nonneg C)
      _ = C ^ 2 * (1 + 8 * Real.log ((n : ℝ) + 2)) := by rw [hcast]
  unfold l2Norm
  rw [hfdef] at hstep ⊢
  calc Real.sqrt (∑' z : Site 2, f z ^ 2)
      ≤ Real.sqrt (C ^ 2 * (1 + 8 * Real.log ((n : ℝ) + 2))) := by
        rw [hfdef]; exact Real.sqrt_le_sqrt hstep
    _ = C * Real.sqrt (1 + 8 * Real.log ((n : ℝ) + 2)) := by
        rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC.le]

/-- **The `L`-step `l2Norm` comparison in dimension two.** -/
theorem exists_green_space_l2_bound_two {C : ℝ} (hC : 0 < C)
    (hgradraw : ∀ m : ℕ, 1 ≤ m → ∀ y z : Site 2, z ∈ nbrFinset y →
      |green 2 m y - green 2 m z| ≤ C * (1 + (graphNorm y : ℝ)) ^ (1 - ((2:ℕ) : ℝ)))
    {n : ℕ} (hn : 1 ≤ n) (x y : Site 2) :
    l2Norm (fun z => green 2 n (x - z) - green 2 n (y - z))
      ≤ (graphNorm (x - y) : ℝ) * (C * Real.sqrt (1 + 8 * Real.log ((n : ℝ) + 2))) :=
  exists_green_space_l2_bound_of_step (n := n)
    (B := C * Real.sqrt (1 + 8 * Real.log ((n : ℝ) + 2))) (by positivity)
    (fun a b hb => exists_green_space_step_l2_bound_two hC hgradraw hn hb)
    (graphNorm (x - y)) x y rfl

/-! ### The combined wrapper, `1 ≤ d ≤ 3`, no `External` hypothesis (`GreenGradient` is
PROVED at `d = 2, 3`, and dimension one needs no citation) -/

/-- **The dimension-dependent rate factor this module's one-step bound achieves.**  For
`d = 1`, `√(2n+3)`; for `d = 2`, `√(1+8·log(n+2))`; for `d ≥ 3`, the `n`-independent
`√(1+2d·2^{d-1})` (`Parking.Support.SpatGreenShift`'s own bound, unchanged).  This is NOT
the paper's optimal `√κ_d(n)` at `d = 1`: the `d = 1` route here uses a crude cardinality
bound (`O(√n)`, matching `κ_1(n)` ITSELF rather than its square root) rather than the sharp
Chebyshev one (`O(n^{1/4}) = √κ_1(n)`) that `sq_green_one_step_le`'s pointwise bound already
supports.  The sharp rate is obtained in `Parking.Support.SpatGreenShiftLowDimSharp`, which
sums that pointwise bound after a `Finset.sum_nbij'` reflection-split of
`Finset.Icc (-(n+1)) (n+1)`, in place of the crude `sq_green_one_step_le_four` bound
`sum_green_one_step_sq_le` uses. -/
noncomputable def spatialStepRate (d n : ℕ) : ℝ :=
  if d = 1 then Real.sqrt (2 * (n : ℝ) + 3)
  else if d = 2 then Real.sqrt (1 + 8 * Real.log ((n : ℝ) + 2))
  else Real.sqrt (1 + 2 * (d : ℝ) * 2 ^ (d - 1))

/-- **The space-direction translated-kernel-difference comparison, `l2Norm` form, the FULL
range `1 ≤ d ≤ 3` `prop:spatial-scaling` needs, unconditionally (no `External` hypothesis):
`GreenGradient` is PROVED at `d = 2, 3` (`Parking.External.greenGradient`), and dimension
one needs no citation at all.** -/
theorem exists_green_space_shift_l2_bound_full (hd1 : 1 ≤ d) (hd3 : d ≤ 3) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n → ∀ x y : Site d,
      l2Norm (fun z => green d n (x - z) - green d n (y - z))
        ≤ K * spatialStepRate d n * (graphNorm (x - y) : ℝ) := by
  interval_cases d
  · refine ⟨2, by norm_num, fun n hn x y => ?_⟩
    have hb := exists_green_space_l2_bound_one n x y
    unfold spatialStepRate
    norm_num
    linarith [hb]
  · obtain ⟨C, hC, hgradraw⟩ := Parking.External.greenGradient 2 (by norm_num)
    refine ⟨C, hC, fun n hn x y => ?_⟩
    have hb := exists_green_space_l2_bound_two hC hgradraw hn x y
    unfold spatialStepRate
    norm_num
    linarith [hb]
  · obtain ⟨C, hC, hgradraw⟩ := Parking.External.greenGradient 3 (by norm_num)
    refine ⟨C, hC, fun n hn x y => ?_⟩
    have hb := exists_green_space_l2_bound (hd3 := le_refl 3) hC hgradraw hn
      (graphNorm (x - y)) x y rfl
    have hsqrt : Real.sqrt (1 + 2 * ((3:ℕ) : ℝ) * 2 ^ ((3:ℕ) - 1)) = 5 := by
      rw [show (1 + 2 * ((3:ℕ) : ℝ) * 2 ^ ((3:ℕ) - 1)) = 5 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5)]
    rw [hsqrt] at hb
    unfold spatialStepRate
    norm_num
    linarith [hb]

/-- **The space-direction translated-kernel-difference comparison, `supAbs` form, the FULL
range `1 ≤ d ≤ 3`, unconditionally, `n`-independent in every dimension.** -/
theorem exists_green_space_shift_sup_bound_full (hd1 : 1 ≤ d) (hd3 : d ≤ 3) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n → ∀ x y : Site d,
      supAbs (fun z => green d n (x - z) - green d n (y - z)) ≤ K * (graphNorm (x - y) : ℝ) := by
  interval_cases d
  · refine ⟨2, by norm_num, fun n _ x y => ?_⟩
    rw [mul_comm]
    exact exists_green_space_sup_bound_one n x y
  · exact exists_green_space_shift_sup_bound (by norm_num) (Parking.External.greenGradient 2 (by norm_num))
  · exact exists_green_space_shift_sup_bound (by norm_num) (Parking.External.greenGradient 3 (by norm_num))

end Parking

end
