/-
`eq:stopping-blocks` for a fixed configuration (`parking.tex:2806-2814`).

The paper's display is

    E ∑_{j<σ} ξ(X_j) ≤ ∑_{k≥0} E[1{σ>s_k} u_{ℓ_k}(X_{s_k};ξ)] ,

with the blocks `[0,N)`, `[N,2N)`, `[2N,4N)`, ….  Here it is proved for a fixed
field and a stopping time bounded by `n`, so the sum is finite: the boundaries
`blockBound N k` pass `n` at `k = n + 1`, and every later block is empty.

The one technical point is the truncation.  The Markov step of
`Parking/Support/BlockStop.lean` asks for a field bounded on the WHOLE lattice,
while the field of the lemma is not.  The field is therefore clipped to the box
of radius `3n + N` about the origin, and the clipping is undone at both ends
because the walk almost surely stays in the box of radius `n` up to time `n`
(`LatticeProb.ae_image_subset_boxFinset`) and because the odometer at time `ℓ`
about a site within `n` of the origin reads only the box of radius `n + ℓ`
(`Parking.u_eq_of_eqOn_box`).  On a block the stopping time reaches, the block's
start is below `n`, so its length is at most `max N (2n)` and `n + ℓ ≤ 3n + N`.
-/
import Parking.Support.BlockTools
import LatticeProb.Walk.RangeSecond

noncomputable section

namespace Parking

open MeasureTheory LatticeProb

variable {d : ℕ}

/-- The field read only inside the box of radius `R` about the origin. -/
def clipField (ζ : Site d → ℝ) (R : ℕ) : Site d → ℝ :=
  fun y => if y ∈ boxFinset (0 : Site d) R then ζ y else 0

theorem clipField_bound (ζ : Site d → ℝ) (R : ℕ) (y : Site d) :
    |clipField ζ R y| ≤ ∑ z ∈ boxFinset (0 : Site d) R, |ζ z| := by
  classical
  rw [clipField]
  by_cases hy : y ∈ boxFinset (0 : Site d) R
  · rw [if_pos hy]
    exact Finset.single_le_sum (f := fun z => |ζ z|) (fun z _ => abs_nonneg _) hy
  · rw [if_neg hy, abs_zero]
    exact Finset.sum_nonneg fun z _ => abs_nonneg _

theorem clipField_nonneg_bound (ζ : Site d → ℝ) (R : ℕ) :
    (0:ℝ) ≤ ∑ z ∈ boxFinset (0 : Site d) R, |ζ z| :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem clipField_eq_of_mem (ζ : Site d → ℝ) {R : ℕ} {y : Site d}
    (hy : y ∈ boxFinset (0 : Site d) R) : clipField ζ R y = ζ y := by
  rw [clipField, if_pos hy]

/-- On the event that the walk has stayed in the box of radius `t`, the clipped field
gives the same odometer at the walk's position, provided the box is large enough. -/
theorem u_clipField_eq (_hd : 1 ≤ d) (ζ : Site d → ℝ) {R t ℓ : ℕ} {y : Site d}
    (hy : y ∈ boxFinset (0 : Site d) t) (hR : t + ℓ ≤ R) :
    u (clipField ζ R) ℓ y = u ζ ℓ y := by
  refine u_eq_of_eqOn_box ℓ y fun w hw => ?_
  exact clipField_eq_of_mem ζ (boxFinset_mono hR (mem_boxFinset_add hy hw))

/-! ### Measurability of the block quantities -/

theorem dependsUpTo_blockSum (ζ : Site d → ℝ) {σ : (ℕ → Site d) → ℕ}
    (hσ : LatticeProb.IsWalkStopping σ) {n : ℕ} (hσn : ∀ X, σ X ≤ n) (s ℓ : ℕ) :
    LatticeProb.DependsUpTo n
      (fun X : ℕ → Site d => ∑ j ∈ Finset.Ico s (min (σ X) (s + ℓ)), ζ (X j)) := by
  intro X X' h
  have hσeq : σ X = σ X' := LatticeProb.dependsUpTo_of_isWalkStopping hσ hσn X X' h
  show (∑ j ∈ Finset.Ico s (min (σ X) (s + ℓ)), ζ (X j))
    = ∑ j ∈ Finset.Ico s (min (σ X') (s + ℓ)), ζ (X' j)
  rw [hσeq]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjlt : j < min (σ X') (s + ℓ) := (Finset.mem_Ico.mp hj).2
  exact congrArg ζ (h j (by have := hσn X'; omega))

theorem dependsUpTo_blockU (ζ : Site d → ℝ) {σ : (ℕ → Site d) → ℕ}
    (hσ : LatticeProb.IsWalkStopping σ) {n : ℕ} (hσn : ∀ X, σ X ≤ n) (s ℓ : ℕ) :
    LatticeProb.DependsUpTo n
      (fun X : ℕ → Site d => if s < σ X then u ζ ℓ (X s) else 0) := by
  intro X X' h
  have hσeq : σ X = σ X' := LatticeProb.dependsUpTo_of_isWalkStopping hσ hσn X X' h
  show (if s < σ X then u ζ ℓ (X s) else 0) = if s < σ X' then u ζ ℓ (X' s) else 0
  rw [hσeq]
  by_cases hlt : s < σ X'
  · rw [if_pos hlt, if_pos hlt, h s (by have := hσn X'; omega)]
  · rw [if_neg hlt, if_neg hlt]

theorem integrable_blockSum (hd : 1 ≤ d) (ζ : Site d → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ y, |ζ y| ≤ B) {σ : (ℕ → Site d) → ℕ}
    (hσ : LatticeProb.IsWalkStopping σ) {n : ℕ} (hσn : ∀ X, σ X ≤ n) (s ℓ : ℕ) (x : Site d) :
    Integrable (fun X : ℕ → Site d => ∑ j ∈ Finset.Ico s (min (σ X) (s + ℓ)), ζ (X j))
      (LatticeProb.siteWalkLaw d x) := by
  haveI : NeZero d := ⟨by omega⟩
  refine (integrable_const ((n : ℝ) * B)).mono'
    (LatticeProb.measurable_of_dependsUpTo
      (dependsUpTo_blockSum ζ hσ hσn s ℓ)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun X => ?_)
  rw [Real.norm_eq_abs]
  calc |∑ j ∈ Finset.Ico s (min (σ X) (s + ℓ)), ζ (X j)|
      ≤ ∑ j ∈ Finset.Ico s (min (σ X) (s + ℓ)), |ζ (X j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.Ico s (min (σ X) (s + ℓ)), B := Finset.sum_le_sum fun j _ => hB (X j)
    _ = ((min (σ X) (s + ℓ) - s : ℕ) : ℝ) * B := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ (n : ℝ) * B := by
        refine mul_le_mul_of_nonneg_right ?_ hB0
        have := hσn X
        exact_mod_cast (by omega : min (σ X) (s + ℓ) - s ≤ n)

theorem integrable_blockU (hd : 1 ≤ d) (ζ : Site d → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ y, |ζ y| ≤ B) {σ : (ℕ → Site d) → ℕ}
    (hσ : LatticeProb.IsWalkStopping σ) {n : ℕ} (hσn : ∀ X, σ X ≤ n) (s ℓ : ℕ) (x : Site d) :
    Integrable (fun X : ℕ → Site d => if s < σ X then u ζ ℓ (X s) else 0)
      (LatticeProb.siteWalkLaw d x) := by
  haveI : NeZero d := ⟨by omega⟩
  refine (integrable_const ((ℓ : ℝ) * B)).mono'
    (LatticeProb.measurable_of_dependsUpTo
      (dependsUpTo_blockU ζ hσ hσn s ℓ)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun X => ?_)
  by_cases hlt : s < σ X
  · rw [if_pos hlt, Real.norm_eq_abs, abs_of_nonneg (u_nonneg ζ ℓ (X s))]
    exact u_le_mul_of_le hd hB0 (fun y => le_trans (le_abs_self _) (hB y)) ℓ (X s)
  · rw [if_neg hlt, norm_zero]
    positivity

/-! ### The block decomposition of the whole reward -/

theorem ae_mem_boxFinset (hd : 1 ≤ d) (t : ℕ) (x : Site d) :
    ∀ᵐ X ∂(LatticeProb.siteWalkLaw d x), ∀ j ≤ t, X j ∈ boxFinset x t := by
  haveI : NeZero d := ⟨by omega⟩
  filter_upwards [LatticeProb.ae_image_subset_boxFinset hd x t] with X hX j hj
  exact hX (Finset.mem_image_of_mem X (Finset.mem_range.mpr (by omega)))

/-- **`eq:stopping-blocks`.**  The reward collected before a bounded stopping time is at
most the sum, over the dyadic blocks, of the odometer at the block's length started at the
walk's position at the block's start, on the event that the stopping time reaches the
block.  The field is truncated to a box for the Markov step and the truncation is undone
by the locality of the odometer. -/
theorem integral_stopping_reward_le (hd : 1 ≤ d) (hStopping : Parking.External.Stopping)
    (ζ : Site d → ℝ) {σ : (ℕ → Site d) → ℕ} (hσ : LatticeProb.IsWalkStopping σ) {n : ℕ}
    (hσn : ∀ X, σ X ≤ n) {N : ℕ} (hN : 1 ≤ N) :
    ∫ X, (∑ j ∈ Finset.range (σ X), ζ (X j)) ∂(LatticeProb.siteWalkLaw d (0 : Site d))
      ≤ ∑ k ∈ Finset.range (n + 1),
          ∫ X, (if blockBound N k < σ X then
              u ζ (blockBound N (k + 1) - blockBound N k) (X (blockBound N k)) else 0)
            ∂(LatticeProb.siteWalkLaw d (0 : Site d)) := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  set W := LatticeProb.siteWalkLaw d (0 : Site d) with hW
  set R : ℕ := 3 * n + N with hR
  set ζ' : Site d → ℝ := clipField ζ R with hζ'
  set B : ℝ := ∑ z ∈ boxFinset (0 : Site d) R, |ζ z| with hBdef
  have hB0 : 0 ≤ B := clipField_nonneg_bound ζ R
  have hB : ∀ y, |ζ' y| ≤ B := fun y => clipField_bound ζ R y
  have hae := ae_mem_boxFinset hd n (0 : Site d)
  -- the blocks reach beyond the horizon
  have hJ : n ≤ blockBound N (n + 1) := le_blockBound N hN n
  -- the truncated field agrees with the field along the walk
  have hstep1 : ∫ X, (∑ j ∈ Finset.range (σ X), ζ (X j)) ∂W
      = ∫ X, (∑ j ∈ Finset.range (min (σ X) (blockBound N (n + 1))), ζ' (X j)) ∂W := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with X hX
    have hmin : min (σ X) (blockBound N (n + 1)) = σ X :=
      min_eq_left (le_trans (hσn X) hJ)
    rw [hmin]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := by
      have := Finset.mem_range.mp hj
      have := hσn X
      omega
    have hmem : X j ∈ boxFinset (0 : Site d) R :=
      boxFinset_mono (by omega) (hX j hjn)
    rw [hζ', clipField_eq_of_mem ζ hmem]
  -- the blocks exhaust the reward
  have hstep2 : ∀ X : ℕ → Site d,
      (∑ j ∈ Finset.range (min (σ X) (blockBound N (n + 1))), ζ' (X j))
        = ∑ k ∈ Finset.range (n + 1),
            (∑ j ∈ Finset.Ico (blockBound N k)
              (min (σ X) (blockBound N k + (blockBound N (k + 1) - blockBound N k))),
              ζ' (X j)) := by
    intro X
    rw [← sum_blockReward ζ' σ N X (n + 1)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [blockReward_shiftPath]
  have hstep3 : ∫ X, (∑ j ∈ Finset.range (min (σ X) (blockBound N (n + 1))), ζ' (X j)) ∂W
      = ∑ k ∈ Finset.range (n + 1),
          ∫ X, (∑ j ∈ Finset.Ico (blockBound N k)
            (min (σ X) (blockBound N k + (blockBound N (k + 1) - blockBound N k))),
            ζ' (X j)) ∂W := by
    rw [← integral_finsetSum _ (fun k _ => integrable_blockSum hd ζ' hB0 hB hσ hσn _ _ 0)]
    exact integral_congr_ae (Filter.Eventually.of_forall hstep2)
  -- each block is bounded by the odometer of the truncated field
  have hstep4 : ∀ k ∈ Finset.range (n + 1),
      (∫ X, (∑ j ∈ Finset.Ico (blockBound N k)
          (min (σ X) (blockBound N k + (blockBound N (k + 1) - blockBound N k))),
          ζ' (X j)) ∂W)
        ≤ ∫ X, (if blockBound N k < σ X then
            u ζ' (blockBound N (k + 1) - blockBound N k) (X (blockBound N k)) else 0) ∂W :=
    fun k _ => integral_blockReward_le hd hStopping ζ' hB0 hB hσ hσn _ _ 0
  -- and the truncation is undone
  have hstep5 : ∀ k : ℕ,
      (∫ X, (if blockBound N k < σ X then
          u ζ' (blockBound N (k + 1) - blockBound N k) (X (blockBound N k)) else 0) ∂W)
        = ∫ X, (if blockBound N k < σ X then
            u ζ (blockBound N (k + 1) - blockBound N k) (X (blockBound N k)) else 0) ∂W := by
    intro k
    refine integral_congr_ae ?_
    filter_upwards [hae] with X hX
    by_cases hlt : blockBound N k < σ X
    · rw [if_pos hlt, if_pos hlt]
      have hbk : blockBound N k ≤ n := by have := hσn X; omega
      have hmem : X (blockBound N k) ∈ boxFinset (0 : Site d) n := hX _ hbk
      have hsz : n + (blockBound N (k + 1) - blockBound N k) ≤ R := by
        have h1 : blockBound N (k + 1) = max N (2 * blockBound N k) := rfl
        have h2 : blockBound N (k + 1) ≤ max N (2 * n) := by
          rw [h1]; omega
        have h3 : max N (2 * n) ≤ N + 2 * n := by omega
        omega
      rw [hζ', u_clipField_eq hd ζ hmem hsz]
    · rw [if_neg hlt, if_neg hlt]
  rw [hstep1, hstep3]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [← hstep5 k]
  exact hstep4 k hk

end Parking

end
