/-
The block decomposition of Step 2 of `lem:mean-horizon` (`parking.tex:2802-2826`).

Step 2 splits the horizon into the blocks `[0,N)`, `[N,2N)`, `[2N,4N)`, … and
bounds the reward collected in each block by the odometer at the block's length,
started at the walk's position at the block's start (`eq:stopping-blocks`).

The Lean form of "conditionally on the walk through time `s`" is
`LatticeProb.markov_fixed_general`, the Markov property at a deterministic time
with a future functional that reads the past.  The functional is the reward of
the block, written as a function of the past `X` and of the shifted path `Y`
through the GLUED path `glue s X Y`, which follows `X` before time `s` and `Y`
after it.  Three facts make the argument work.

* The glued path reads `X` only strictly before time `s`, so the functional
  reads the past only through the positions up to time `s`, which is what
  `markov_fixed_general` demands.
* `blockStop σ s ℓ X` is a genuine stopping time OF THE SHIFTED WALK for every
  fixed past `X`, bounded by the block's length.  This is the content of
  `isWalkStopping_blockStop`, and it is what turns the inner integral into an
  element of the set of stopping values, hence at most the odometer by the
  optimal stopping representation `lem:stopping`.
* The functional is bounded whenever the field is, which is why the caller
  truncates the field to a box before applying the bound.

Summing the blocks is `sum_blockReward`: the rewards of the first `J` blocks add
up to the reward collected before the stopping time truncated at the `J`-th
boundary, and the boundaries `blockBound N k = 2^{k-1}N` pass every horizon.
-/
import Parking.Support.Walk
import LatticeProb.Walk.Markov
import LatticeProb.Graph.ZdRepresentation
import Parking.External.Stopping
import Parking.Support.UFinite
import Parking.Support.UMoment

noncomputable section

namespace Parking

open MeasureTheory LatticeProb

variable {d : ℕ}

/-- The path that follows `X` strictly before time `s` and `Y` from time `s` on. -/
def glue (s : ℕ) (X Y : ℕ → Site d) : ℕ → Site d := fun j => if j < s then X j else Y (j - s)

theorem glue_shiftPath (s : ℕ) (X : ℕ → Site d) :
    glue s X (LatticeProb.shiftPath s X) = X := by
  funext j
  by_cases h : j < s
  · simp only [glue, if_pos h]
  · simp only [glue, if_neg h, LatticeProb.shiftPath]
    congr 1
    omega

theorem glue_congr_right {s k : ℕ} (X Y Y' : ℕ → Site d)
    (h : ∀ j ≤ k, Y j = Y' j) : ∀ j ≤ s + k, glue s X Y j = glue s X Y' j := by
  intro j hj
  by_cases hjs : j < s
  · simp only [glue, if_pos hjs]
  · simp only [glue, if_neg hjs]
    exact h (j - s) (by omega)

theorem glue_congr_left {s : ℕ} (X X' Y : ℕ → Site d)
    (h : ∀ j ≤ s, X j = X' j) : glue s X Y = glue s X' Y := by
  funext j
  by_cases hjs : j < s
  · simp only [glue, if_pos hjs]; exact h j (by omega)
  · simp only [glue, if_neg hjs]

/-- The stopping time of the block `[s, s+ℓ)`, read in the shifted path. -/
def blockStop (σ : (ℕ → Site d) → ℕ) (s ℓ : ℕ) (X Y : ℕ → Site d) : ℕ :=
  min (σ (glue s X Y)) (s + ℓ) - s

theorem blockStop_le (σ : (ℕ → Site d) → ℕ) (s ℓ : ℕ) (X Y : ℕ → Site d) :
    blockStop σ s ℓ X Y ≤ ℓ := by
  unfold blockStop
  omega

theorem blockStop_shiftPath (σ : (ℕ → Site d) → ℕ) (s ℓ : ℕ) (X : ℕ → Site d) :
    blockStop σ s ℓ X (LatticeProb.shiftPath s X) = min (σ X) (s + ℓ) - s := by
  rw [blockStop, glue_shiftPath]

/-- **The block stopping time is a stopping time of the shifted walk**, for every
fixed past. -/
theorem isWalkStopping_blockStop {σ : (ℕ → Site d) → ℕ} (hσ : LatticeProb.IsWalkStopping σ)
    (s ℓ : ℕ) (X : ℕ → Site d) : LatticeProb.IsWalkStopping (blockStop σ s ℓ X) := by
  intro k Y Y' hYY' hk
  have hkey : ∀ j ≤ s + k, glue s X Y j = glue s X Y' j := glue_congr_right X Y Y' hYY'
  unfold blockStop at hk ⊢
  rcases lt_or_ge (σ (glue s X Y)) (s + ℓ) with hlt | hge
  · rw [min_eq_left hlt.le] at hk
    have heq : σ (glue s X Y') = σ (glue s X Y) :=
      hσ (σ (glue s X Y)) (glue s X Y) (glue s X Y') (fun j hj => hkey j (by omega)) rfl
    rw [heq, min_eq_left hlt.le]
    exact hk
  · rw [min_eq_right hge] at hk
    have hkl : k = ℓ := by omega
    have hm'ge : s + ℓ ≤ σ (glue s X Y') := by
      by_contra hcon
      have hlt' : σ (glue s X Y') < s + ℓ := by omega
      have heq : σ (glue s X Y) = σ (glue s X Y') :=
        hσ (σ (glue s X Y')) (glue s X Y') (glue s X Y)
          (fun j hj => (hkey j (by omega)).symm) rfl
      omega
    rw [min_eq_right hm'ge]
    omega

/-! ### The reward collected in one block -/

/-- The reward collected in the block `[s, s+ℓ)` before the stopping time, read as a
function of the past `X` and of the shifted path `Y`.  It vanishes off `{σ > s}`, the
event on which `eq:stopping-blocks` collects the block. -/
def blockReward (ζ : Site d → ℝ) (σ : (ℕ → Site d) → ℕ) (s ℓ : ℕ)
    (X Y : ℕ → Site d) : ℝ :=
  if s < σ X then LatticeProb.Graph.Zd.sceneryPartialSum ζ (blockStop σ s ℓ X Y) Y else 0

theorem blockReward_shiftPath (ζ : Site d → ℝ) (σ : (ℕ → Site d) → ℕ) (s ℓ : ℕ)
    (X : ℕ → Site d) :
    blockReward ζ σ s ℓ X (LatticeProb.shiftPath s X)
      = ∑ j ∈ Finset.Ico s (min (σ X) (s + ℓ)), ζ (X j) := by
  rw [blockReward]
  by_cases hlt : s < σ X
  · rw [if_pos hlt, blockStop_shiftPath, LatticeProb.Graph.Zd.sceneryPartialSum,
      Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rfl
  · rw [if_neg hlt, Finset.Ico_eq_empty (by omega), Finset.sum_empty]

/-- The dyadic block boundaries `0, N, 2N, 4N, …` of `eq:stopping-blocks`. -/
def blockBound (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | (k + 1) => max N (2 * blockBound N k)

theorem blockBound_le_succ (N : ℕ) (k : ℕ) : blockBound N k ≤ blockBound N (k + 1) := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      rw [blockBound, blockBound]
      omega

theorem blockBound_mono (N : ℕ) : Monotone (blockBound N) :=
  monotone_nat_of_le_succ (blockBound_le_succ N)

theorem blockBound_succ_eq (N : ℕ) (_hN : 1 ≤ N) (k : ℕ) :
    blockBound N (k + 1) = 2 ^ k * N := by
  induction k with
  | zero => simp [blockBound]
  | succ k ih =>
      rw [blockBound, ih]
      have h1 : N ≤ 2 ^ k * N := Nat.le_mul_of_pos_left N (Nat.two_pow_pos k)
      rw [max_eq_right (by omega)]
      ring

theorem le_blockBound (N : ℕ) (hN : 1 ≤ N) (k : ℕ) : k ≤ blockBound N (k + 1) := by
  rw [blockBound_succ_eq N hN k]
  calc k ≤ 2 ^ k := Nat.le_of_lt (Nat.lt_two_pow_self)
    _ ≤ 2 ^ k * N := Nat.le_mul_of_pos_right _ hN

/-- **The blocks exhaust the reward.**  The rewards of the first `J` blocks add up to the
reward collected before the stopping time, truncated at the `J`-th boundary. -/
theorem sum_blockReward (ζ : Site d → ℝ) (σ : (ℕ → Site d) → ℕ) (N : ℕ)
    (X : ℕ → Site d) (J : ℕ) :
    ∑ k ∈ Finset.range J,
        blockReward ζ σ (blockBound N k) (blockBound N (k + 1) - blockBound N k) X
          (LatticeProb.shiftPath (blockBound N k) X)
      = ∑ j ∈ Finset.range (min (σ X) (blockBound N J)), ζ (X j) := by
  induction J with
  | zero => simp [blockBound]
  | succ J ih =>
      rw [Finset.sum_range_succ, ih, blockReward_shiftPath]
      have hb : blockBound N J + (blockBound N (J + 1) - blockBound N J)
          = blockBound N (J + 1) := by
        have := blockBound_le_succ N J
        omega
      rw [hb]
      have hIco : ∑ j ∈ Finset.Ico (blockBound N J) (min (σ X) (blockBound N (J + 1))), ζ (X j)
          = ∑ j ∈ Finset.Ico (min (σ X) (blockBound N J))
              (min (σ X) (blockBound N (J + 1))), ζ (X j) := by
        rcases le_or_gt (blockBound N J) (σ X) with hle | hgt
        · rw [min_eq_right hle]
        · have h1 : min (σ X) (blockBound N J) = σ X := min_eq_left (le_of_lt hgt)
          have h2 : min (σ X) (blockBound N (J + 1)) = σ X :=
            min_eq_left (le_trans (le_of_lt hgt) (blockBound_le_succ N J))
          rw [h1, h2, Finset.Ico_self]
          rw [Finset.Ico_eq_empty (by omega)]
      rw [hIco, Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.sum_Ico_consecutive _ (Nat.zero_le _)
          (min_le_min_left _ (blockBound_le_succ N J))]

/-! ### Measurability and boundedness -/

theorem measurable_glue (s : ℕ) :
    Measurable (fun p : (ℕ → Site d) × (ℕ → Site d) => glue s p.1 p.2) := by
  refine measurable_pi_lambda _ fun j => ?_
  by_cases h : j < s
  · simp only [glue, if_pos h]
    exact measurable_fst.eval
  · simp only [glue, if_neg h]
    exact measurable_snd.eval

theorem measurable_blockStop {σ : (ℕ → Site d) → ℕ} (hσ : LatticeProb.IsWalkStopping σ)
    {n : ℕ} (hσn : ∀ X, σ X ≤ n) (s ℓ : ℕ) :
    Measurable (fun p : (ℕ → Site d) × (ℕ → Site d) => blockStop σ s ℓ p.1 p.2) := by
  have hσm : Measurable σ := LatticeProb.measurable_isWalkStopping hσ hσn
  have h1 : Measurable (fun p : (ℕ → Site d) × (ℕ → Site d) => σ (glue s p.1 p.2)) :=
    hσm.comp (measurable_glue s)
  exact (measurable_of_countable (fun k : ℕ => min k (s + ℓ) - s)).comp h1

theorem measurable_blockReward (ζ : Site d → ℝ) {σ : (ℕ → Site d) → ℕ}
    (hσ : LatticeProb.IsWalkStopping σ) {n : ℕ} (hσn : ∀ X, σ X ≤ n) (s ℓ : ℕ) :
    Measurable (Function.uncurry (blockReward ζ σ s ℓ)) := by
  classical
  have hσm : Measurable σ := LatticeProb.measurable_isWalkStopping hσ hσn
  have hK := measurable_blockStop hσ hσn s ℓ
  have hsum : Measurable (fun p : (ℕ → Site d) × (ℕ → Site d) =>
      LatticeProb.Graph.Zd.sceneryPartialSum ζ (blockStop σ s ℓ p.1 p.2) p.2) := by
    have heq : (fun p : (ℕ → Site d) × (ℕ → Site d) =>
          LatticeProb.Graph.Zd.sceneryPartialSum ζ (blockStop σ s ℓ p.1 p.2) p.2)
        = fun p : (ℕ → Site d) × (ℕ → Site d) => ∑ i ∈ Finset.range (ℓ + 1),
            (if blockStop σ s ℓ p.1 p.2 = i then ∑ j ∈ Finset.range i, ζ (p.2 j) else 0) := by
      funext p
      rw [Finset.sum_eq_single (blockStop σ s ℓ p.1 p.2)
        (fun i _ hi => if_neg (fun h => hi h.symm))
        (fun hmem => absurd (Finset.mem_range.mpr
          (Nat.lt_succ_of_le (blockStop_le σ s ℓ p.1 p.2))) hmem)]
      rw [if_pos rfl]
      rfl
    rw [heq]
    refine Finset.measurable_sum _ fun i _ => ?_
    refine Measurable.ite (hK (measurableSet_singleton i)) ?_ measurable_const
    exact Finset.measurable_sum _ fun j _ =>
      (measurable_of_countable (fun y : Site d => ζ y)).comp
        ((measurable_pi_apply j).comp measurable_snd)
  have hset : MeasurableSet {p : (ℕ → Site d) × (ℕ → Site d) | s < σ p.1} :=
    (hσm.comp measurable_fst) (measurableSet_Ioi (a := s))
  exact Measurable.ite hset hsum measurable_const

theorem abs_blockReward_le (ζ : Site d → ℝ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ y, |ζ y| ≤ B)
    (σ : (ℕ → Site d) → ℕ) (s ℓ : ℕ) (X Y : ℕ → Site d) :
    ‖blockReward ζ σ s ℓ X Y‖ ≤ (ℓ : ℝ) * B := by
  rw [Real.norm_eq_abs, blockReward]
  by_cases hlt : s < σ X
  swap
  · rw [if_neg hlt, abs_zero]
    positivity
  rw [if_pos hlt, LatticeProb.Graph.Zd.sceneryPartialSum]
  calc |∑ j ∈ Finset.range (blockStop σ s ℓ X Y), ζ (Y j)|
      ≤ ∑ j ∈ Finset.range (blockStop σ s ℓ X Y), |ζ (Y j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range (blockStop σ s ℓ X Y), B :=
        Finset.sum_le_sum fun j _ => hB (Y j)
    _ = (blockStop σ s ℓ X Y : ℝ) * B := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (ℓ : ℝ) * B := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast blockStop_le σ s ℓ X Y) hB0

/-! ### The block bound of `eq:stopping-blocks` -/

/-- Whether the stopping time has passed `s` is settled by the positions up to `s`. -/
theorem sigma_gt_congr {σ : (ℕ → Site d) → ℕ} (hσ : LatticeProb.IsWalkStopping σ) (s : ℕ)
    {X X' : ℕ → Site d} (h : ∀ k ≤ s, X k = X' k) : (s < σ X) ↔ (s < σ X') := by
  constructor
  · intro hlt
    by_contra hcon
    have hle : σ X' ≤ s := by omega
    have : σ X = σ X' :=
      hσ (σ X') X' X (fun j hj => (h j (le_trans hj hle)).symm) rfl
    omega
  · intro hlt
    by_contra hcon
    have hle : σ X ≤ s := by omega
    have : σ X' = σ X :=
      hσ (σ X) X X' (fun j hj => h j (le_trans hj hle)) rfl
    omega

/-- **One block of `eq:stopping-blocks`.**  Conditionally on the walk up to time `s`, the
reward collected from time `s` until the stopping time, truncated at `s + ℓ`, is at most
`u_ℓ(X_s; ζ)` on the event that the stopping time has passed `s`, and zero off it.  This
is the Markov property at the deterministic time `s` together with the optimal stopping
representation applied to the shifted walk: the rule `blockStop σ s ℓ X` IS a stopping
time of the shifted walk for every fixed past `X`. -/
theorem integral_blockReward_le (hd : 1 ≤ d)
    (hStopping : Parking.External.Stopping)
    (ζ : Site d → ℝ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ y, |ζ y| ≤ B)
    {σ : (ℕ → Site d) → ℕ} (hσ : LatticeProb.IsWalkStopping σ) {n : ℕ} (hσn : ∀ X, σ X ≤ n)
    (s ℓ : ℕ) (x : Site d) :
    ∫ X, (∑ j ∈ Finset.Ico s (min (σ X) (s + ℓ)), ζ (X j)) ∂(LatticeProb.siteWalkLaw d x)
      ≤ ∫ X, (if s < σ X then u ζ ℓ (X s) else 0) ∂(LatticeProb.siteWalkLaw d x) := by
  haveI : NeZero d := ⟨by omega⟩
  have hmeas := measurable_blockReward ζ hσ hσn s ℓ
  have hbdd := abs_blockReward_le ζ hB0 hB σ s ℓ
  have hpast : ∀ X X' Y : ℕ → Site d, (∀ k ≤ s, X k = X' k) →
      blockReward ζ σ s ℓ X Y = blockReward ζ σ s ℓ X' Y := by
    intro X X' Y h
    rw [blockReward, blockReward, blockStop, blockStop, glue_congr_left X X' Y h]
    by_cases hlt : s < σ X
    · rw [if_pos hlt, if_pos ((sigma_gt_congr hσ s h).mp hlt)]
    · rw [if_neg hlt, if_neg (fun hc => hlt ((sigma_gt_congr hσ s h).mpr hc))]
  have hmk := LatticeProb.markov_fixed_general d s x (blockReward ζ σ s ℓ) hmeas hbdd hpast
  have hlhs : ∫ X, (∑ j ∈ Finset.Ico s (min (σ X) (s + ℓ)), ζ (X j))
        ∂(LatticeProb.siteWalkLaw d x)
      = ∫ X, blockReward ζ σ s ℓ X (LatticeProb.shiftPath s X)
        ∂(LatticeProb.siteWalkLaw d x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun X =>
      (blockReward_shiftPath ζ σ s ℓ X).symm)
  rw [hlhs, hmk]
  have hinner : ∀ X : ℕ → Site d,
      (∫ Y, blockReward ζ σ s ℓ X Y ∂(LatticeProb.siteWalkLaw d (X s)))
        ≤ (if s < σ X then u ζ ℓ (X s) else 0) := by
    intro X
    by_cases hlt : s < σ X
    · rw [if_pos hlt]
      have hcongr : (∫ Y, blockReward ζ σ s ℓ X Y ∂(LatticeProb.siteWalkLaw d (X s)))
          = ∫ Y, LatticeProb.Graph.Zd.sceneryPartialSum ζ (blockStop σ s ℓ X Y) Y
              ∂(LatticeProb.siteWalkLaw d (X s)) :=
        integral_congr_ae (Filter.Eventually.of_forall fun Y => by
          rw [blockReward, if_pos hlt])
      rw [hcongr]
      refine (hStopping d hd ζ ℓ (X s)).1 ?_
      exact ⟨blockStop σ s ℓ X, isWalkStopping_blockStop hσ s ℓ X,
        fun Y => blockStop_le σ s ℓ X Y, rfl⟩
    · rw [if_neg hlt]
      have hcongr : (∫ Y, blockReward ζ σ s ℓ X Y ∂(LatticeProb.siteWalkLaw d (X s)))
          = ∫ _Y : ℕ → Site d, (0:ℝ) ∂(LatticeProb.siteWalkLaw d (X s)) :=
        integral_congr_ae (Filter.Eventually.of_forall fun Y => by
          rw [blockReward, if_neg hlt])
      rw [hcongr, integral_zero]
  have hdep : LatticeProb.DependsUpTo s
      (fun X : ℕ → Site d => ∫ Y, blockReward ζ σ s ℓ X Y ∂(LatticeProb.siteWalkLaw d (X s))) := by
    intro X X' h
    show (∫ Y, blockReward ζ σ s ℓ X Y ∂(LatticeProb.siteWalkLaw d (X s)))
      = ∫ Y, blockReward ζ σ s ℓ X' Y ∂(LatticeProb.siteWalkLaw d (X' s))
    rw [h s le_rfl]
    exact integral_congr_ae (Filter.Eventually.of_forall fun Y => hpast X X' Y h)
  have hmeasInner : Measurable
      (fun X : ℕ → Site d => ∫ Y, blockReward ζ σ s ℓ X Y ∂(LatticeProb.siteWalkLaw d (X s))) :=
    LatticeProb.measurable_of_dependsUpTo hdep
  have hdepU : LatticeProb.DependsUpTo s
      (fun X : ℕ → Site d => if s < σ X then u ζ ℓ (X s) else 0) := by
    intro X X' h
    show (if s < σ X then u ζ ℓ (X s) else 0) = if s < σ X' then u ζ ℓ (X' s) else 0
    rw [h s le_rfl]
    by_cases hlt : s < σ X
    · rw [if_pos hlt, if_pos ((sigma_gt_congr hσ s h).mp hlt)]
    · rw [if_neg hlt, if_neg (fun hc => hlt ((sigma_gt_congr hσ s h).mpr hc))]
  have hmeasU : Measurable (fun X : ℕ → Site d => if s < σ X then u ζ ℓ (X s) else 0) :=
    LatticeProb.measurable_of_dependsUpTo hdepU
  have hubU : ∀ X : ℕ → Site d, ‖(if s < σ X then u ζ ℓ (X s) else 0)‖ ≤ (ℓ : ℝ) * B := by
    intro X
    by_cases hlt : s < σ X
    · rw [if_pos hlt, Real.norm_eq_abs, abs_of_nonneg (u_nonneg ζ ℓ (X s))]
      exact u_le_mul_of_le hd hB0 (fun y => le_trans (le_abs_self _) (hB y)) ℓ (X s)
    · rw [if_neg hlt, norm_zero]
      positivity
  have hubI : ∀ X : ℕ → Site d,
      ‖∫ Y, blockReward ζ σ s ℓ X Y ∂(LatticeProb.siteWalkLaw d (X s))‖ ≤ (ℓ : ℝ) * B := by
    intro X
    have h := norm_integral_le_of_norm_le_const (μ := LatticeProb.siteWalkLaw d (X s))
      (Filter.Eventually.of_forall fun Y => hbdd X Y)
    rwa [probReal_univ, mul_one] at h
  refine integral_mono ?_ ?_ hinner
  · exact (integrable_const ((ℓ : ℝ) * B)).mono' hmeasInner.aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => by simpa using hubI X)
  · exact (integrable_const ((ℓ : ℝ) * B)).mono' hmeasU.aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => by simpa using hubU X)

end Parking

end
