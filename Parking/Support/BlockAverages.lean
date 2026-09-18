/-
The block averages of Step 2 of `lem:mean-horizon`, read in the configuration.

`blockAvg` is the `k`-th term of `eq:stopping-blocks` averaged over the walk,
and `rewardAvg` is the reward of the lemma's left side averaged over the walk;
both are functions of the configuration alone, and Step 2 integrates them over
it.  This file supplies the two facts that integration needs: they are
measurable (the joint measurability of
`Parking/Support/JointStopping.lean` plus the measurability of a parametrized
integral), and they are dominated by a multiple of the field summed over a box,
which is integrable because the one-site law has a first moment.

The domination is the a priori bound of `eq:apriori-finite` read along the walk:
almost surely the walk has stayed within `n` of the origin by time `n`, so the
odometer at a block's start reads only the box of radius `n + max N (2n)`.
-/
import Parking.Support.BlockMoments

noncomputable section

namespace Parking

open MeasureTheory LatticeProb
open scoped ENNReal

variable {d : ℕ}

/-- The block term averaged over the walk, as a function of the configuration. -/
def blockAvg (δ : ℝ) (σ : (Site d → ℤ) → (ℕ → Site d) → ℕ) (N k : ℕ)
    (η : Site d → ℤ) : ℝ :=
  ∫ X, (if blockBound N k < σ η X then
      u (Parking.xi δ η) (blockBound N (k + 1) - blockBound N k) (X (blockBound N k))
    else 0) ∂(LatticeProb.siteWalkLaw d (0 : Site d))

/-- The reward averaged over the walk, as a function of the configuration. -/
def rewardAvg (δ : ℝ) (σ : (Site d → ℤ) → (ℕ → Site d) → ℕ) (η : Site d → ℤ) : ℝ :=
  ∫ X, (∑ j ∈ Finset.range (σ η X), Parking.xi δ η (X j))
    ∂(LatticeProb.siteWalkLaw d (0 : Site d))

theorem blockAvg_nonneg (δ : ℝ) (σ : (Site d → ℤ) → (ℕ → Site d) → ℕ) (N k : ℕ)
    (η : Site d → ℤ) : 0 ≤ blockAvg δ σ N k η := by
  refine integral_nonneg fun X => ?_
  show (0:ℝ) ≤ if blockBound N k < σ η X then _ else 0
  by_cases h : blockBound N k < σ η X
  · rw [if_pos h]; exact u_nonneg _ _ _
  · rw [if_neg h]

theorem stronglyMeasurable_blockAvg (hd : 1 ≤ d) (δ : ℝ)
    {σ : (Site d → ℤ) → (ℕ → Site d) → ℕ} (hσ : ∀ η, LatticeProb.IsWalkStopping (σ η))
    {n : ℕ} (hσn : ∀ η X, σ η X ≤ n) (hm : ∀ X, Measurable fun η => σ η X) (N k : ℕ) :
    StronglyMeasurable (blockAvg δ σ N k) := by
  haveI : NeZero d := ⟨by omega⟩
  exact StronglyMeasurable.integral_prod_right'
    (measurable_blockTerm hσ hσn hm δ (blockBound N k)
      (blockBound N (k + 1) - blockBound N k)).stronglyMeasurable

theorem stronglyMeasurable_rewardAvg (hd : 1 ≤ d) (δ : ℝ)
    {σ : (Site d → ℤ) → (ℕ → Site d) → ℕ} (hσ : ∀ η, LatticeProb.IsWalkStopping (σ η))
    {n : ℕ} (hσn : ∀ η X, σ η X ≤ n) (hm : ∀ X, Measurable fun η => σ η X) :
    StronglyMeasurable (rewardAvg δ σ) := by
  haveI : NeZero d := ⟨by omega⟩
  exact StronglyMeasurable.integral_prod_right'
    (measurable_rewardSum hσ hσn hm δ).stronglyMeasurable

/-! ### The a priori bounds in the configuration -/

theorem blockAvg_le (hd : 1 ≤ d) (δ : ℝ) {σ : (Site d → ℤ) → (ℕ → Site d) → ℕ}
    {n : ℕ} (hσn : ∀ η X, σ η X ≤ n) (N k : ℕ) (η : Site d → ℤ) :
    blockAvg δ σ N k η
      ≤ ((max N (2 * n) : ℕ) : ℝ)
          * ∑ z ∈ boxFinset (0 : Site d) (n + max N (2 * n)), |Parking.xi δ η z| := by
  haveI : NeZero d := ⟨by omega⟩
  have hbound := ae_mem_boxFinset hd n (0 : Site d)
  have hle : blockAvg δ σ N k η
      ≤ ∫ _X : ℕ → Site d, (((max N (2 * n) : ℕ) : ℝ)
          * ∑ z ∈ boxFinset (0 : Site d) (n + max N (2 * n)), |Parking.xi δ η z|)
        ∂(LatticeProb.siteWalkLaw d (0 : Site d)) := by
    refine integral_mono_of_nonneg ?_ (integrable_const _) ?_
    · filter_upwards with X
      show (0:ℝ) ≤ if blockBound N k < σ η X then _ else 0
      by_cases h : blockBound N k < σ η X
      · rw [if_pos h]; exact u_nonneg _ _ _
      · rw [if_neg h]
    · filter_upwards [hbound] with X hX
      exact blockTerm_bound hd δ η (hσn η) k hX
  refine hle.trans (le_of_eq ?_)
  rw [integral_const, probReal_univ, one_smul]

theorem abs_rewardAvg_le (hd : 1 ≤ d) (δ : ℝ) {σ : (Site d → ℤ) → (ℕ → Site d) → ℕ}
    {n : ℕ} (hσn : ∀ η X, σ η X ≤ n) (η : Site d → ℤ) :
    |rewardAvg δ σ η| ≤ (n : ℝ) * ∑ z ∈ boxFinset (0 : Site d) n, |Parking.xi δ η z| := by
  haveI : NeZero d := ⟨by omega⟩
  set G : ℝ := ∑ z ∈ boxFinset (0 : Site d) n, |Parking.xi δ η z| with hG
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hbound := ae_mem_boxFinset hd n (0 : Site d)
  have hstep : ∫ X, ‖∑ j ∈ Finset.range (σ η X), Parking.xi δ η (X j)‖
        ∂(LatticeProb.siteWalkLaw d (0 : Site d))
      ≤ ∫ _X : ℕ → Site d, ((n : ℝ) * G) ∂(LatticeProb.siteWalkLaw d (0 : Site d)) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun X => norm_nonneg _)
      (integrable_const _) ?_
    filter_upwards [hbound] with X hX
    rw [Real.norm_eq_abs]
    calc |∑ j ∈ Finset.range (σ η X), Parking.xi δ η (X j)|
        ≤ ∑ j ∈ Finset.range (σ η X), |Parking.xi δ η (X j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range n, |Parking.xi δ η (X j)| :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun j hj => Finset.mem_range.mpr
              (lt_of_lt_of_le (Finset.mem_range.mp hj) (hσn η X)))
            (fun j _ _ => abs_nonneg _)
      _ ≤ ∑ _j ∈ Finset.range n, G := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hjn : j ≤ n := le_of_lt (Finset.mem_range.mp hj)
          exact Finset.single_le_sum (f := fun z => |Parking.xi δ η z|)
            (fun z _ => abs_nonneg _) (hX j hjn)
      _ = (n : ℝ) * G := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hnorm : |rewardAvg δ σ η|
      ≤ ∫ X, ‖∑ j ∈ Finset.range (σ η X), Parking.xi δ η (X j)‖
        ∂(LatticeProb.siteWalkLaw d (0 : Site d)) := by
    rw [rewardAvg, ← Real.norm_eq_abs]
    exact norm_integral_le_integral_norm _
  refine hnorm.trans (hstep.trans (le_of_eq ?_))
  rw [integral_const, probReal_univ, one_smul]

/-! ### Integrability in the configuration -/

theorem integrable_blockAvg (hd : 1 ≤ d) {δ θ : ℝ} (hθ : 0 < θ)
    (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν)
    {σ : (Site d → ℤ) → (ℕ → Site d) → ℕ} (hσ : ∀ η, LatticeProb.IsWalkStopping (σ η))
    {n : ℕ} (hσn : ∀ η X, σ η X ≤ n) (hm : ∀ X, Measurable fun η => σ η X) (N k : ℕ) :
    Integrable (blockAvg δ σ N k) (LatticeProb.iidLaw d ν) := by
  have hint : Integrable (fun k : ℤ => ((k : ℝ))) ν := integrable_intCast_of_exp hθ ν hexp
  refine Integrable.mono'
    ((integrable_boxSum_xi δ ν hint (n + max N (2 * n))).const_mul
      ((max N (2 * n) : ℕ) : ℝ))
    (stronglyMeasurable_blockAvg hd δ hσ hσn hm N k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun η => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (blockAvg_nonneg δ σ N k η)]
  exact blockAvg_le hd δ hσn N k η

theorem integrable_rewardAvg (hd : 1 ≤ d) {δ θ : ℝ} (hθ : 0 < θ)
    (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν)
    {σ : (Site d → ℤ) → (ℕ → Site d) → ℕ} (hσ : ∀ η, LatticeProb.IsWalkStopping (σ η))
    {n : ℕ} (hσn : ∀ η X, σ η X ≤ n) (hm : ∀ X, Measurable fun η => σ η X) :
    Integrable (rewardAvg δ σ) (LatticeProb.iidLaw d ν) := by
  have hint : Integrable (fun k : ℤ => ((k : ℝ))) ν := integrable_intCast_of_exp hθ ν hexp
  refine Integrable.mono'
    ((integrable_boxSum_xi δ ν hint n).const_mul ((n : ℕ) : ℝ))
    (stronglyMeasurable_rewardAvg hd δ hσ hσn hm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun η => ?_)
  rw [Real.norm_eq_abs]
  exact abs_rewardAvg_le hd δ hσn η

end Parking

end
