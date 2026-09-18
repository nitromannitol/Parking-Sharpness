/-
The geometric lower tail of the range, the last sentence of Step 1 of the proof
of `prop:resolvent` (`parking.tex:2685-2691`):

  "The ranges traced within successive blocks of `n` steps, translated to their
   starting points, are independent.  If `|R_t| < m`, each block range has fewer
   than `m` sites, so `P_0(|R_t| < m)` is at most `(1-c)^{⌊t/n⌋}`."

The independence of the blocks is the Markov property of the walk at the
deterministic times `n, 2n, …`, which is `LatticeProb.markov_fixed`; the
identification of the law of a block with the law of the walk from the origin is
the translation invariance of the event, which holds because the number of
distinct sites a path visits does not change when the path is translated.
-/
import Parking.Support.RangeTail

open MeasureTheory

noncomputable section

namespace Parking

variable {d : ℕ}

/-- Translating a path does not change the number of distinct sites it visits. -/
theorem rangeCard_translate (x : Site d) (X : ℕ → Site d) (t : ℕ) :
    LatticeProb.rangeCard (fun k => x + X k) t = LatticeProb.rangeCard X t := by
  unfold LatticeProb.rangeCard
  rw [show (fun k => x + X k) = (fun y => x + y) ∘ X from rfl, ← Finset.image_image]
  exact Finset.card_image_of_injective _ (fun y z h => by simpa using h)

/-- Shifting twice is shifting once by the sum. -/
theorem shiftPath_shiftPath (a b : ℕ) (X : ℕ → Site d) :
    LatticeProb.shiftPath a (LatticeProb.shiftPath b X)
      = LatticeProb.shiftPath (b + a) X := by
  funext k
  simp only [LatticeProb.shiftPath, ← Nat.add_assoc]

/-- Shifting by zero does nothing. -/
theorem shiftPath_zero (X : ℕ → Site d) : LatticeProb.shiftPath 0 X = X := by
  funext k
  simp only [LatticeProb.shiftPath, Nat.zero_add]

/-- The range of a block is at most the range of the whole path. -/
theorem rangeCard_shiftPath_le (X : ℕ → Site d) (a n t : ℕ) (h : a + n ≤ t) :
    LatticeProb.rangeCard (LatticeProb.shiftPath a X) n ≤ LatticeProb.rangeCard X t := by
  unfold LatticeProb.rangeCard
  refine Finset.card_le_card ?_
  intro y hy
  simp only [Finset.mem_image, Finset.mem_range, LatticeProb.shiftPath] at hy ⊢
  obtain ⟨k, hk, hky⟩ := hy
  exact ⟨a + k, by omega, hky⟩

/-- The path from `x` is the path from the origin translated by `x`. -/
theorem sitePath_eq_add (x : Site d) (xi : ℕ → Site d) (k : ℕ) :
    LatticeProb.sitePath x xi k = x + LatticeProb.sitePath 0 xi k := by
  simp only [LatticeProb.sitePath, zero_add]

/-- The range by time `t` is settled by the positions up to time `t`. -/
theorem rangeCard_congr (X Y : ℕ → Site d) (t : ℕ) (h : ∀ k ≤ t, X k = Y k) :
    LatticeProb.rangeCard X t = LatticeProb.rangeCard Y t := by
  unfold LatticeProb.rangeCard
  congr 1
  refine Finset.image_congr ?_
  intro k hk
  exact h k (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hk)


/-- The event that each of the first `K` blocks of `n` steps traces fewer than
`m` distinct sites.  `blockSmall d n m K` is the event of the paper's Step 1
after `K` blocks. -/
def blockSmall (d n m K : ℕ) : Set (ℕ → Site d) :=
  {X | ∀ i < K, LatticeProb.rangeCard (LatticeProb.shiftPath (i * n) X) n < m}


/-- The event that the range by time `n` is smaller than `m` is measurable. -/
theorem measurableSet_rangeCard_lt (n m : ℕ) :
    MeasurableSet {X : ℕ → Site d | LatticeProb.rangeCard X n < m} :=
  (LatticeProb.measurable_rangeCard (d := d) n)
    (MeasurableSet.of_discrete (s := {k : ℕ | k < m}))

/-- The event of the first `K` blocks is measurable. -/
theorem measurableSet_blockSmall (n m K : ℕ) :
    MeasurableSet (blockSmall d n m K) := by
  have hrw : blockSmall d n m K
      = ⋂ i : ℕ, ⋂ _ : i < K,
        (LatticeProb.shiftPath (i * n)) ⁻¹'
          {X : ℕ → Site d | LatticeProb.rangeCard X n < m} := by
    ext X
    simp only [blockSmall, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [hrw]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    (LatticeProb.measurable_shiftPath (i * n)) (measurableSet_rangeCard_lt n m)

/-- One block peeled off the front: the first `K + 1` blocks are small exactly
when the first block is small and the first `K` blocks of the shifted path are.
This is where the Markov property will be applied. -/
theorem blockSmall_succ (n m K : ℕ) :
    blockSmall d n m (K + 1)
      = {X : ℕ → Site d | LatticeProb.rangeCard X n < m}
          ∩ (LatticeProb.shiftPath n) ⁻¹' (blockSmall d n m K) := by
  ext X
  simp only [blockSmall, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · intro h
    refine ⟨by simpa [shiftPath_zero] using h 0 (Nat.succ_pos K), fun i hi => ?_⟩
    rw [shiftPath_shiftPath (i * n) n X]
    have he : n + i * n = (i + 1) * n := by ring
    rw [he]
    exact h (i + 1) (by omega)
  · rintro ⟨h0, hrest⟩ i hi
    match i with
    | 0 => simpa [shiftPath_zero] using h0
    | (j + 1) =>
        have hj := hrest j (by omega)
        rw [shiftPath_shiftPath (j * n) n X] at hj
        have he : n + j * n = (j + 1) * n := by ring
        rw [he] at hj
        exact hj

/-- **Translation invariance.**  A functional of the path that does not change
when the path is translated has the same expectation from every site. -/
theorem integral_siteWalkLaw_translate [NeZero d] (F : (ℕ → Site d) → ℝ)
    (hFm : Measurable F)
    (hFtr : ∀ (y : Site d) (X : ℕ → Site d), F (fun k => y + X k) = F X) (x : Site d) :
    ∫ X, F X ∂(LatticeProb.siteWalkLaw d x) = ∫ X, F X ∂(LatticeProb.siteWalkLaw d 0) := by
  rw [LatticeProb.siteWalkLaw_eq d x, LatticeProb.siteWalkLaw_eq d 0,
    integral_map (LatticeProb.measurable_sitePath x).aemeasurable hFm.aestronglyMeasurable,
    integral_map (LatticeProb.measurable_sitePath (0 : Site d)).aemeasurable
      hFm.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun xi => ?_)
  show F (LatticeProb.sitePath x xi) = F (LatticeProb.sitePath 0 xi)
  have hpath : LatticeProb.sitePath x xi = fun k => x + LatticeProb.sitePath 0 xi k :=
    funext fun k => sitePath_eq_add x xi k
  rw [hpath, hFtr x (LatticeProb.sitePath 0 xi)]


/-- Shifting commutes with translating. -/
theorem shiftPath_translate (a : ℕ) (y : Site d) (X : ℕ → Site d) :
    LatticeProb.shiftPath a (fun k => y + X k)
      = fun k => y + LatticeProb.shiftPath a X k := by
  funext k
  simp only [LatticeProb.shiftPath]

/-- A translation-invariant event has the same probability from every site. -/
theorem measureReal_siteWalkLaw_translate [NeZero d] (S : Set (ℕ → Site d))
    (hS : MeasurableSet S)
    (hStr : ∀ (y : Site d) (X : ℕ → Site d), (fun k => y + X k) ∈ S ↔ X ∈ S) (x : Site d) :
    (LatticeProb.siteWalkLaw d x).real S = (LatticeProb.siteWalkLaw d 0).real S := by
  rw [← integral_indicator_one (μ := LatticeProb.siteWalkLaw d x) hS,
    ← integral_indicator_one (μ := LatticeProb.siteWalkLaw d 0) hS]
  refine integral_siteWalkLaw_translate (fun X => S.indicator 1 X) ?_ ?_ x
  · exact (measurable_const : Measurable fun _ : ℕ → Site d => (1 : ℝ)).indicator hS
  · intro y X
    by_cases hX : X ∈ S
    · rw [Set.indicator_of_mem ((hStr y X).mpr hX), Set.indicator_of_mem hX]
      simp
    · rw [Set.indicator_of_notMem (fun hc => hX ((hStr y X).mp hc)),
        Set.indicator_of_notMem hX]

/-- The block event is translation invariant. -/
theorem mem_blockSmall_translate (n m K : ℕ) (y : Site d) (X : ℕ → Site d) :
    (fun k => y + X k) ∈ blockSmall d n m K ↔ X ∈ blockSmall d n m K := by
  simp only [blockSmall, Set.mem_setOf_eq, shiftPath_translate, rangeCard_translate]

/-- The event that the range by time `n` is small is translation invariant. -/
theorem mem_rangeCard_lt_translate (n m : ℕ) (y : Site d) (X : ℕ → Site d) :
    (fun k => y + X k) ∈ {X : ℕ → Site d | LatticeProb.rangeCard X n < m}
      ↔ X ∈ {X : ℕ → Site d | LatticeProb.rangeCard X n < m} := by
  simp only [Set.mem_setOf_eq, rangeCard_translate]


/-- **The blocks are independent.**  The first `K` blocks of `n` steps are all
small with probability exactly the `K`-th power of the probability that one
block is small.  This is the independence of the successive block ranges of
Step 1 of `prop:resolvent`, proved from the Markov property of the walk at the
deterministic times `n, 2n, …` and the translation invariance of the event. -/
theorem measureReal_blockSmall [NeZero d] (n m : ℕ) :
    ∀ (K : ℕ) (x : Site d),
      (LatticeProb.siteWalkLaw d x).real (blockSmall d n m K)
        = ((LatticeProb.siteWalkLaw d 0).real
            {X : ℕ → Site d | LatticeProb.rangeCard X n < m}) ^ K := by
  intro K
  induction K with
  | zero =>
      intro x
      have h0 : blockSmall d n m 0 = (Set.univ : Set (ℕ → Site d)) := by
        ext X; simp [blockSmall]
      rw [h0, pow_zero, probReal_univ]
  | succ K ih =>
      intro x
      rw [blockSmall_succ]
      set A : Set (ℕ → Site d) := {X : ℕ → Site d | LatticeProb.rangeCard X n < m} with hA
      set B : Set (ℕ → Site d) := blockSmall d n m K with hB
      set p : ℝ := (LatticeProb.siteWalkLaw d 0).real A with hp
      have hAm : MeasurableSet A := measurableSet_rangeCard_lt n m
      have hBm : MeasurableSet B := measurableSet_blockSmall n m K
      set F : (ℕ → Site d) → ℝ := fun X => A.indicator 1 X with hF
      set G : (ℕ → Site d) → ℝ := fun X => B.indicator 1 X with hG
      have hGm : Measurable G :=
        (measurable_const : Measurable (1 : (ℕ → Site d) → ℝ)).indicator hBm
      have hGb : ∀ X, ‖G X‖ ≤ 1 := by
        intro X
        by_cases hX : X ∈ B
        · simp [hG, Set.indicator_of_mem hX]
        · simp [hG, Set.indicator_of_notMem hX]
      have hFb : ∀ X, ‖F X‖ ≤ 1 := by
        intro X
        by_cases hX : X ∈ A
        · simp [hF, Set.indicator_of_mem hX]
        · simp [hF, Set.indicator_of_notMem hX]
      have hFdep : LatticeProb.DependsUpTo n F := by
        intro X Y hXY
        have hr : LatticeProb.rangeCard X n = LatticeProb.rangeCard Y n :=
          rangeCard_congr X Y n hXY
        have hiff : X ∈ A ↔ Y ∈ A := by
          simp only [hA, Set.mem_setOf_eq, hr]
        by_cases hX : X ∈ A
        · simp [hF, Set.indicator_of_mem hX, Set.indicator_of_mem (hiff.mp hX)]
        · simp [hF, Set.indicator_of_notMem hX,
            Set.indicator_of_notMem (fun hc => hX (hiff.mpr hc))]
      have hmk := LatticeProb.markov_fixed d n x G hGm (CF := 1) hGb F (CH := 1) hFb hFdep
      have hPE : ∀ y : Site d, LatticeProb.pathExpect d G y = p ^ K := by
        intro y
        rw [LatticeProb.pathExpect,
          integral_indicator_one (μ := LatticeProb.siteWalkLaw d y) hBm]
        exact ih y
      have hLHS : ∫ X, G (LatticeProb.shiftPath n X) * F X ∂(LatticeProb.siteWalkLaw d x)
          = (LatticeProb.siteWalkLaw d x).real (A ∩ (LatticeProb.shiftPath n) ⁻¹' B) := by
        rw [← integral_indicator_one (μ := LatticeProb.siteWalkLaw d x)
          (hAm.inter ((LatticeProb.measurable_shiftPath n) hBm))]
        refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
        by_cases h1 : X ∈ A <;> by_cases h2 : LatticeProb.shiftPath n X ∈ B <;>
          simp [hF, hG, Set.indicator_apply, h1, h2, Set.mem_inter_iff, Set.mem_preimage]
      have hRHS : ∫ X, LatticeProb.pathExpect d G (X n) * F X ∂(LatticeProb.siteWalkLaw d x)
          = p ^ K * (LatticeProb.siteWalkLaw d x).real A := by
        simp only [hPE]
        rw [integral_const_mul, integral_indicator_one (μ := LatticeProb.siteWalkLaw d x) hAm]
      rw [← hLHS, hmk, hRHS,
        measureReal_siteWalkLaw_translate A hAm (mem_rangeCard_lt_translate n m) x]
      ring


/-- A path of small range has every fitting block of small range. -/
theorem subset_blockSmall (n m t : ℕ) :
    {X : ℕ → Site d | LatticeProb.rangeCard X t < m} ⊆ blockSmall d n m (t / n) := by
  intro X hX i hi
  simp only [Set.mem_setOf_eq] at hX
  have hfit : i * n + n ≤ t := by
    have h1 : (i + 1) * n ≤ (t / n) * n := Nat.mul_le_mul_right n hi
    have h2 : (t / n) * n ≤ t := Nat.div_mul_le_self t n
    have h3 : (i + 1) * n = i * n + n := by ring
    omega
  exact lt_of_le_of_lt (rangeCard_shiftPath_le X (i * n) n t hfit) hX

/-- **The geometric lower tail of the range.**  This is the conclusion of Step 1
of `prop:resolvent` (`parking.tex:2685-2691`), before the horizon is chosen. -/
theorem measureReal_rangeCard_lt_le_pow [NeZero d] (n m t : ℕ) (x : Site d) :
    (LatticeProb.siteWalkLaw d x).real {X : ℕ → Site d | LatticeProb.rangeCard X t < m}
      ≤ ((LatticeProb.siteWalkLaw d 0).real
          {X : ℕ → Site d | LatticeProb.rangeCard X n < m}) ^ (t / n) := by
  rw [← measureReal_blockSmall n m (t / n) x]
  exact measureReal_mono (subset_blockSmall n m t) (measure_ne_top _ _)

/-- **One block is small with probability at most `7/8`**, as soon as `m` is at
most half the expected range at the horizon `n`.  This is the Paley-Zygmund
half of Step 1. -/
theorem measureReal_rangeCard_lt_le_seven_eighths (hd : 1 ≤ d) (n m : ℕ)
    (hm : (m : ℝ)
      ≤ (1 / 2) * ∫ X, (LatticeProb.rangeCard X n : ℝ) ∂(LatticeProb.siteWalkLaw d 0)) :
    (LatticeProb.siteWalkLaw d 0).real {X : ℕ → Site d | LatticeProb.rangeCard X n < m}
      ≤ 7 / 8 := by
  haveI : NeZero d := ⟨by omega⟩
  set E : Set (ℕ → Site d) := {X : ℕ → Site d | (1 / 2 : ℝ)
      * (∫ Y, (LatticeProb.rangeCard Y n : ℝ) ∂(LatticeProb.siteWalkLaw d 0))
    < (LatticeProb.rangeCard X n : ℝ)} with hE
  have hEm : MeasurableSet E := by
    have hpre : E = (fun X : ℕ → Site d => LatticeProb.rangeCard X n) ⁻¹'
        {k : ℕ | (1 / 2 : ℝ)
          * (∫ Y, (LatticeProb.rangeCard Y n : ℝ) ∂(LatticeProb.siteWalkLaw d 0))
            < (k : ℝ)} := rfl
    rw [hpre]
    exact (LatticeProb.measurable_rangeCard n) MeasurableSet.of_discrete
  have hpz := rangeCard_half_mean_prob hd (0 : Site d) n
  have hsub : {X : ℕ → Site d | LatticeProb.rangeCard X n < m} ⊆ Eᶜ := by
    intro X hX
    simp only [hE, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    have h1 : ((LatticeProb.rangeCard X n : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast hX
    linarith [hm]
  have hsum := measureReal_add_measureReal_compl (μ := LatticeProb.siteWalkLaw d 0) hEm
  rw [probReal_univ] at hsum
  have hmono := measureReal_mono (μ := LatticeProb.siteWalkLaw d 0) hsub (measure_ne_top _ _)
  linarith


/-- Half the expected range at the horizon `n`, rounded down: the largest `m`
for which the Paley-Zygmund bound of Step 1 applies at that horizon. -/
def blockThreshold (d n : ℕ) : ℕ :=
  ⌊(1 / 2 : ℝ) * ∫ X, (LatticeProb.rangeCard X n : ℝ) ∂(LatticeProb.siteWalkLaw d 0)⌋₊


/-- **Step 1 of `prop:resolvent`.**  At the threshold `blockThreshold d n` the
range by time `t` is small with probability at most `(7/8)^{⌊t/n⌋}`. -/
theorem rangeTail_le (hd : 1 ≤ d) (n t : ℕ) (x : Site d) :
    (LatticeProb.siteWalkLaw d x).real
        {X : ℕ → Site d | LatticeProb.rangeCard X t < blockThreshold d n}
      ≤ (7 / 8 : ℝ) ^ (t / n) := by
  haveI : NeZero d := ⟨by omega⟩
  have hmean : (0 : ℝ)
      ≤ ∫ X, (LatticeProb.rangeCard X n : ℝ) ∂(LatticeProb.siteWalkLaw d 0) :=
    integral_nonneg fun X => by positivity
  have hfl : ((blockThreshold d n : ℕ) : ℝ)
      ≤ (1 / 2) * ∫ X, (LatticeProb.rangeCard X n : ℝ) ∂(LatticeProb.siteWalkLaw d 0) :=
    Nat.floor_le (by linarith)
  refine (measureReal_rangeCard_lt_le_pow (d := d) n (blockThreshold d n) t x).trans ?_
  exact pow_le_pow_left₀ measureReal_nonneg
    (measureReal_rangeCard_lt_le_seven_eighths hd n (blockThreshold d n) hfl) (t / n)

/-- The threshold is at least a constant multiple of `(n+1)/φ_d(n)`, up to one:
this is the first display of Step 1 of `prop:resolvent` in the form the
optimization uses. -/
theorem blockThreshold_lower (hd : 1 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      c * (((n : ℝ) + 1) / greenScale d n) - 1 ≤ (blockThreshold d n : ℝ) := by
  obtain ⟨c₀, hc₀, hlow⟩ := exists_meanRange_lower (d := d) hd
  refine ⟨c₀ / 2, by positivity, fun n => ?_⟩
  have h1 := hlow (0 : Site d) n
  have h2 := Nat.sub_one_lt_floor
    ((1 / 2 : ℝ) * ∫ X, (LatticeProb.rangeCard X n : ℝ) ∂(LatticeProb.siteWalkLaw d 0))
  simp only [blockThreshold]
  linarith

end Parking

end
