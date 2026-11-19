import Parking.Support.RangeOrthant
import Parking.Support.RangeResolvent

/-!
# Box confinement for the simple walk

The probability of remaining in an outer box and returning to its inner box
provides the block estimate used for confinement of the walk range.
-/

open MeasureTheory

noncomputable section

namespace Parking

variable {d : ℕ}

/-- A position path stays in a box of radius `2 * R` and ends in the box of
radius `R`. -/
def boxBlock (n : ℕ) (R : ℝ) : Set (ℕ → Site d) :=
  {X | (∀ k ≤ n, ∀ i, |(X k i : ℝ)| ≤ 2 * R) ∧ ∀ i, |(X n i : ℝ)| ≤ R}

/-- Box confinement and the endpoint condition are measurable. -/
theorem measurableSet_boxBlock (n : ℕ) (R : ℝ) : MeasurableSet (boxBlock (d := d) n R) := by
  have hm (k : ℕ) (i : Fin d) : Measurable fun X : ℕ → Site d => |(X k i : ℝ)| :=
    (measurable_of_countable (fun x : Site d => |(x i : ℝ)|)).comp (measurable_pi_apply k)
  have heq : boxBlock (d := d) n R =
      (⋂ k : ℕ, ⋂ _ : k ≤ n, ⋂ i : Fin d, {X | |(X k i : ℝ)| ≤ 2 * R}) ∩
        (⋂ i : Fin d, {X | |(X n i : ℝ)| ≤ R}) := by
    ext X
    simp [boxBlock]
  rw [heq]
  exact (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun i => measurableSet_le (hm k i) measurable_const).inter
      (MeasurableSet.iInter fun i => measurableSet_le (hm n i) measurable_const)

/-- The signed-direction formulation and the position-path formulation of a
box block have the same probability. -/
theorem measureReal_boxBlock_eq (hd : 1 ≤ d) (x : Site d) (n : ℕ) (R : ℝ) :
    (LatticeProb.siteWalkLaw d x).real (boxBlock n R) =
      (walkLaw d).real (walkBoxBlock x n R) := by
  have : NeZero d := ⟨by omega⟩
  have hpath : Measurable (walkPath x) :=
    Measurable.of_eval fun k => measurable_walkPath x k
  rw [← map_walkLaw_walkPath hd x, measureReal_def,
    Measure.map_apply hpath (measurableSet_boxBlock n R), ← measureReal_def]
  rfl

/-- The inner-to-inner box block has probability at least `2⁻ᵈ⁻¹`. -/
theorem half_le_pow_mul_measureReal_boxBlock (hd : 1 ≤ d) (n : ℕ) (x : Site d)
    {r R : ℝ} (hr : 0 < r) (hn : (n : ℝ) ≤ r ^ 2 / 2)
    (hR : (d : ℝ) * r ≤ R) (hx : ∀ i, |(x i : ℝ)| ≤ R) :
    (1 : ℝ) / 2 ≤ (2 : ℝ) ^ d * (LatticeProb.siteWalkLaw d x).real (boxBlock n R) := by
  rw [measureReal_boxBlock_eq hd x n R]
  exact half_le_pow_mul_walkBoxBlock hd n x hr hn hR hx

/-- The indicator of a box block depends only on positions up to its horizon. -/
theorem boxBlock_indicator_dependsUpTo (n : ℕ) (R : ℝ) :
    LatticeProb.DependsUpTo n ((boxBlock n R).indicator (1 : (ℕ → Site d) → ℝ)) := by
  intro X Y hXY
  have hiff : X ∈ boxBlock n R ↔ Y ∈ boxBlock n R := by
    simp only [boxBlock, Set.mem_ofPred_eq]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor
    · intro k hk i
      rw [← hXY k hk]
      exact h₁ k hk i
    · intro i
      rw [← hXY n le_rfl]
      exact h₂ i
    · intro k hk i
      rw [hXY k hk]
      exact h₁ k hk i
    · intro i
      rw [hXY n le_rfl]
      exact h₂ i
  by_cases hX : X ∈ boxBlock n R
  · simp [Set.indicator_of_mem hX, Set.indicator_of_mem (hiff.mp hX)]
  · simp [Set.indicator_of_notMem hX, Set.indicator_of_notMem (fun h => hX (hiff.mpr h))]

/-- The Markov property multiplies a box-block probability by a uniform lower
bound for a following block from the inner box. -/
theorem mul_measureReal_boxBlock_le_inter (hd : 1 ≤ d) (n m : ℕ) (R c : ℝ)
    (x : Site d)
    (hnext : ∀ y : Site d, (∀ i, |(y i : ℝ)| ≤ R) →
      c ≤ (LatticeProb.siteWalkLaw d y).real (boxBlock m R)) :
    c * (LatticeProb.siteWalkLaw d x).real (boxBlock n R) ≤
      (LatticeProb.siteWalkLaw d x).real
        (boxBlock n R ∩ (LatticeProb.shiftPath n) ⁻¹' boxBlock m R) := by
  have : NeZero d := ⟨by omega⟩
  let A : Set (ℕ → Site d) := boxBlock n R
  let B : Set (ℕ → Site d) := boxBlock m R
  let F : (ℕ → Site d) → ℝ := B.indicator 1
  let H : (ℕ → Site d) → ℝ := A.indicator 1
  have hAm : MeasurableSet A := measurableSet_boxBlock n R
  have hBm : MeasurableSet B := measurableSet_boxBlock m R
  have hFm : Measurable F := (measurable_const : Measurable (1 : (ℕ → Site d) → ℝ)).indicator hBm
  have hFb : ∀ X, ‖F X‖ ≤ 1 := by
    intro X
    by_cases hX : X ∈ B <;> simp [F, hX]
  have hHb : ∀ X, ‖H X‖ ≤ 1 := by
    intro X
    by_cases hX : X ∈ A <;> simp [H, hX]
  have hmk := LatticeProb.markov_fixed d n x F hFm (CF := 1) hFb H (CH := 1)
    hHb (boxBlock_indicator_dependsUpTo n R)
  have hPE (y : Site d) : LatticeProb.pathExpect d F y =
      (LatticeProb.siteWalkLaw d y).real B := by
    exact integral_indicator_one hBm
  have hleft : ∫ X, F (LatticeProb.shiftPath n X) * H X ∂(LatticeProb.siteWalkLaw d x) =
      (LatticeProb.siteWalkLaw d x).real (A ∩ (LatticeProb.shiftPath n) ⁻¹' B) := by
    rw [← integral_indicator_one (hAm.inter ((LatticeProb.measurable_shiftPath n) hBm))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    by_cases h₁ : X ∈ A <;> by_cases h₂ : LatticeProb.shiftPath n X ∈ B <;>
      simp [F, H, h₁, h₂, Set.mem_inter_iff, Set.mem_preimage]
  have hGm : Measurable fun X : ℕ → Site d => LatticeProb.pathExpect d F (X n) * H X :=
    ((LatticeProb.measurable_pathExpect d F).comp (measurable_pi_apply n)).mul
      ((measurable_const : Measurable (1 : (ℕ → Site d) → ℝ)).indicator hAm)
  have hGi : Integrable (fun X : ℕ → Site d => LatticeProb.pathExpect d F (X n) * H X)
      (LatticeProb.siteWalkLaw d x) := by
    refine Integrable.of_bound hGm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun X => ?_)
    rw [hPE]
    by_cases hX : X ∈ A
    · simp only [H, Set.indicator_of_mem hX, Pi.one_apply, mul_one, Real.norm_eq_abs,
        abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
    · simp [H, Set.indicator_of_notMem hX]
  have hHi : Integrable (fun X : ℕ → Site d => c * H X) (LatticeProb.siteWalkLaw d x) :=
    ((integrable_const (1 : ℝ)).indicator hAm).const_mul c
  have hmono : (∫ X, c * H X ∂(LatticeProb.siteWalkLaw d x)) ≤
      ∫ X, LatticeProb.pathExpect d F (X n) * H X ∂(LatticeProb.siteWalkLaw d x) := by
    refine integral_mono hHi hGi fun X => ?_
    by_cases hX : X ∈ A
    · have hinner : ∀ i, |(X n i : ℝ)| ≤ R := hX.2
      simpa [H, Set.indicator_of_mem hX, hPE] using hnext (X n) hinner
    · simp [H, Set.indicator_of_notMem hX]
  rw [integral_const_mul, integral_indicator_one hAm] at hmono
  rw [← hmk, hleft] at hmono
  exact hmono

/-- Two successive box blocks form a box block over their combined horizon. -/
theorem boxBlock_inter_shift_subset (n m : ℕ) (R : ℝ) :
    boxBlock (d := d) n R ∩ (LatticeProb.shiftPath n) ⁻¹' boxBlock m R ⊆
      boxBlock (n + m) R := by
  intro X hX
  rcases hX with ⟨⟨hfirst, _⟩, hsecond, hend⟩
  change (∀ k ≤ n + m, ∀ i, |(X k i : ℝ)| ≤ 2 * R) ∧
    ∀ i, |(X (n + m) i : ℝ)| ≤ R
  constructor
  · intro k hk i
    by_cases hkn : k ≤ n
    · exact hfirst k hkn i
    · have hsub : k - n ≤ m := by omega
      have h := hsecond (k - n) hsub i
      simpa only [LatticeProb.shiftPath, Nat.add_sub_of_le (le_of_not_ge hkn)] using h
  · intro i
    exact hend i

/-- A uniform inner-to-inner block probability iterates over successive blocks. -/
theorem pow_le_measureReal_boxBlock_mul (hd : 1 ≤ d) (n : ℕ) (R c : ℝ)
    (hR : 0 ≤ R) (hc : 0 ≤ c)
    (hblock : ∀ y : Site d, (∀ i, |(y i : ℝ)| ≤ R) →
      c ≤ (LatticeProb.siteWalkLaw d y).real (boxBlock n R)) :
    ∀ (j : ℕ) (x : Site d), (∀ i, |(x i : ℝ)| ≤ R) →
      c ^ j ≤ (LatticeProb.siteWalkLaw d x).real (boxBlock (j * n) R) := by
  have : NeZero d := ⟨by omega⟩
  have := stepLaw_isProbability hd
  have : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  intro j
  induction j with
  | zero =>
      intro x hx
      rw [Nat.zero_mul, measureReal_boxBlock_eq hd x 0 R, pow_zero]
      have hsmall : ∀ i, |(x i : ℝ)| ≤ 2 * R := fun i => (hx i).trans (by linarith)
      have huniv : walkBoxBlock x 0 R = Set.univ := by
        ext p
        simp [walkBoxBlock, walkPath, hx, hsmall]
      rw [huniv, probReal_univ]
  | succ j ih =>
      intro x hx
      have hj := mul_measureReal_boxBlock_le_inter hd n (j * n) R (c ^ j) x
        (fun y hy => ih y hy)
      have hmono : (LatticeProb.siteWalkLaw d x).real
          (boxBlock n R ∩ (LatticeProb.shiftPath n) ⁻¹' boxBlock (j * n) R) ≤
          (LatticeProb.siteWalkLaw d x).real (boxBlock (n + j * n) R) :=
        measureReal_mono (boxBlock_inter_shift_subset n (j * n) R) (measure_ne_top _ _)
      have hfirst := hblock x hx
      calc c ^ (j + 1) = c ^ j * c := by ring
        _ ≤ c ^ j * (LatticeProb.siteWalkLaw d x).real (boxBlock n R) :=
          mul_le_mul_of_nonneg_left hfirst (pow_nonneg hc _)
        _ ≤ (LatticeProb.siteWalkLaw d x).real (boxBlock (n + j * n) R) := hj.trans hmono
        _ = (LatticeProb.siteWalkLaw d x).real (boxBlock ((j + 1) * n) R) := by
          congr 2
          ring

end Parking

end
