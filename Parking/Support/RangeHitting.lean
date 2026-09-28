import Parking.Support.RangeLower

/-!
# The range of the simple walk, its first moment, and the hitting identity

The range of the simple walk as a measurable functional of the path, its first moment,
and the range identity of Step 3 of `lem:critical-density` (`parking.tex:1335-1345`):

    ∑_{z ≠ 0} P_z(T_0 ≤ m) = E_0 |R_m| - 1 ≤ m .

The paper reads the identity through the reversal `P_z(T_0 ≤ m) = P_0(T_z ≤ m)`. Here it
is the translation `walkPath z p j = z + walkPath 0 p j`, which turns "the walk from `z`
reaches the origin" into "the walk from the origin reaches `-z`", and negation is a
bijection of the sites, so no reversal is needed. The sum over the sites of the chance of
visiting one of them is the expected range, because the range is the sum over the sites of
the indicator that the walk visits them; and `E_0|R_m| ≤ m + 1` is the crude bound, that a
walk of `m` steps visits at most `m + 1` sites.

`lintegral_rangeCard` is the expectation of the range as a functional of the path, which
the shared library does not have.
-/

open LatticeProb (measurable_from_countable')

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Parking

variable {d : ℕ}

/-! ### The walk translated -/

/-- The walk from `z` is the walk from the origin translated by `z`, by induction on the
step count. -/
theorem walkPath_eq_add (z : Site d) (p : ℕ → Fin d × Bool) (j : ℕ) :
    walkPath z p j = z + walkPath (0 : Site d) p j := by
  induction j with
  | zero => simp [walkPath]
  | succ j ih => rw [walkPath, ih, walkPath, add_assoc]

/-- `z` lies in the image of the walk's first `t + 1` steps iff some step at or before
`t` lands on `z`. -/
theorem mem_rangeImage_iff (x z : Site d) (p : ℕ → Fin d × Bool) (t : ℕ) :
    z ∈ (Finset.range (t + 1)).image (fun j => walkPath x p j) ↔ ∃ j ≤ t, walkPath x p j = z := by
  simp [Finset.mem_image, Finset.mem_range]

/-- The range after `t` steps has at most `t + 1` sites, since it is the image of the
`t + 1`-element set `Finset.range (t + 1)`. -/
theorem rangeCard_le_succ (x : Site d) (p : ℕ → Fin d × Bool) (t : ℕ) :
    Parking.rangeCard x p t ≤ t + 1 := by
  classical
  rw [Parking.rangeCard]
  exact le_trans Finset.card_image_le (by rw [Finset.card_range])

/-- The event that the walk from `x` visits `z` by time `t` is measurable, being a
countable union over `j ≤ t` of the measurable events that step `j` lands on `z`. -/
theorem measurableSet_visit (x z : Site d) (t : ℕ) :
    MeasurableSet {p : ℕ → Fin d × Bool | ∃ j ≤ t, walkPath x p j = z} := by
  have hrw : {p : ℕ → Fin d × Bool | ∃ j ≤ t, walkPath x p j = z}
      = ⋃ j ∈ Set.Iic t, {p : ℕ → Fin d × Bool | walkPath x p j = z} := by
    ext p; simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Iic, exists_prop]
  rw [hrw]
  exact MeasurableSet.biUnion (Set.to_countable _)
    (fun j _ => (Parking.measurable_walkPath x j) (measurableSet_singleton z))

/-- The reversal via translation: the walk from `z` hits the origin by time `t` iff the
walk from the origin hits `-z` by time `t`. -/
theorem visit_zero_eq (z : Site d) (t : ℕ) :
    {p : ℕ → Fin d × Bool | ∃ j ≤ t, walkPath z p j = 0}
      = {p : ℕ → Fin d × Bool | ∃ j ≤ t, walkPath (0 : Site d) p j = -z} := by
  ext p
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, eq_neg_of_add_eq_zero_right (by rw [← walkPath_eq_add]; exact h)⟩
  · rintro ⟨j, hj, h⟩
    refine ⟨j, hj, ?_⟩
    rw [walkPath_eq_add, h, add_neg_cancel]


/-- The range, cast into `ℝ≥0∞`, is the sum over all sites of the indicator that the walk
visits them by time `t`. -/
theorem rangeCard_eq_tsum (x : Site d) (p : ℕ → Fin d × Bool) (t : ℕ) :
    (Parking.rangeCard x p t : ℝ≥0∞)
      = ∑' z : Site d, (if ∃ j ≤ t, walkPath x p j = z then (1 : ℝ≥0∞) else 0) := by
  classical
  set S : Finset (Site d) := (Finset.range (t + 1)).image (fun j => walkPath x p j) with hS
  have hiff : ∀ z : Site d,
      (if ∃ j ≤ t, walkPath x p j = z then (1 : ℝ≥0∞) else 0) = if z ∈ S then 1 else 0 := by
    intro z
    simp only [hS, mem_rangeImage_iff]
  rw [tsum_congr hiff]
  rw [tsum_eq_sum (s := S) (fun z hz => by simp [hz])]
  have hone : ∀ z ∈ S, (if z ∈ S then (1 : ℝ≥0∞) else 0) = 1 := fun z hz => by simp [hz]
  rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hS, Parking.rangeCard]

/-- The expected range is the sum, over all sites, of the probability that the walk
visits them by time `t`, by Tonelli's theorem applied to `rangeCard_eq_tsum`. -/
theorem lintegral_rangeCard (x : Site d) (t : ℕ) :
    ∫⁻ p, (Parking.rangeCard x p t : ℝ≥0∞) ∂(walkLaw d)
      = ∑' z : Site d, (walkLaw d) {p | ∃ j ≤ t, walkPath x p j = z} := by
  classical
  have hpt : ∀ p : ℕ → Fin d × Bool, (Parking.rangeCard x p t : ℝ≥0∞)
      = ∑' z : Site d, Set.indicator {p' : ℕ → Fin d × Bool | ∃ j ≤ t, walkPath x p' j = z}
          (1 : (ℕ → Fin d × Bool) → ℝ≥0∞) p := by
    intro p
    rw [rangeCard_eq_tsum]
    exact tsum_congr fun z => by simp [Set.indicator_apply]
  rw [lintegral_congr hpt]
  rw [lintegral_tsum (fun z => ((measurable_one.indicator
    (measurableSet_visit x z t)).aemeasurable))]
  exact tsum_congr fun z => lintegral_indicator_one (measurableSet_visit x z t)

/-- The sum over all sites `z` of the chance that the walk from `z` hits the origin by
time `t` equals the expected range from the origin, by the reversal `visit_zero_eq` and
reindexing the sum along the negation bijection of the sites. -/
theorem tsum_hitZero (t : ℕ) :
    ∑' z : Site d, (walkLaw d) {p | ∃ j ≤ t, walkPath z p j = 0}
      = ∫⁻ p, (Parking.rangeCard (0 : Site d) p t : ℝ≥0∞) ∂(walkLaw d) := by
  rw [lintegral_rangeCard]
  have h1 : ∀ z : Site d, (walkLaw d) {p | ∃ j ≤ t, walkPath z p j = 0}
      = (walkLaw d) {p | ∃ j ≤ t, walkPath (0 : Site d) p j = -z} := by
    intro z; rw [visit_zero_eq]
  rw [tsum_congr h1]
  exact (Equiv.neg (Site d)).tsum_eq
    (fun z : Site d => (walkLaw d) {p | ∃ j ≤ t, walkPath (0 : Site d) p j = z})

/-- **Step 3 of `lem:critical-density`.** The sum over `z ≠ 0` of the chance of hitting
the origin from `z` by time `t` is at most `t`, obtained by separating out the `z = 0`
term, which contributes exactly `1`, from the bound `E_0|R_t| ≤ t + 1`. -/
theorem tsum_hitZero_le (hd : 1 ≤ d) (t : ℕ) :
    ∑' z : Site d, (if z = 0 then 0 else (walkLaw d) {p | ∃ j ≤ t, walkPath z p j = 0})
      ≤ (t : ℝ≥0∞) := by
  classical
  haveI : IsProbabilityMeasure (walkLaw d) := Parking.walkLaw_isProbability hd
  have hzero : (walkLaw d) {p : ℕ → Fin d × Bool | ∃ j ≤ t, walkPath (0 : Site d) p j = 0} = 1 := by
    have huniv : {p : ℕ → Fin d × Bool | ∃ j ≤ t, walkPath (0 : Site d) p j = 0} = Set.univ := by
      ext p; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact ⟨0, Nat.zero_le t, rfl⟩
    rw [huniv, measure_univ]
  have hsplit : ∑' z : Site d, (walkLaw d) {p | ∃ j ≤ t, walkPath z p j = 0}
      = (walkLaw d) {p | ∃ j ≤ t, walkPath (0 : Site d) p j = 0}
        + ∑' z : Site d, (if z = 0 then 0 else (walkLaw d) {p | ∃ j ≤ t, walkPath z p j = 0}) :=
    Summable.tsum_eq_add_tsum_ite' (0 : Site d) ENNReal.summable
  have hbound : ∑' z : Site d, (walkLaw d) {p | ∃ j ≤ t, walkPath z p j = 0} ≤ (t : ℝ≥0∞) + 1 := by
    rw [tsum_hitZero]
    calc ∫⁻ p, (Parking.rangeCard (0 : Site d) p t : ℝ≥0∞) ∂(walkLaw d)
        ≤ ∫⁻ _p : ℕ → Fin d × Bool, ((t : ℝ≥0∞) + 1) ∂(walkLaw d) := by
          refine lintegral_mono fun p => ?_
          have h := rangeCard_le_succ (0 : Site d) p t
          have : ((Parking.rangeCard (0 : Site d) p t : ℕ) : ℝ≥0∞) ≤ ((t + 1 : ℕ) : ℝ≥0∞) :=
            Nat.cast_le.mpr h
          simpa using this
      _ = (t : ℝ≥0∞) + 1 := by simp
  rw [hsplit, hzero] at hbound
  have h1 : (1 : ℝ≥0∞) ≠ ⊤ := by simp
  refine (ENNReal.add_le_add_iff_left h1).mp ?_
  calc (1 : ℝ≥0∞) +
        ∑' z : Site d, (if z = 0 then 0 else (walkLaw d) {p | ∃ j ≤ t, walkPath z p j = 0})
      ≤ (t : ℝ≥0∞) + 1 := hbound
    _ = 1 + (t : ℝ≥0∞) := by rw [add_comm]


/-! ### The first moment of the range -/

/-- The expected range is finite, and at most `t + 1`. -/
theorem lintegral_rangeCard_le (hd : 1 ≤ d) (x : Site d) (t : ℕ) :
    ∫⁻ p, (Parking.rangeCard x p t : ℝ≥0∞) ∂(walkLaw d) ≤ (t : ℝ≥0∞) + 1 := by
  haveI : IsProbabilityMeasure (walkLaw d) := Parking.walkLaw_isProbability hd
  calc ∫⁻ p, (Parking.rangeCard x p t : ℝ≥0∞) ∂(walkLaw d)
      ≤ ∫⁻ _p : ℕ → Fin d × Bool, ((t : ℝ≥0∞) + 1) ∂(walkLaw d) := by
        refine lintegral_mono fun p => ?_
        have h : ((Parking.rangeCard x p t : ℕ) : ℝ≥0∞) ≤ ((t + 1 : ℕ) : ℝ≥0∞) :=
          Nat.cast_le.mpr (rangeCard_le_succ x p t)
        simpa using h
    _ = (t : ℝ≥0∞) + 1 := by simp

/-- The range is integrable, being bounded. -/
theorem integrable_rangeCard (hd : 1 ≤ d) (x : Site d) (t : ℕ) :
    Integrable (fun p => (Parking.rangeCard x p t : ℝ)) (walkLaw d) := by
  haveI : IsProbabilityMeasure (walkLaw d) := Parking.walkLaw_isProbability hd
  refine Integrable.mono' (integrable_const ((t : ℝ) + 1))
    (((measurable_from_countable' (fun n : ℕ => (n : ℝ))).comp
        (measurable_rangeCard x t)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h : ((Parking.rangeCard x p t : ℕ) : ℝ) ≤ ((t + 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (rangeCard_le_succ x p t)
  simpa using h

/-- `E_x|R_t| ≤ t + 1`, in the reals. -/
theorem integral_rangeCard_le (hd : 1 ≤ d) (x : Site d) (t : ℕ) :
    ∫ p, (Parking.rangeCard x p t : ℝ) ∂(walkLaw d) ≤ (t : ℝ) + 1 := by
  haveI : IsProbabilityMeasure (walkLaw d) := Parking.walkLaw_isProbability hd
  calc ∫ p, (Parking.rangeCard x p t : ℝ) ∂(walkLaw d)
      ≤ ∫ _p : ℕ → Fin d × Bool, ((t : ℝ) + 1) ∂(walkLaw d) := by
        refine integral_mono (integrable_rangeCard hd x t) (integrable_const _) fun p => ?_
        have h : ((Parking.rangeCard x p t : ℕ) : ℝ) ≤ ((t + 1 : ℕ) : ℝ) :=
          Nat.cast_le.mpr (rangeCard_le_succ x p t)
        simpa using h
    _ = (t : ℝ) + 1 := by simp

end Parking

end
