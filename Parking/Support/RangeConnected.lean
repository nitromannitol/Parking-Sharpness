import Parking.Support.RangeFixedSet
import LatticeProb.Prob.Percolation.Peierls.Animals

/-!
# Connectedness of the walk range

The range of the nearest-neighbour walk is connected, and therefore belongs to
an exponentially bounded family of finite sets of the same cardinality.
-/

open MeasureTheory LatticeProb LatticeProb.Percolation.Peierls

noncomputable section

namespace Parking

variable {d : ℕ}

/-- The finite set of positions visited by the signed-direction walk. -/
def walkRange (x : Site d) (p : ℕ → Fin d × Bool) (t : ℕ) : Finset (Site d) :=
  (Finset.range (t + 1)).image (walkPath x p)

/-- The displacement of any signed direction is nonzero. -/
theorem stepVec_ne_zero (b : Fin d × Bool) : stepVec b ≠ 0 := by
  obtain ⟨i, b⟩ := b
  intro h
  have hi := congrFun h i
  cases b <;> simp [stepVec, LatticeProb.unit] at hi

/-- Successive positions of the walk are adjacent in the king graph. -/
theorem star_walkPath_succ (x : Site d) (p : ℕ → Fin d × Bool) (t : ℕ) :
    xmh_star (walkPath x p t) (walkPath x p (t + 1)) := by
  constructor
  · intro h
    have heq : walkPath x p t + stepVec (p t) = walkPath x p t := by
      simpa only [walkPath] using h.symm
    exact stepVec_ne_zero (p t) (add_eq_left.mp heq)
  · intro i
    rw [walkPath]
    simp only [Pi.add_apply]
    have heq : walkPath x p t i - (walkPath x p t i + stepVec (p t) i) =
        -stepVec (p t) i := by ring
    rw [heq, abs_neg]
    exact abs_stepVec_le_one (p t) i

/-- The range of the signed-direction walk is king-connected. -/
theorem walkRange_starConnected (x : Site d) (p : ℕ → Fin d × Bool) :
    ∀ t : ℕ, xmh_SConn (walkRange x p t : Set (Site d)) := by
  intro t
  induction t with
  | zero =>
      have heq : walkRange x p 0 = {x} := by simp [walkRange, walkPath]
      rw [heq]
      simpa using xmh_SConn_singleton x
  | succ t ih =>
      have heq : walkRange x p (t + 1) = insert (walkPath x p (t + 1)) (walkRange x p t) := by
        simp only [walkRange, Finset.range_add_one, Finset.image_insert]
      have hmem : walkPath x p t ∈ walkRange x p t := by
        exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (Nat.lt_succ_self t), rfl⟩
      rw [heq]
      simpa only [Finset.coe_insert] using
        xmh_SConn_insert ih hmem (star_walkPath_succ x p t)

/-- Ranges of a fixed cardinality are covered by an exponentially bounded
family of finite sets. -/
theorem exists_walkRange_cover : ∃ K : ℕ, ∀ (m : ℕ),
    ∃ T : Finset (Finset (Site d)), T.card ≤ K ^ m ∧
      ∀ (p : ℕ → Fin d × Bool) (t : ℕ), rangeCard (0 : Site d) p t = m →
        walkRange 0 p t ∈ T := by
  obtain ⟨K, hK⟩ := xmh_starCount d
  refine ⟨K, fun m => ?_⟩
  obtain ⟨T, hT, hcover⟩ := hK 0 m
  refine ⟨T, hT, fun p t hm => ?_⟩
  apply hcover
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ t), by simp [walkPath]⟩
  · exact hm
  · exact walkRange_starConnected 0 p t

/-- For a fixed range size, an exponential count of possible ranges and
the finite-set survival bound give a geometric probability estimate. -/
theorem exists_rangeCard_eq_upper (hd : 1 ≤ d) : ∃ K : ℕ, ∀ m n t : ℕ, 1 ≤ n →
    (m : ℝ) * (Real.sqrt 2 ^ d * greenConst d * (n : ℝ) ^ (-(d : ℝ) / 2)) ≤ 1 / 2 →
    (walkLaw d).real {p | rangeCard (0 : Site d) p t = m} ≤
      (K : ℝ) ^ m * (1 / 2 : ℝ) ^ (t / n) := by
  classical
  have := stepLaw_isProbability hd
  have : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  obtain ⟨K, hcover⟩ := exists_walkRange_cover (d := d)
  refine ⟨K, fun m n t hn hsmall => ?_⟩
  obtain ⟨T, hcard, hT⟩ := hcover m
  let U := T.filter fun B => B.card = m
  let E : Finset (Site d) → Set (ℕ → Fin d × Bool) :=
    fun B => {p | ∀ i ≤ t, walkPath (0 : Site d) p i ∈ B}
  have hsub : {p | rangeCard (0 : Site d) p t = m} ⊆ ⋃ B ∈ U, E B := by
    intro p hp
    refine Set.mem_iUnion.mpr ⟨walkRange 0 p t, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨hT p t hp, hp⟩
    · intro i hi
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩
  have htime : t % n + (t / n) * n = t := by
    have h := Nat.div_add_mod t n
    nlinarith
  have heach : ∀ B ∈ U, (walkLaw d).real (E B) ≤ (1 / 2 : ℝ) ^ (t / n) := by
    intro B hB
    have hsize : B.card = m := (Finset.mem_filter.mp hB).2
    have hBsmall : (B.card : ℝ) *
        (Real.sqrt 2 ^ d * greenConst d * (n : ℝ) ^ (-(d : ℝ) / 2)) ≤ 1 / 2 := by
      rw [hsize]
      exact hsmall
    have h := measureReal_walkLaw_stayIn_le_half_pow hd B n hn hBsmall (t / n) (t % n)
    rw [htime] at h
    exact h
  calc (walkLaw d).real {p | rangeCard (0 : Site d) p t = m}
      ≤ (walkLaw d).real (⋃ B ∈ U, E B) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ B ∈ U, (walkLaw d).real (E B) := measureReal_biUnion_finset_le U E
    _ ≤ ∑ _B ∈ U, (1 / 2 : ℝ) ^ (t / n) := Finset.sum_le_sum heach
    _ = (U.card : ℝ) * (1 / 2 : ℝ) ^ (t / n) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (K : ℝ) ^ m * (1 / 2 : ℝ) ^ (t / n) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hU : U.card ≤ T.card := Finset.card_filter_le _ _
      exact_mod_cast hU.trans hcard

end Parking

end
