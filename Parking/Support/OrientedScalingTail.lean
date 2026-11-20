import Parking.Support.TightHappBound

/-!
# A uniform maximal bound for the scaled oriented walk

A maximal inequality for the coordinate-difference walk controls the probability
of leaving a fixed spatial interval before a fixed rescaled time horizon.
-/

open MeasureTheory

noncomputable section

namespace Parking

/-- The scaled oriented walk's exit event before the time horizon. -/
def orientedScaledExit (n : ℕ) (T A : ℝ) : Set (ℕ → Fin 2 × Bool) :=
  {p | ∃ k ≤ ⌊(n : ℝ) * T⌋₊, A ≤ |orientedScaledSite n (orientedPath (0 : Site 2) p k)|}

/-- The scaled exit event is measurable. -/
theorem measurableSet_orientedScaledExit (n : ℕ) (T A : ℝ) :
    MeasurableSet (orientedScaledExit n T A) := by
  have heq : orientedScaledExit n T A = ⋃ k ∈ Finset.range (⌊(n : ℝ) * T⌋₊ + 1),
      {p | A ≤ |orientedScaledSite n (orientedPath (0 : Site 2) p k)|} := by
    ext p
    simp only [orientedScaledExit, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range]
    constructor
    · rintro ⟨k, hk, h⟩; exact ⟨k, by omega, h⟩
    · rintro ⟨k, hk, h⟩; exact ⟨k, by omega, h⟩
  rw [heq]
  refine MeasurableSet.biUnion (Finset.range _).countable_toSet (fun k _ => ?_)
  simp_rw [orientedScaledSite_orientedPath]
  exact measurableSet_le measurable_const ((measurable_walkPartialSum k).div_const _).abs

/-- The probability of exiting a fixed interval is bounded uniformly in the
    scale by a constant times the inverse square of its radius. -/
theorem measureReal_orientedScaledExit_le {n : ℕ} (hn : 1 ≤ n)
    {T A : ℝ} (hT : 0 ≤ T) (hA : 0 < A) :
    (walkLaw 2).real (orientedScaledExit n T A) ≤ (T + 1) ^ 2 / (4 * A ^ 2) := by
  have := stepLaw_isProbability (d := 2) (by norm_num)
  have : IsProbabilityMeasure (walkLaw 2) := by unfold walkLaw; infer_instance
  let K : ℕ := ⌊(n : ℝ) * T⌋₊ + 1
  let a : ℝ := A / (2 * (T + 1))
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < a := by dsimp [a]; positivity
  have hK : 1 ≤ K := by dsimp [K]; omega
  have hKle : (K : ℝ) ≤ (n : ℝ) * (T + 1) := by
    have hf := Nat.floor_le (mul_nonneg (by positivity : (0 : ℝ) ≤ n) hT)
    dsimp [K]
    push_cast
    nlinarith
  have hrn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hrK : 0 ≤ Real.sqrt (K : ℝ) := Real.sqrt_nonneg _
  have hsqrtn : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
  have hsqrtK : Real.sqrt (K : ℝ) ^ 2 = K := Real.sq_sqrt (by positivity)
  have hsqrt : Real.sqrt (K : ℝ) ≤ (T + 1) * Real.sqrt n := by
    have hfactor : T + 1 ≤ (T + 1) ^ 2 := by nlinarith
    have hprod := mul_le_mul_of_nonneg_left hfactor (show (0 : ℝ) ≤ n by positivity)
    have hsqcomp : Real.sqrt (K : ℝ) ^ 2 ≤ ((T + 1) * Real.sqrt n) ^ 2 := by
      rw [mul_pow, hsqrtn, hsqrtK]
      nlinarith
    have hright : 0 ≤ (T + 1) * Real.sqrt n := by positivity
    nlinarith
  have hsubset : orientedScaledExit n T A ⊆ walkBad K a := by
    intro p hp
    obtain ⟨k, hk, hlarge⟩ := hp
    refine ⟨k, by dsimp [K]; omega, ?_⟩
    rw [orientedScaledSite_orientedPath, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.sqrt n)] at hlarge
    have hstep : 2 * A * Real.sqrt n ≤ |walkPartialSum k p| := by
      have := (le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt n)).mp hlarge
      nlinarith
    have hcompare : 4 * a * Real.sqrt K ≤ 2 * A * Real.sqrt n := by
      dsimp [a]
      have hnon : 0 ≤ A / (T + 1) := by positivity
      have hh := mul_le_mul_of_nonneg_left hsqrt hnon
      field_simp at hh ⊢
      nlinarith
    exact hcompare.trans hstep
  have hprob : (walkLaw 2).real (orientedScaledExit n T A) ≤ (walkLaw 2).real (walkBad K a) :=
    measureReal_mono hsubset
  have hmax := measureReal_sup_walkPartialSum_sq_le K hK ha
  calc
    (walkLaw 2).real (orientedScaledExit n T A) ≤ (walkLaw 2).real (walkBad K a) := hprob
    _ ≤ 1 / (16 * a ^ 2) := hmax
    _ = (T + 1) ^ 2 / (4 * A ^ 2) := by
      dsimp [a]
      field_simp; ring

end Parking
