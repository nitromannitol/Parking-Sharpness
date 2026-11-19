import Parking.Support.RangeBoxIteration
import Parking.Support.TailRangeBounds
import LatticeProb.Walk.Shells

/-!
# Confinement and the range moment

Repeated returns to a finite box give a lower bound on the exponential moment
of the random-walk range.
-/

open MeasureTheory

noncomputable section

namespace Parking

variable {d : ℕ}

/-- A uniform box-block probability yields a lower bound for the range moment
at every time covered by the blocks. -/
theorem exp_mul_pow_le_rangeExp_of_boxBlocks (hd : 1 ≤ d) {a : ℝ} (ha : 0 ≤ a)
    (n j t L : ℕ) (c : ℝ) (hc : 0 ≤ c) (ht : t ≤ j * n)
    (hblock : ∀ y : Site d, (∀ i, |(y i : ℝ)| ≤ (L : ℝ)) →
      c ≤ (LatticeProb.siteWalkLaw d y).real (boxBlock n L)) :
    Real.exp (-(a * (((4 * L + 1 : ℕ) ^ d : ℕ) : ℝ))) * c ^ j ≤ rangeExp d a t := by
  have : NeZero d := ⟨by omega⟩
  let B : Finset (Site d) := LatticeProb.boxFinset 0 (2 * L)
  have hsub : boxBlock (j * n) (L : ℝ) ⊆
      {X : ℕ → Site d | ∀ k ≤ t, X k ∈ B} := by
    intro X hX k hk
    apply LatticeProb.mem_boxFinset_iff.mpr
    intro i
    have hbound := hX.1 k (le_trans hk ht) i
    have hreal : |(X k i : ℝ)| ≤ ((2 * L : ℕ) : ℝ) := by
      push_cast
      exact hbound
    have hint : |X k i| ≤ ((2 * L : ℕ) : ℤ) := by exact_mod_cast hreal
    simpa [B] using hint
  have hpow : c ^ j ≤ (LatticeProb.siteWalkLaw d 0).real (boxBlock (j * n) (L : ℝ)) :=
    pow_le_measureReal_boxBlock_mul hd n L c (by positivity) hc hblock j 0 (by simp)
  have hprob := measureReal_mono (μ := LatticeProb.siteWalkLaw d 0) hsub (measure_ne_top _ _)
  have hcard : B.card = (4 * L + 1) ^ d := by
    rw [show B = LatticeProb.boxFinset (0 : Site d) (2 * L) from rfl,
      LatticeProb.card_boxFinset_zero]
    congr 1
    omega
  have hconf := rangeExp_ge_exp_mul_confinement_probability hd ha B t
  rw [hcard] at hconf
  exact (mul_le_mul_of_nonneg_left (hpow.trans hprob) (Real.exp_nonneg _)).trans hconf

/-- A box of radius proportional to `d * k` and blocks of length `2 * k²`
give an explicit lower bound for the range moment. -/
theorem exp_mul_pow_le_rangeExp (hd : 1 ≤ d) {a : ℝ} (ha : 0 ≤ a)
    (k t : ℕ) (hk : 1 ≤ k) :
    Real.exp (-(a * (((8 * d * k + 1 : ℕ) ^ d : ℕ) : ℝ))) *
      ((2 * (2 : ℝ) ^ d)⁻¹) ^ (t / (2 * k ^ 2) + 1) ≤ rangeExp d a t := by
  let n : ℕ := 2 * k ^ 2
  let L : ℕ := 2 * d * k
  let j : ℕ := t / n + 1
  let c : ℝ := (2 * (2 : ℝ) ^ d)⁻¹
  have hn : 1 ≤ n := by dsimp [n]; nlinarith
  have ht : t ≤ j * n := by
    have hmod := Nat.mod_lt t (by omega : 0 < n)
    have hdiv := Nat.div_add_mod t n
    dsimp [j]
    nlinarith
  have hr : 0 < 2 * (k : ℝ) := by exact_mod_cast (show 0 < 2 * k by omega)
  have hnreal : (n : ℝ) ≤ (2 * (k : ℝ)) ^ 2 / 2 := by
    dsimp [n]
    push_cast
    ring_nf
    rfl
  have hL : (d : ℝ) * (2 * (k : ℝ)) ≤ (L : ℝ) := by
    dsimp [L]
    push_cast
    ring_nf
    rfl
  have hpow : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hblock : ∀ y : Site d, (∀ i, |(y i : ℝ)| ≤ (L : ℝ)) →
      c ≤ (LatticeProb.siteWalkLaw d y).real (boxBlock n L) := by
    intro y hy
    have h := half_le_pow_mul_measureReal_boxBlock hd n y hr hnreal hL hy
    have heq : c = (1 / 2 : ℝ) / (2 : ℝ) ^ d := by
      dsimp [c]
      field_simp
    rw [heq, div_le_iff₀ hpow]
    simpa [mul_comm] using h
  have h := exp_mul_pow_le_rangeExp_of_boxBlocks hd ha n j t L c hc ht hblock
  have hL' : 4 * L + 1 = 8 * d * k + 1 := by dsimp [L]; ring
  rw [hL'] at h
  simpa only [n, j, c] using h

end Parking

end
