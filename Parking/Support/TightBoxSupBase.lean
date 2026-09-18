/-
The remaining gap in `happ`: a FIXED-RADIUS dyadic chaining bound, from the level-`0`
grid up to the level-`n1` grid, for `Parking.Yfield`.  This is deliberately NOT built by reusing
`LatticeProb.dtruncPi_dist_le`/`LatticeProb.dlimPi_sub_dtruncPi_le` directly: those lemmas'
hypothesis `hz : ∀ i, |z i| ≤ (m : ℝ)` ties the coordinate-radius bound to the SAME level `m`
that starts the chain (because the library's own `LatticeProb.DyadicIncBoundPi f a n₀` Prop
demands increment-bound coverage of radius EXACTLY `(n+1)` at level `n` — a "radius grows with
level" scheme built for the unbounded-domain Kolmogorov-Chentsov theorem).  Checked directly
against `dtruncPi_step`'s own proof (which derives its chaining-index range from `hz` via
`floor_range`): there is no way to instantiate it with `hz` at a SMALL level (like `0`) while `z`
ranges over a box of radius `n1 ≫ 0`.  So going from level `n1` DOWN to level `0` needs a
DIFFERENT, hand-built one-step lemma with the coordinate-radius bound `R` (fixed at `n1`)
DECOUPLED from the chaining level `m` (which ranges from `0` to `n1`).

The fix reuses the library's own combinatorial pieces (`LatticeProb.chainIdx`,
`chainIdx_zero`, `chainIdx_succ`, `chainIdx_top`, `LatticeProb.floor_succ_level_real`, all
public, all UNCONDITIONAL in the case of the floor-doubling facts) with two small
re-derivations of the two library lemmas that HARD-CODE the level-radius coupling
(`floor_range`, `chainIdx_range`): `Parking.floor_range_fixed` and
`Parking.chainIdx_range_fixed` are the identical proofs with the magnitude bound `R` and the
level exponent decoupled.  Since `Fin 2` has exactly two coordinates, the one-step lemma
(`Parking.yfield_step_fixed`) is written directly for the two steps (no generic induction over
`k` is needed), giving `|Yfield(dtruncPi (m+1) z) - Yfield(dtruncPi m z)| ≤ 2 * a(m+1)` for
`z` with `∀ i, |z i| ≤ R`, at EVERY level `m`, for the SAME fixed `R` throughout — the key
property that makes the finite telescoping sum from level `0` to level `R` well-posed with a
SINGLE hypothesis on `z`, unlike the library's growing-radius scheme.

Why this is enough to beat the exponential grid-count blowup: the moment bound
on `Parking.levelIncFixed R n m η` (the level-`m` increment, built as a genuine `Finset.sup'`
over the FIXED-radius level-`m` grid, `LatticeProb.boxIdx (R + 1) m`) has cardinality
`(2 * ((R + 1) * 2 ^ m) + 1) ^ 2`, i.e. `Θ(R² · 4^m)`: the radius `R` contributes only a
POLYNOMIAL prefactor `R²`, fixed across all levels `m`, while the `4^m` growth is the SAME
per-level grid-fineness factor whose decay (via the `p > 8` Kolmogorov exponent) already makes
the sum over `m` geometric in `TightBoxSupTail.lean`'s tail bound.  So summing the level-`m`
moments for `m = 1, …, R` (R := n1, chosen ≥ 2A) gives a bound `Θ(R²)` — polynomial in `R`, not
exponential — exactly the base term this route needs.
-/
import Parking.Support.TightBoxSupMoment

open MeasureTheory LatticeProb Filter Topology

noncomputable section

namespace Parking

/-! ### Two small re-derivations, decoupling the coordinate-radius bound from the level -/

/-- **`LatticeProb.floor_range`, with the magnitude bound `R` decoupled from the level
exponent `m`.**  Same proof, `R` in place of the level. -/
theorem floor_range_fixed {R m : ℕ} {x : ℝ} (hx : |x| ≤ (R : ℝ)) :
    |⌊x * 2 ^ m⌋| ≤ (R : ℤ) * 2 ^ m := by
  have habs : |x * 2 ^ m| ≤ (R : ℝ) * 2 ^ m := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ m)]
    exact mul_le_mul_of_nonneg_right hx (by positivity)
  have habsl := abs_le.mp habs
  have hfl : ⌊(-((R : ℝ) * 2 ^ m))⌋ = -((R : ℤ) * 2 ^ m) := by
    have heq : (-((R : ℝ) * 2 ^ m)) = ((-((R : ℤ) * 2 ^ m) : ℤ) : ℝ) := by push_cast; ring
    rw [heq, Int.floor_intCast]
  have hfr : ⌊((R : ℝ) * 2 ^ m)⌋ = (R : ℤ) * 2 ^ m := by
    have heq : ((R : ℝ) * 2 ^ m) = (((R : ℤ) * 2 ^ m : ℤ) : ℝ) := by push_cast; ring
    rw [heq, Int.floor_intCast]
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · rw [← hfl]; exact Int.floor_le_floor habsl.1
  · rw [← hfr]; exact Int.floor_le_floor habsl.2

/-- **`LatticeProb.chainIdx_range`, with the magnitude bound `B` decoupled from being of the
shape `n * 2 ^ n`.**  Identical proof (`nlinarith` from the two `abs_le`-unfolded bounds does
not use the specific shape of `B`). -/
theorem chainIdx_range_fixed {k : ℕ} (J₀ J₁ : Fin k → ℤ) (t : ℕ) {B : ℤ}
    (hJ₀ : ∀ i, |J₀ i| ≤ B) (hstep : ∀ i, |J₁ i - 2 * J₀ i| ≤ 1) :
    ∀ i, |LatticeProb.chainIdx J₀ J₁ t i| ≤ 2 * B + 1 := by
  intro i
  rw [LatticeProb.chainIdx]
  split
  · have h1 := hJ₀ i
    have h2 := hstep i
    rw [abs_le] at h1 h2 ⊢
    constructor <;> nlinarith
  · have h1 := hJ₀ i
    rw [abs_le] at h1 ⊢
    constructor <;> nlinarith

/-! ### The fixed-radius level-`m` grid pairs, and the actual max increment -/

/-- The `(grid index, direction)` pairs at level `m`, inside the box of FIXED coordinate radius
`R + 1` (not `m + 1`): every direction, at every grid point of the level-`m`, radius-`(R + 1)`
box. -/
def levelPairsFixed (R m : ℕ) : Finset ((Fin 2 → ℤ) × Fin 2) :=
  (LatticeProb.boxIdx (R + 1) m) ×ˢ (Finset.univ : Finset (Fin 2))

theorem levelPairsFixed_nonempty (R m : ℕ) : (levelPairsFixed R m).Nonempty := by
  refine ⟨(0, 0), ?_⟩
  rw [levelPairsFixed, Finset.mem_product]
  refine ⟨?_, Finset.mem_univ 0⟩
  rw [LatticeProb.mem_boxIdx_iff]
  intro i
  simp

/-- **The single fixed-radius dyadic increment term.** -/
def levelIncTermFixed (A : ℝ) (hA : 0 ≤ A) (n m : ℕ) (η : Site 2 → ℝ)
    (idx : (Fin 2 → ℤ) × Fin 2) : ℝ :=
  |Yfield A hA n η (LatticeProb.gridPt m (idx.1 + Pi.single idx.2 1)) -
    Yfield A hA n η (LatticeProb.gridPt m idx.1)|

theorem levelIncTermFixed_nonneg (A : ℝ) (hA : 0 ≤ A) (n m : ℕ) (η : Site 2 → ℝ)
    (idx : (Fin 2 → ℤ) × Fin 2) : 0 ≤ levelIncTermFixed A hA n m η idx :=
  abs_nonneg _

/-- **The actual maximum dyadic increment of `Yfield` at level `m`, within the FIXED box of
radius `R + 1`.** -/
def levelIncFixed (A : ℝ) (hA : 0 ≤ A) (R n m : ℕ) (η : Site 2 → ℝ) : ℝ :=
  (levelPairsFixed R m).sup' (levelPairsFixed_nonempty R m) (levelIncTermFixed A hA n m η)

theorem levelIncFixed_nonneg (A : ℝ) (hA : 0 ≤ A) (R n m : ℕ) (η : Site 2 → ℝ) :
    0 ≤ levelIncFixed A hA R n m η := by
  obtain ⟨idx, hidx⟩ := levelPairsFixed_nonempty R m
  exact le_trans (levelIncTermFixed_nonneg A hA n m η idx)
    (Finset.le_sup' (levelIncTermFixed A hA n m η) hidx)

theorem levelIncTermFixed_le (A : ℝ) (hA : 0 ≤ A) (n m : ℕ) (η : Site 2 → ℝ) {R : ℕ}
    {idx : (Fin 2 → ℤ) × Fin 2} (hmem : idx ∈ levelPairsFixed R m) :
    levelIncTermFixed A hA n m η idx ≤ levelIncFixed A hA R n m η :=
  Finset.le_sup' (levelIncTermFixed A hA n m η) hmem

/-! ### The one-step fixed-radius bound -/

/-- **The value of `Yfield` at consecutive dyadic truncations of a point of coordinate radius
`≤ R` differs by at most `2 * levelIncFixed R (m + 1)`, at EVERY level `m` — `R` fixed
throughout, decoupled from `m`.** -/
theorem yfield_step_fixed (A : ℝ) (hA : 0 ≤ A) (n : ℕ) (η : Site 2 → ℝ) (R m : ℕ)
    {z : Fin 2 → ℝ} (hz : ∀ i, |z i| ≤ (R : ℝ)) :
    |Yfield A hA n η (LatticeProb.dtruncPi (m + 1) z) -
        Yfield A hA n η (LatticeProb.dtruncPi m z)| ≤
      2 * levelIncFixed A hA R n (m + 1) η := by
  set J₀ : Fin 2 → ℤ := fun i => ⌊z i * 2 ^ m⌋ with hJ₀def
  set J₁ : Fin 2 → ℤ := fun i => ⌊z i * 2 ^ (m + 1)⌋ with hJ₁def
  have hJ₀ : ∀ i, |J₀ i| ≤ (R : ℤ) * 2 ^ m := fun i => floor_range_fixed (hz i)
  have hstep : ∀ i, |J₁ i - 2 * J₀ i| ≤ 1 := by
    intro i
    rcases LatticeProb.floor_succ_level_real m (z i) with h | h
    · simp only [hJ₁def, hJ₀def, h]; simp
    · simp only [hJ₁def, hJ₀def, h]; simp
  have hrange : ∀ t : ℕ, ∀ i, |LatticeProb.chainIdx J₀ J₁ t i| ≤ ((R : ℕ) + 1 : ℕ) * 2 ^ (m + 1) := by
    intro t i
    have hb := chainIdx_range_fixed J₀ J₁ t hJ₀ hstep i
    have hle : (2 * ((R : ℤ) * 2 ^ m) + 1) ≤ (((R : ℕ) + 1 : ℕ) : ℤ) * 2 ^ (m + 1) := by
      have h2 : (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m := by ring
      have hpow : (0 : ℤ) < 2 ^ m := by positivity
      push_cast
      nlinarith
    exact hb.trans hle
  have h00 : LatticeProb.chainIdx J₀ J₁ 0 = fun i => 2 * J₀ i := LatticeProb.chainIdx_zero J₀ J₁
  have h22 : LatticeProb.chainIdx J₀ J₁ 2 = J₁ := LatticeProb.chainIdx_top J₀ J₁
  have step_bound : ∀ t : ℕ, (ht : t < 2) →
      |Yfield A hA n η (LatticeProb.gridPt (m + 1) (LatticeProb.chainIdx J₀ J₁ (t + 1))) -
          Yfield A hA n η (LatticeProb.gridPt (m + 1) (LatticeProb.chainIdx J₀ J₁ t))| ≤
        levelIncFixed A hA R n (m + 1) η := by
    intro t ht
    have hsucc := LatticeProb.chainIdx_succ J₀ J₁ ht
    set i0 : Fin 2 := ⟨t, ht⟩ with hi0def
    rcases LatticeProb.floor_succ_level_real m (z i0) with hδ | hδ
    · have hz0 : J₁ i0 - 2 * J₀ i0 = 0 := by simp only [hJ₁def, hJ₀def, hδ]; ring
      rw [hsucc, hz0, Pi.single_zero, add_zero, sub_self, abs_zero]
      exact levelIncFixed_nonneg A hA R n (m + 1) η
    · have hz1 : J₁ i0 - 2 * J₀ i0 = 1 := by simp only [hJ₁def, hJ₀def, hδ]; ring
      rw [hsucc, hz1]
      have hmem : (LatticeProb.chainIdx J₀ J₁ t, i0) ∈ levelPairsFixed R (m + 1) := by
        rw [levelPairsFixed, Finset.mem_product]
        refine ⟨(LatticeProb.mem_boxIdx_iff (R + 1) (m + 1) _).mpr ?_, Finset.mem_univ i0⟩
        intro i
        have := hrange t i
        push_cast
        exact_mod_cast this
      have hle := levelIncTermFixed_le A hA n (m + 1) η hmem
      unfold levelIncTermFixed at hle
      exact hle
  have h0 := step_bound 0 (by norm_num)
  have h1 := step_bound 1 (by norm_num)
  have htri : |Yfield A hA n η (LatticeProb.gridPt (m + 1) (LatticeProb.chainIdx J₀ J₁ 2)) -
        Yfield A hA n η (LatticeProb.gridPt (m + 1) (LatticeProb.chainIdx J₀ J₁ 0))| ≤
      |Yfield A hA n η (LatticeProb.gridPt (m + 1) (LatticeProb.chainIdx J₀ J₁ 2)) -
          Yfield A hA n η (LatticeProb.gridPt (m + 1) (LatticeProb.chainIdx J₀ J₁ 1))| +
        |Yfield A hA n η (LatticeProb.gridPt (m + 1) (LatticeProb.chainIdx J₀ J₁ 1)) -
            Yfield A hA n η (LatticeProb.gridPt (m + 1) (LatticeProb.chainIdx J₀ J₁ 0))| :=
    abs_sub_le _ _ _
  have hfinal := htri.trans (add_le_add h1 h0)
  have heq0 : LatticeProb.gridPt (m + 1) (LatticeProb.chainIdx J₀ J₁ 0) =
      LatticeProb.dtruncPi m z := by
    rw [h00]
    exact LatticeProb.gridPt_two_mul m J₀
  have heq2 : LatticeProb.gridPt (m + 1) (LatticeProb.chainIdx J₀ J₁ 2) =
      LatticeProb.dtruncPi (m + 1) z := by
    rw [h22]; rfl
  rw [heq0, heq2] at hfinal
  linarith [hfinal]

/-! ### The finite telescoping sum, from level `0` to any level `t ≤ R` -/

/-- **The finite telescoping bound**: `Yfield` at the level-`t` and level-`0` truncations of a
point of coordinate radius `≤ R` differ by at most twice the sum of the fixed-radius level
increments from `1` to `t` — for the SAME `R` throughout, so a SINGLE hypothesis on `z`
suffices for every step. -/
theorem yfield_dtruncPi_dist_le_fixed (A : ℝ) (hA : 0 ≤ A) (n : ℕ) (η : Site 2 → ℝ) (R : ℕ)
    {z : Fin 2 → ℝ} (hz : ∀ i, |z i| ≤ (R : ℝ)) :
    ∀ t : ℕ, |Yfield A hA n η (LatticeProb.dtruncPi t z) -
        Yfield A hA n η (LatticeProb.dtruncPi 0 z)| ≤
      2 * ∑ s ∈ Finset.range t, levelIncFixed A hA R n (s + 1) η := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    calc |Yfield A hA n η (LatticeProb.dtruncPi (t + 1) z) -
            Yfield A hA n η (LatticeProb.dtruncPi 0 z)|
        ≤ |Yfield A hA n η (LatticeProb.dtruncPi (t + 1) z) -
              Yfield A hA n η (LatticeProb.dtruncPi t z)| +
            |Yfield A hA n η (LatticeProb.dtruncPi t z) -
                Yfield A hA n η (LatticeProb.dtruncPi 0 z)| := abs_sub_le _ _ _
      _ ≤ 2 * levelIncFixed A hA R n (t + 1) η +
            2 * ∑ s ∈ Finset.range t, levelIncFixed A hA R n (s + 1) η :=
          add_le_add (yfield_step_fixed A hA n η R t hz) ih
      _ = 2 * ∑ s ∈ Finset.range (t + 1), levelIncFixed A hA R n (s + 1) η := by
          rw [Finset.sum_range_succ]; ring

end Parking

end
