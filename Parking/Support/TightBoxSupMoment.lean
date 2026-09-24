/-
The estimate to which `happ` reduces (see `Parking/Support/TightGYBoxBound.lean`) is a bound,
UNIFORM IN `n`, on `E_η[‖Parking.boxRewardMap 1 h1 A hA n η‖^2]`, i.e. on the `L^2` moment of the
supremum of the box-clamped rescaled reward field over the whole cutoff box.  Neither the
library's own `LatticeProb.KolmogorovSup.integral_sup_sub_rpow_le_of_kolmogorov`
(`SupTail.lean`) nor its companion in `SupTailQuant.lean` can be applied to this field directly:
both need an ALMOST-SURE modulus of continuity at a FIXED (non-random) scale `δ`, and for a
field built from an UNBOUNDED-tail scenery `η` (only an exponential-moment tail is assumed) this
is false at every fixed `δ`, not merely unproved.

The route here is the classical Kolmogorov-Chentsov dyadic-chaining moment bound, built directly:

1. **Globalize.** `Parking.orientedBoxReward`'s increment bound
   (`Parking.exists_orientedBoxReward_kolmogorov`) only holds for points INSIDE the cutoff box.
   Composing with `LatticeProb.boxClamp` (already in the library, `KolmogorovPi.lean`) gives a
   field `Yfield` defined and CONTINUOUS on all of `Fin 2 → ℝ`, equal to the true field on the
   box (`LatticeProb.boxClamp_eq`), with the SAME increment/moment bounds holding GLOBALLY (since
   `LatticeProb.dist_boxClamp_le` is a contraction and `LatticeProb.boxClamp_mem` always lands
   back in the box).
2. **Chain.** `Yfield`'s own dyadic-adjacent increments, at every level `m`, are bounded by a
   RANDOM but ALWAYS WELL-DEFINED quantity `a(m)`, the actual maximum of the (finitely many)
   relevant increments — trivially satisfying `LatticeProb.DyadicIncBoundPi` by construction, no
   almost-sure argument needed. `LatticeProb.dtruncPi_step` (already in the library,
   `ChentsovPi.lean`) then bounds `Yfield`'s value at any box point by a telescoping sum of the
   `a(m)`, deterministically, for EVERY realization.
3. **Sum the moments.** `E[a(m)^p]` is bounded via `(max)^p ≤ Σ(increment)^p`, using the
   GLOBAL increment bound of step 1 at the (fixed, `4^m`-many) dyadic pairs of a fixed-size box —
   `LatticeProb.card_boxIdx_level_le` counts them. The resulting series in `m` is bounded by a
   GEOMETRIC series (`LatticeProb.summable_polynomial_geometric`) once the increment exponent
   `q = p / 4` exceeds the dimension `2`, i.e. `p > 8`. Minkowski's inequality for finite sums
   (`MeasureTheory.eLpNorm_sum_le`) plus monotone convergence sums the series in `L^p`.
4. **Convert.** Lyapunov's inequality (`E[X^2] ≤ (E[X^p])^{2/p}` for `p ≥ 2`) turns the `L^p`
   bound into the `L^2` bound `happ` needs.
-/
import Parking.Support.TightKolmogorov
import Parking.Support.TightBoxMoment
import LatticeProb.Prob.ChentsovPiModification

open MeasureTheory LatticeProb Filter Topology

noncomputable section

namespace Parking

/-! ### The box, in `Fin 2 → ℝ` form -/

/-- The lower corner of the cutoff box, matching `Parking.orientedBox 1 A`. -/
def boxLo (A : ℝ) : Fin 2 → ℝ := ![0, -(2 * A)]

/-- The upper corner of the cutoff box, matching `Parking.orientedBox 1 A`. -/
def boxHi (A : ℝ) : Fin 2 → ℝ := ![1, 2 * A]

theorem boxLo_le_boxHi {A : ℝ} (hA : 0 ≤ A) : boxLo A ≤ boxHi A := by
  intro i
  unfold boxLo boxHi
  fin_cases i <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_zero, Fin.mk_one] <;>
    linarith

theorem mem_orientedBox_iff_mem_Icc {A : ℝ} (u : Fin 2 → ℝ) :
    u ∈ orientedBox 1 A ↔ u ∈ Set.Icc (boxLo A) (boxHi A) := by
  rfl

/-! ### `Yfield`: the box-clamped rescaled reward field, defined and continuous globally -/

/-- **`Yfield`**: `Parking.orientedBoxReward` at horizon `1`, precomposed with clamping the
argument to the cutoff box.  Globally defined and continuous, and equal to the true field on
the box itself. -/
def Yfield (A : ℝ) (hA : 0 ≤ A) (n : ℕ) (η : Site 2 → ℝ) (v : Fin 2 → ℝ) : ℝ :=
  orientedBoxReward 1 n η (LatticeProb.boxClamp (boxLo A) (boxHi A) (boxLo_le_boxHi hA) v)

theorem continuous_Yfield {A : ℝ} (hA : 0 ≤ A) (n : ℕ) (η : Site 2 → ℝ) :
    Continuous (Yfield A hA n η) :=
  (continuous_orientedBoxReward 1 n η).comp
    (LatticeProb.continuous_boxClamp (boxLo A) (boxHi A) (boxLo_le_boxHi hA))

theorem measurable_Yfield {A : ℝ} (hA : 0 ≤ A) (n : ℕ) (v : Fin 2 → ℝ) :
    Measurable fun η : Site 2 → ℝ => Yfield A hA n η v :=
  measurable_orientedBoxReward 1 n
    (LatticeProb.boxClamp (boxLo A) (boxHi A) (boxLo_le_boxHi hA) v)

theorem Yfield_eq_of_mem {A : ℝ} (hA : 0 ≤ A) (n : ℕ) (η : Site 2 → ℝ) {v : Fin 2 → ℝ}
    (hv : v ∈ orientedBox 1 A) : Yfield A hA n η v = orientedBoxReward 1 n η v := by
  unfold Yfield
  rw [LatticeProb.boxClamp_eq (boxLo_le_boxHi hA) hv]

theorem boxClamp_mem_orientedBox {A : ℝ} (hA : 0 ≤ A) (v : Fin 2 → ℝ) :
    LatticeProb.boxClamp (boxLo A) (boxHi A) (boxLo_le_boxHi hA) v ∈ orientedBox 1 A :=
  LatticeProb.boxClamp_mem (boxLo A) (boxHi A) (boxLo_le_boxHi hA) v

/-- **`Yfield`'s base-point moment bound holds at EVERY point, uniformly**, via
`Parking.exists_orientedBoxReward_moment` at the (always box-valid) clamped point. -/
theorem exists_Yfield_moment (ν : Measure ℤ) (hν : CriticalLaw ν) (p : ℝ) (hp : 2 ≤ p) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (A : ℝ) (hA : 0 ≤ A) (n : ℕ), 1 ≤ n → ∀ v : Fin 2 → ℝ,
      Integrable (fun η : Site 2 → ℝ => |Yfield A hA n η v| ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, |Yfield A hA n η v| ^ p ∂(iidLaw 2 (realLaw ν))) ≤ M := by
  obtain ⟨M, hM, hb⟩ := exists_orientedBoxReward_moment ν hν p hp 1 (by norm_num)
  refine ⟨M, hM, fun A hA n hn v => ?_⟩
  have hu0 : (0 : ℝ) ≤ LatticeProb.boxClamp (boxLo A) (boxHi A) (boxLo_le_boxHi hA) v 0 :=
    (boxClamp_mem_orientedBox hA v).1 0
  have := hb n hn (LatticeProb.boxClamp (boxLo A) (boxHi A) (boxLo_le_boxHi hA) v) hu0
  exact this

/-- **`Yfield`'s increment moment bound holds GLOBALLY, at every pair of points**, via
`Parking.exists_orientedBoxReward_kolmogorov` at the (always box-valid) clamped points, and the
fact that clamping is a contraction of the distance.  The witness `M` is bounded by
`Parking.orientedBoxRewardKolmogorovK ν hν p hp 1 * (1 + A) ^ (p / 2)`, an `A`-independent
constant times the same polynomial growth rate as `exists_orientedBoxReward_kolmogorov`. -/
theorem exists_Yfield_kolmogorov (ν : Measure ℤ) (hν : CriticalLaw ν) (p : ℝ) (hp : 2 ≤ p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ℝ) (hA : 0 ≤ A), ∃ M : ℝ, 0 ≤ M ∧ M ≤ K * (1 + A) ^ (p / 2) ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ v v' : Fin 2 → ℝ,
      Integrable (fun η : Site 2 → ℝ => |Yfield A hA n η v - Yfield A hA n η v'| ^ p)
        (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, |Yfield A hA n η v - Yfield A hA n η v'| ^ p
          ∂(iidLaw 2 (realLaw ν))) ≤ M * (dist v v') ^ (p / 4) := by
  obtain ⟨K, hKnn, hKall⟩ := exists_orientedBoxReward_kolmogorov ν hν p hp 1 (by norm_num)
  refine ⟨K, hKnn, fun A hA => ?_⟩
  obtain ⟨M, hM, hMbd, hb⟩ := hKall A hA
  refine ⟨M, hM, hMbd, fun n hn v v' => ?_⟩
  set cv := LatticeProb.boxClamp (boxLo A) (boxHi A) (boxLo_le_boxHi hA) v with hcv
  set cv' := LatticeProb.boxClamp (boxLo A) (boxHi A) (boxLo_le_boxHi hA) v' with hcv'
  have hmem : cv ∈ orientedBox 1 A := boxClamp_mem_orientedBox hA v
  have hmem' : cv' ∈ orientedBox 1 A := boxClamp_mem_orientedBox hA v'
  obtain ⟨hint, hbound⟩ := hb n hn cv cv' hmem hmem'
  have hdist : dist cv cv' ≤ dist v v' :=
    LatticeProb.dist_boxClamp_le (boxLo A) (boxHi A) (boxLo_le_boxHi hA) v v'
  have hp4 : (0 : ℝ) ≤ p / 4 := by linarith
  refine ⟨hint, le_trans hbound ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hdist hp4) hM

/-! ### The dyadic level-`m` grid pairs inside a fixed box, and the actual max increment -/

/-- The `(grid index, direction)` pairs relevant to `LatticeProb.DyadicIncBoundPi` at level `m`:
every direction, at every grid point of the level-`m`, radius-`(m+1)` box. -/
def levelPairs (m : ℕ) : Finset ((Fin 2 → ℤ) × Fin 2) :=
  (LatticeProb.boxIdx (m + 1) m) ×ˢ (Finset.univ : Finset (Fin 2))

theorem levelPairs_nonempty (m : ℕ) : (levelPairs m).Nonempty := by
  refine ⟨(0, 0), ?_⟩
  rw [levelPairs, Finset.mem_product]
  refine ⟨?_, Finset.mem_univ 0⟩
  rw [LatticeProb.mem_boxIdx_iff]
  intro i
  simp

/-- **The single dyadic increment term**, named to keep the elaborator from repeatedly
processing a large inline lambda. -/
def levelIncTerm (A : ℝ) (hA : 0 ≤ A) (n m : ℕ) (η : Site 2 → ℝ)
    (idx : (Fin 2 → ℤ) × Fin 2) : ℝ :=
  |Yfield A hA n η (LatticeProb.gridPt m (idx.1 + Pi.single idx.2 1)) -
    Yfield A hA n η (LatticeProb.gridPt m idx.1)|

theorem levelIncTerm_nonneg (A : ℝ) (hA : 0 ≤ A) (n m : ℕ) (η : Site 2 → ℝ)
    (idx : (Fin 2 → ℤ) × Fin 2) : 0 ≤ levelIncTerm A hA n m η idx :=
  abs_nonneg _

/-- **The actual maximum dyadic increment of `Yfield` at level `m`.**  A finite `Finset.sup'`,
well-defined for EVERY realization — no almost-sure argument is used to construct it. -/
def levelInc (A : ℝ) (hA : 0 ≤ A) (n m : ℕ) (η : Site 2 → ℝ) : ℝ :=
  (levelPairs m).sup' (levelPairs_nonempty m) (levelIncTerm A hA n m η)

theorem levelInc_nonneg (A : ℝ) (hA : 0 ≤ A) (n m : ℕ) (η : Site 2 → ℝ) :
    0 ≤ levelInc A hA n m η := by
  obtain ⟨idx, hidx⟩ := (levelPairs_nonempty m)
  exact le_trans (levelIncTerm_nonneg A hA n m η idx)
    (Finset.le_sup' (levelIncTerm A hA n m η) hidx)

theorem levelInc_eq_sup' (A : ℝ) (hA : 0 ≤ A) (n m : ℕ) (η : Site 2 → ℝ) :
    levelInc A hA n m η = (levelPairs m).sup' (levelPairs_nonempty m)
      (levelIncTerm A hA n m η) := rfl

/-- **`Yfield`'s dyadic increment bound holds trivially, by construction of `levelInc`.** -/
theorem dyadicIncBoundPi_Yfield (A : ℝ) (hA : 0 ≤ A) (n : ℕ) (η : Site 2 → ℝ) :
    LatticeProb.DyadicIncBoundPi (Yfield A hA n η) (fun m => levelInc A hA n m η) 0 := by
  intro m _ j hj i
  have hmem : (j, i) ∈ levelPairs m := by
    rw [levelPairs, Finset.mem_product]
    refine ⟨?_, Finset.mem_univ i⟩
    exact LatticeProb.mem_boxIdx_iff (m + 1) m j |>.mpr hj
  have hle := Finset.le_sup' (levelIncTerm A hA n m η) hmem
  show |Yfield A hA n η (LatticeProb.gridPt m (j + Pi.single i 1)) -
      Yfield A hA n η (LatticeProb.gridPt m j)| ≤ levelInc A hA n m η
  rw [levelInc_eq_sup']
  exact hle

/-! ### The moment of `levelInc`, uniform in `n` -/

/-- **The real distance between dyadic-adjacent grid points at level `m`.** -/
theorem dist_gridPt_step (m : ℕ) (j : Fin 2 → ℤ) (i : Fin 2) :
    dist (LatticeProb.gridPt m (j + Pi.single i 1)) (LatticeProb.gridPt m j) = 1 / 2 ^ m := by
  have h := LatticeProb.edist_gridPt_step m j i
  rw [edist_dist] at h
  have h2 := congrArg ENNReal.toReal h
  rwa [ENNReal.toReal_ofReal dist_nonneg, ENNReal.toReal_ofReal (by positivity)] at h2

theorem card_levelPairs_le (m : ℕ) :
    ((levelPairs m).card : ℝ) ≤ 2 * (3 ^ 2 * ((m : ℝ) + 1) ^ 2 * (2 ^ 2) ^ m) := by
  unfold levelPairs
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  push_cast
  have hb := LatticeProb.card_boxIdx_level_le 2 m
  calc (((LatticeProb.boxIdx (m + 1) m).card : ℝ) * 2)
      ≤ (3 ^ 2 * ((m : ℝ) + 1) ^ 2 * (2 ^ 2) ^ m) * 2 := by
        exact mul_le_mul_of_nonneg_right hb (by norm_num)
    _ = 2 * (3 ^ 2 * ((m : ℝ) + 1) ^ 2 * (2 ^ 2) ^ m) := by ring

/-- **`(max)^p ≤ Σ (term)^p`**: the `p`-th power of the actual maximum increment is bounded by
the sum of the `p`-th powers of every increment in the level-`m` index set. -/
theorem levelInc_rpow_le_sum (A : ℝ) (hA : 0 ≤ A) (n m : ℕ) (p : ℝ) (η : Site 2 → ℝ) :
    (levelInc A hA n m η) ^ p ≤
      ∑ idx ∈ levelPairs m, (levelIncTerm A hA n m η idx) ^ p := by
  obtain ⟨idx, hidx, heq⟩ :=
    Finset.exists_mem_eq_sup' (levelPairs_nonempty m) (levelIncTerm A hA n m η)
  rw [levelInc_eq_sup', heq]
  exact Finset.single_le_sum
    (fun idx _ => Real.rpow_nonneg (levelIncTerm_nonneg A hA n m η idx) p) hidx

/-- **The `p`-th moment of `levelInc` at level `m`, bounded uniformly in `n`.** -/
theorem exists_levelInc_moment (ν : Measure ℤ) (hν : CriticalLaw ν) (p : ℝ) (hp8 : 8 < p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ℝ) (hA : 0 ≤ A), ∃ M : ℝ, 0 ≤ M ∧ M ≤ K * (1 + A) ^ (p / 2) ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ m : ℕ,
      Integrable (fun η : Site 2 → ℝ => (levelInc A hA n m η) ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, (levelInc A hA n m η) ^ p ∂(iidLaw 2 (realLaw ν))) ≤
        M * (2 * (3 ^ 2 * ((m : ℝ) + 1) ^ 2 * (2 ^ 2) ^ m)) * ((1 : ℝ) / 2 ^ m) ^ (p / 4) := by
  have hp2 : (2 : ℝ) ≤ p := by linarith
  obtain ⟨K, hKnn, hKall⟩ := exists_Yfield_kolmogorov ν hν p hp2
  refine ⟨K, hKnn, fun A hA => ?_⟩
  obtain ⟨M0, hM0, hM0bd, hb⟩ := hKall A hA
  have hM0dist : 0 ≤ M0 * ((1 : ℝ) / 2 ^ 0) ^ (p / 4) := by positivity
  refine ⟨M0, hM0, hM0bd, fun n hn m => ?_⟩
  have hterm : ∀ idx ∈ levelPairs m,
      Integrable (fun η : Site 2 → ℝ => (levelIncTerm A hA n m η idx) ^ p)
        (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, (levelIncTerm A hA n m η idx) ^ p ∂(iidLaw 2 (realLaw ν))) ≤
        M0 * ((1 : ℝ) / 2 ^ m) ^ (p / 4) := by
    rintro ⟨j, i⟩ -
    unfold levelIncTerm
    have hd := dist_gridPt_step m j i
    obtain ⟨hint, hbound⟩ := hb n hn (LatticeProb.gridPt m (j + Pi.single i 1))
      (LatticeProb.gridPt m j)
    rw [hd] at hbound
    exact ⟨hint, hbound⟩
  have hintSum : Integrable (fun η : Site 2 → ℝ =>
      ∑ idx ∈ levelPairs m, (levelIncTerm A hA n m η idx) ^ p) (iidLaw 2 (realLaw ν)) :=
    integrable_finsetSum (levelPairs m) fun idx hidx => (hterm idx hidx).1
  have hmeasLevelInc : Measurable (fun η : Site 2 → ℝ => levelInc A hA n m η) := by
    have heq : (fun η : Site 2 → ℝ => levelInc A hA n m η) =
        (levelPairs m).sup' (levelPairs_nonempty m)
          (fun idx (η : Site 2 → ℝ) => levelIncTerm A hA n m η idx) := by
      funext η
      rw [levelInc_eq_sup', Finset.sup'_apply]
    rw [heq]
    apply Finset.measurable_sup'
    intro idx _
    exact ((measurable_Yfield hA n
      (LatticeProb.gridPt m (idx.1 + Pi.single idx.2 1))).sub
      (measurable_Yfield hA n (LatticeProb.gridPt m idx.1))).abs
  have hmeasPow : Measurable (fun η : Site 2 → ℝ => (levelInc A hA n m η) ^ p) := by
    have heq : (fun η : Site 2 → ℝ => (levelInc A hA n m η) ^ p) =
        (fun η : Site 2 → ℝ => |levelInc A hA n m η| ^ p) := by
      funext η
      rw [abs_of_nonneg (levelInc_nonneg A hA n m η)]
    rw [heq]
    exact LatticeProb.measurable_abs_rpow hmeasLevelInc p
  have hintPow : Integrable (fun η : Site 2 → ℝ => (levelInc A hA n m η) ^ p)
      (iidLaw 2 (realLaw ν)) := by
    refine hintSum.mono' ?_ ?_
    · exact hmeasPow.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun η => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg
        (Real.rpow_nonneg (levelInc_nonneg A hA n m η) p)]
      exact levelInc_rpow_le_sum A hA n m p η
  refine ⟨hintPow, ?_⟩
  calc (∫ η : Site 2 → ℝ, (levelInc A hA n m η) ^ p ∂(iidLaw 2 (realLaw ν)))
      ≤ ∫ η : Site 2 → ℝ, ∑ idx ∈ levelPairs m, (levelIncTerm A hA n m η idx) ^ p
          ∂(iidLaw 2 (realLaw ν)) :=
        integral_mono_ae hintPow hintSum
          (Filter.Eventually.of_forall fun η => levelInc_rpow_le_sum A hA n m p η)
    _ = ∑ idx ∈ levelPairs m, ∫ η : Site 2 → ℝ, (levelIncTerm A hA n m η idx) ^ p
          ∂(iidLaw 2 (realLaw ν)) :=
        integral_finsetSum (levelPairs m) fun idx hidx => (hterm idx hidx).1
    _ ≤ ∑ _idx ∈ levelPairs m, M0 * ((1 : ℝ) / 2 ^ m) ^ (p / 4) :=
        Finset.sum_le_sum fun idx hidx => (hterm idx hidx).2
    _ = ((levelPairs m).card : ℝ) * (M0 * ((1 : ℝ) / 2 ^ m) ^ (p / 4)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (3 ^ 2 * ((m : ℝ) + 1) ^ 2 * (2 ^ 2) ^ m)) * (M0 * ((1 : ℝ) / 2 ^ m) ^ (p / 4)) := by
        exact mul_le_mul_of_nonneg_right (card_levelPairs_le m)
          (by positivity)
    _ = M0 * (2 * (3 ^ 2 * ((m : ℝ) + 1) ^ 2 * (2 ^ 2) ^ m)) * ((1 : ℝ) / 2 ^ m) ^ (p / 4) := by
        ring

end Parking

end
