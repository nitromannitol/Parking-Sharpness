/-
The law of the rescaled oriented box-reward field on `C(K)`
(`parking.tex:3192-3203`).

The rescaled reward `G_n(u) = hatInterp V_n (n·u₀, √n·u₁ + n·u₀/2)` of
`Parking.Support.TightKolmogorov` is, for each scenery, a continuous function
of `u` on the box `K = [0,T] × [-2A,2A]`, and as the scenery varies it reads
only the finitely many grid values of `V_n` at the corners of the cells that
the box can touch.  This module packages that reading as a `C(K)`-valued map
of the scenery and takes its law:

- `Parking.boxToFin` reads a point of the box as a point of the plane; it is
  continuous and lands in `Parking.orientedBox`;
- `Parking.boxRewardMap` is the field `η ↦ G_n` as a `C(K)`-valued map.  Its
  measurability (`Parking.measurable_boxRewardMap`) is proved through the
  factorization `η ↦ V_n ↦ G_n`: the grid-value map into `ℤ → ℤ → ℝ` is
  measurable coordinate by coordinate, and the assembly
  `Parking.boxFieldAssemble` of the corner values into the hat interpolation
  is continuous, because the uncurried map is a fixed finite sum of products
  of evaluations and hat weights;
- `Parking.boxRewardLaw` is the law of the field: the pushforward of the
  i.i.d. scenery law along the box-reward map, a probability measure on
  `C(rewardBox T A, ℝ)`.
-/
import Parking.Support.TightKolmogorov
import Parking.Support.OrientedCutoffValue
import Parking.Support.CriticalLawReal

open MeasureTheory LatticeProb

noncomputable section

namespace Parking

/-- The measurable space on the continuous rewards on the box: the Borel
σ-algebra of the compact-open (uniform) topology. -/
local instance (T A : ℝ) : MeasurableSpace C(rewardBox T A, ℝ) := borel _

/-- The measurable space on the rewards is the Borel one. -/
local instance (T A : ℝ) : BorelSpace C(rewardBox T A, ℝ) := ⟨rfl⟩

/-- The point of the plane attached to a point of the box. -/
def boxToFin (T A : ℝ) : rewardBox T A → Fin 2 → ℝ := fun p => ![p.1.1, p.2.1]

/-- **The reading is continuous.** -/
theorem continuous_boxToFin (T A : ℝ) : Continuous (boxToFin T A) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · show Continuous fun p : rewardBox T A => (p.1 : ℝ)
    exact continuous_subtype_val.comp continuous_fst
  · show Continuous fun p : rewardBox T A => (p.2 : ℝ)
    exact continuous_subtype_val.comp continuous_snd

/-- **The reading lands in the oriented box.** -/
theorem boxToFin_mem_orientedBox (T : ℝ) (_hT : 0 ≤ T) (A : ℝ) (_hA : 0 ≤ A)
    (p : rewardBox T A) : boxToFin T A p ∈ orientedBox T A := by
  obtain ⟨hp1lo, hp1hi⟩ := Set.mem_Icc.mp p.1.2
  obtain ⟨hp2lo, hp2hi⟩ := Set.mem_Icc.mp p.2.2
  rw [orientedBox]
  refine Set.mem_Icc.mpr ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i
  · show (0 : ℝ) ≤ p.1.1
    exact hp1lo
  · show -(2 * A) ≤ p.2.1
    exact hp2lo
  · show p.1.1 ≤ T
    exact hp1hi
  · show p.2.1 ≤ 2 * A
    exact hp2hi

/-- The rescaled box-reward field at scale `n`, as a continuous function of the
box point. -/
def boxRewardMap (T : ℝ) (_hT : 0 ≤ T) (A : ℝ) (_hA : 0 ≤ A) (n : ℕ) (η : Site 2 → ℝ) :
    C(rewardBox T A, ℝ) :=
  ⟨fun p => orientedBoxReward T n η (boxToFin T A p),
    (continuous_orientedBoxReward T n η).comp (continuous_boxToFin T A)⟩

/-- The time coordinates of the grid cells that the hat interpolation over the
box can read: at `u₀ ∈ [0, T]` the hat weights in the first coordinate vanish
outside `{⌊n·u₀⌋, ⌊n·u₀⌋ + 1}`, and `0 ≤ n·u₀ ≤ n·T`. -/
def boxCornerM (T : ℝ) (n : ℕ) : Finset ℤ := Finset.Icc 0 (⌊(n : ℝ) * T⌋ + 1)

/-- The space coordinates of the grid cells that the hat interpolation over the
box can read: at `(u₀, u₁)` in the box the hat weights in the second coordinate
vanish outside `{⌊ũ₂⌋, ⌊ũ₂⌋ + 1}` for `ũ₂ = √n·u₁ + n·u₀/2`, and
`-2A·√n ≤ ũ₂ ≤ 2A·√n + n·T/2`. -/
def boxCornerJ (T A : ℝ) (n : ℕ) : Finset ℤ :=
  Finset.Icc ⌊-(2 * A) * Real.sqrt (n : ℝ)⌋
    (⌊Real.sqrt (n : ℝ) * (2 * A) + (n : ℝ) * T / 2⌋ + 1)

/-- **The hat support in time over the box is inside `Parking.boxCornerM`.** -/
theorem hat1_ne_zero_mem_boxCornerM (T A : ℝ) (_hT : 0 ≤ T) (n : ℕ) (p : rewardBox T A)
    {m : ℤ} (hm : hat1 ((n : ℝ) * boxToFin T A p 0 - (m : ℝ)) ≠ 0) :
    m ∈ boxCornerM T n := by
  obtain ⟨hlo, hhi⟩ := Set.mem_Icc.mp p.1.2
  have hu : boxToFin T A p 0 = p.1.1 := rfl
  have hb1 : (0 : ℝ) ≤ (n : ℝ) * boxToFin T A p 0 := by
    rw [hu]
    exact mul_nonneg (Nat.cast_nonneg n) hlo
  have hb2 : (n : ℝ) * boxToFin T A p 0 ≤ (n : ℝ) * T := by
    rw [hu]
    exact mul_le_mul_of_nonneg_left hhi (Nat.cast_nonneg n)
  obtain h | h := hat1_ne_zero_mem_floor_pair hm
  · rw [boxCornerM, Finset.mem_Icc, h]
    have h1 := Int.floor_nonneg.mpr hb1
    have h2 := Int.floor_mono hb2
    omega
  · rw [boxCornerM, Finset.mem_Icc, h]
    have h1 := Int.floor_nonneg.mpr hb1
    have h2 := Int.floor_mono hb2
    omega

/-- **The hat support in space over the box is inside `Parking.boxCornerJ`.** -/
theorem hat1_ne_zero_mem_boxCornerJ (T : ℝ) (_hT : 0 ≤ T) (A : ℝ) (_hA : 0 ≤ A) (n : ℕ)
    (p : rewardBox T A) {j : ℤ}
    (hj : hat1 (Real.sqrt (n : ℝ) * boxToFin T A p 1 + (n : ℝ) * boxToFin T A p 0 / 2 -
        (j : ℝ)) ≠ 0) : j ∈ boxCornerJ T A n := by
  obtain ⟨h1lo, h1hi⟩ := Set.mem_Icc.mp p.1.2
  obtain ⟨h2lo, h2hi⟩ := Set.mem_Icc.mp p.2.2
  have hu0 : boxToFin T A p 0 = p.1.1 := rfl
  have hu1 : boxToFin T A p 1 = p.2.1 := rfl
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsn : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hlo : -(2 * A) * Real.sqrt (n : ℝ) ≤
      Real.sqrt (n : ℝ) * boxToFin T A p 1 + (n : ℝ) * boxToFin T A p 0 / 2 := by
    have hA1 : Real.sqrt (n : ℝ) * (-(2 * A)) ≤ Real.sqrt (n : ℝ) * boxToFin T A p 1 := by
      rw [hu1]
      exact mul_le_mul_of_nonneg_left h2lo hsn
    have hB1 : (0 : ℝ) ≤ (n : ℝ) * boxToFin T A p 0 / 2 := by
      rw [hu0]
      exact div_nonneg (mul_nonneg hnn h1lo) (by norm_num)
    calc -(2 * A) * Real.sqrt (n : ℝ) = Real.sqrt (n : ℝ) * (-(2 * A)) := by ring
      _ ≤ Real.sqrt (n : ℝ) * boxToFin T A p 1 + (n : ℝ) * boxToFin T A p 0 / 2 :=
          le_trans hA1 (le_add_of_nonneg_right hB1)
  have hhi : Real.sqrt (n : ℝ) * boxToFin T A p 1 + (n : ℝ) * boxToFin T A p 0 / 2 ≤
      Real.sqrt (n : ℝ) * (2 * A) + (n : ℝ) * T / 2 := by
    have hA2 : Real.sqrt (n : ℝ) * boxToFin T A p 1 ≤ Real.sqrt (n : ℝ) * (2 * A) := by
      rw [hu1]
      exact mul_le_mul_of_nonneg_left h2hi hsn
    have hB2 : (n : ℝ) * boxToFin T A p 0 / 2 ≤ (n : ℝ) * T / 2 := by
      rw [hu0]
      have hmul := mul_le_mul_of_nonneg_left h1hi hnn
      linarith
    exact add_le_add hA2 hB2
  obtain h | h := hat1_ne_zero_mem_floor_pair hj
  · rw [boxCornerJ, Finset.mem_Icc, h]
    have h1 := Int.floor_mono hlo
    have h2 := Int.floor_mono hhi
    omega
  · rw [boxCornerJ, Finset.mem_Icc, h]
    have h1 := Int.floor_mono hlo
    have h2 := Int.floor_mono hhi
    omega

/-- The continuous field on the box assembled from a table of grid values: the
hat interpolation, written as the fixed finite sum over the corner sets. -/
noncomputable def boxFieldAssemble (T : ℝ) (_hT : 0 ≤ T) (A : ℝ) (_hA : 0 ≤ A) (n : ℕ)
    (V : ℤ → ℤ → ℝ) : C(rewardBox T A, ℝ) :=
  ⟨fun p => ∑ m ∈ boxCornerM T n, ∑ j ∈ boxCornerJ T A n,
      V m j * (hat1 ((n : ℝ) * boxToFin T A p 0 - (m : ℝ)) *
        hat1 (Real.sqrt (n : ℝ) * boxToFin T A p 1 + (n : ℝ) * boxToFin T A p 0 / 2 -
          (j : ℝ))), by
    have h0 : Continuous fun p : rewardBox T A => boxToFin T A p 0 :=
      (continuous_apply 0).comp (continuous_boxToFin T A)
    have h1 : Continuous fun p : rewardBox T A => boxToFin T A p 1 :=
      (continuous_apply 1).comp (continuous_boxToFin T A)
    apply continuous_finsetSum
    intro m _
    apply continuous_finsetSum
    intro j _
    exact continuous_const.mul
      ((continuous_hat1.comp ((continuous_const.mul h0).sub continuous_const)).mul
        (continuous_hat1.comp (((continuous_const.mul h1).add
          ((continuous_const.mul h0).div_const 2)).sub continuous_const)))⟩

/-- **The assembly is continuous in the table of grid values**: the uncurried
map is a fixed finite sum of products of evaluations and hat weights. -/
theorem continuous_boxFieldAssemble (T : ℝ) (hT : 0 ≤ T) (A : ℝ) (hA : 0 ≤ A) (n : ℕ) :
    Continuous (boxFieldAssemble T hT A hA n) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  have hV : ∀ m j : ℤ, Continuous fun q : (ℤ → ℤ → ℝ) × rewardBox T A => q.1 m j :=
    fun m j => (continuous_apply j).comp ((continuous_apply m).comp continuous_fst)
  have hp0 : Continuous fun q : (ℤ → ℤ → ℝ) × rewardBox T A => boxToFin T A q.2 0 :=
    (continuous_apply 0).comp ((continuous_boxToFin T A).comp continuous_snd)
  have hp1 : Continuous fun q : (ℤ → ℤ → ℝ) × rewardBox T A => boxToFin T A q.2 1 :=
    (continuous_apply 1).comp ((continuous_boxToFin T A).comp continuous_snd)
  show Continuous fun q : (ℤ → ℤ → ℝ) × rewardBox T A =>
      ∑ m ∈ boxCornerM T n, ∑ j ∈ boxCornerJ T A n,
        q.1 m j * (hat1 ((n : ℝ) * boxToFin T A q.2 0 - (m : ℝ)) *
          hat1 (Real.sqrt (n : ℝ) * boxToFin T A q.2 1 + (n : ℝ) * boxToFin T A q.2 0 / 2 -
            (j : ℝ)))
  apply continuous_finsetSum
  intro m _
  apply continuous_finsetSum
  intro j _
  exact (hV m j).mul
    ((continuous_hat1.comp ((continuous_const.mul hp0).sub continuous_const)).mul
      (continuous_hat1.comp (((continuous_const.mul hp1).add
        ((continuous_const.mul hp0).div_const 2)).sub continuous_const)))

/-- **The box-reward map is the assembly of the grid reward.** -/
theorem boxRewardMap_eq_boxFieldAssemble (T : ℝ) (hT : 0 ≤ T) (A : ℝ) (hA : 0 ≤ A) (n : ℕ)
    (η : Site 2 → ℝ) :
    boxRewardMap T hT A hA n η =
      boxFieldAssemble T hT A hA n (orientedGridReward n ⌊(n : ℝ) * T⌋₊ η) := by
  ext p
  show orientedBoxReward T n η (boxToFin T A p) = _
  rw [orientedBoxReward]
  exact hatInterp_eq_sum _ _ _ _
    (fun m hm => hat1_ne_zero_mem_boxCornerM T A hT n p hm)
    (fun j hj => hat1_ne_zero_mem_boxCornerJ T hT A hA n p hj)

/-- **The box-reward map is measurable in the scenery**: it factors as the
grid-value map into the countable product, which is measurable coordinate by
coordinate, followed by the continuous assembly. -/
theorem measurable_boxRewardMap (T : ℝ) (hT : 0 ≤ T) (A : ℝ) (hA : 0 ≤ A) (n : ℕ) :
    Measurable (boxRewardMap T hT A hA n) := by
  have hfact : boxRewardMap T hT A hA n = fun η : Site 2 → ℝ =>
      boxFieldAssemble T hT A hA n (orientedGridReward n ⌊(n : ℝ) * T⌋₊ η) :=
    funext fun η => boxRewardMap_eq_boxFieldAssemble T hT A hA n η
  rw [hfact]
  exact (continuous_boxFieldAssemble T hT A hA n).measurable.comp
    (measurable_pi_lambda _ fun m => measurable_pi_lambda _ fun j =>
      measurable_orientedGridReward n ⌊(n : ℝ) * T⌋₊ m j)

/-- The law of the rescaled box-reward field at scale `n`: the pushforward of
the i.i.d. scenery law along `Parking.boxRewardMap`. -/
noncomputable def boxRewardLaw (T : ℝ) (ν : Measure ℤ) (hT : 0 ≤ T) (A : ℝ) (hA : 0 ≤ A)
    (n : ℕ) : Measure C(rewardBox T A, ℝ) :=
  (iidLaw 2 (realLaw ν)).map (boxRewardMap T hT A hA n)

/-- **The field law is a probability measure.** -/
instance (T : ℝ) (ν : Measure ℤ) [IsProbabilityMeasure ν] (hT : 0 ≤ T) (A : ℝ) (hA : 0 ≤ A)
    (n : ℕ) : IsProbabilityMeasure (boxRewardLaw T ν hT A hA n) := by
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI : IsProbabilityMeasure (iidLaw 2 (realLaw ν)) := by unfold iidLaw; infer_instance
  show IsProbabilityMeasure ((iidLaw 2 (realLaw ν)).map (boxRewardMap T hT A hA n))
  exact Measure.isProbabilityMeasure_map (measurable_boxRewardMap T hT A hA n).aemeasurable

end Parking

end
