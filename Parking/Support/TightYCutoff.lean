/-
`Y`, `hY` and `hYi` of `Parking.oriented_scaling_of_cutoff`: the cutoff optimal-stopping value
of `parking.tex:3199-3203` TOGETHER WITH the potential at the origin, read at the discrete
rescaled box-reward field, as a function of the driving data `w : Data 2`.

`Parking.Y A n w := Parking.orientedCutoffValuePot h1 hA n (Parking.boxRewardMap 1 h1 A hA n
(Parking.confReal w))`, i.e. the value of the truncated (cutoff level `A`) optimal-stopping
problem PLUS the box-reward field's own value at the origin, read at the rescaled reward field
built from `w`'s own scenery.  The extra term matches `Parking.uOriented_eq_potential_add_
stoppingSup`'s own decomposition `u⃗_n(x) = Φ_n(x) + sup_σ E_x[-Φ_{n-σ}(X_σ)]`: without it,
`n^{-1/4}u⃗_n(0) - Y A n w` would carry the fixed, non-vanishing discrepancy `n^{-1/4}Φ_n(0)`
even for stopping rules that never leave the cutoff box, since `Parking.orientedCutoffValue`
alone reads only the stopping-sup term.  Its measurability (`Parking.measurable_Y`) is an
immediate composition: `Parking.confReal` and `Parking.boxRewardMap` are measurable, and
`Parking.orientedCutoffValuePot hT hA n` is `2`-Lipschitz in the reward
(`Parking.abs_orientedCutoffValuePot_sub_le`), hence continuous, hence measurable.  Its
integrability (`Parking.integrable_Y`) follows from the SAME Lipschitz bound, read against the
zero reward: `|Y A n w| ≤ 2‖G_n w‖`, and the box-reward field's sup norm is bounded, corner by
corner, by the finite sum of the absolute grid rewards touching the box
(`Parking.norm_boxRewardMap_le`, from the hat-partition-of-unity bound `hat1_nonneg`/
`hat1_le_one`), each of which is square-integrable
(`Parking.exists_orientedGridReward_single_moment` at `p := 2`) and hence integrable on the
probability space (`Parking.integrable_of_integrable_sq`, via `|x| ≤ 1 + x²`).
-/
import Parking.Support.TightBoxLaw
import Parking.Support.OrientedCutoffValuePot
import Parking.Support.OrientedLaw

open MeasureTheory LatticeProb Filter Topology

noncomputable section

namespace Parking

local instance instMeasurableSpaceRewardBoxTightYCutoff (T A : ℝ) :
    MeasurableSpace C(rewardBox T A, ℝ) := borel _
local instance instBorelSpaceRewardBoxTightYCutoff (T A : ℝ) :
    BorelSpace C(rewardBox T A, ℝ) := ⟨rfl⟩

/-! ### `Parking.orientedCutoffValue` is measurable and bounded by the norm of the reward -/

/-- **`Parking.orientedCutoffValue hT hA n` is measurable in the reward.** -/
theorem measurable_orientedCutoffValue {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (n : ℕ) :
    Measurable (fun G : C(rewardBox T A, ℝ) => orientedCutoffValue hT hA n G) := by
  refine (LipschitzWith.continuous (K := 1) ?_).measurable
  intro G H
  rw [edist_dist, edist_dist]
  have h := abs_orientedCutoffValue_sub_le hT hA n G H
  rw [Real.dist_eq]
  simp only [ENNReal.coe_one, one_mul]
  exact ENNReal.ofReal_le_ofReal h

/-- **The value is bounded by the norm of the reward.** -/
theorem abs_orientedCutoffValue_le {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (n : ℕ)
    (G : C(rewardBox T A, ℝ)) : |orientedCutoffValue hT hA n G| ≤ ‖G‖ := by
  have h := abs_orientedCutoffValue_sub_le hT hA n G 0
  rwa [orientedCutoffValue_zero, sub_zero, dist_zero_right] at h

/-! ### The sup norm of the discrete box-reward field is bounded by the corner sum -/

/-- **The box-reward field's sup norm is bounded by the sum of the absolute grid rewards at
every corner the box can touch.** -/
theorem norm_boxRewardMap_le (T : ℝ) (hT : 0 ≤ T) (A : ℝ) (hA : 0 ≤ A) (n : ℕ)
    (η : Site 2 → ℝ) :
    ‖boxRewardMap T hT A hA n η‖ ≤
      ∑ m ∈ boxCornerM T n, ∑ j ∈ boxCornerJ T A n,
        |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η m j| := by
  set S : ℝ := ∑ m ∈ boxCornerM T n, ∑ j ∈ boxCornerJ T A n,
      |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η m j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ContinuousMap.norm_le _ hS0 |>.2 fun p => ?_
  show |boxRewardMap T hT A hA n η p| ≤ S
  rw [boxRewardMap_eq_boxFieldAssemble T hT A hA n η]
  show |∑ m ∈ boxCornerM T n, ∑ j ∈ boxCornerJ T A n,
      orientedGridReward n ⌊(n : ℝ) * T⌋₊ η m j *
        (hat1 ((n : ℝ) * boxToFin T A p 0 - (m : ℝ)) *
          hat1 (Real.sqrt n * boxToFin T A p 1 + (n : ℝ) * boxToFin T A p 0 / 2 - (j : ℝ)))| ≤ S
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun m _ => ?_)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  have hw1 : |hat1 ((n : ℝ) * boxToFin T A p 0 - (m : ℝ))| ≤ 1 := by
    rw [abs_of_nonneg (hat1_nonneg _)]; exact hat1_le_one _
  have hw2 : |hat1 (Real.sqrt n * boxToFin T A p 1 + (n : ℝ) * boxToFin T A p 0 / 2 - (j : ℝ))|
      ≤ 1 := by rw [abs_of_nonneg (hat1_nonneg _)]; exact hat1_le_one _
  have hwprod : |hat1 ((n : ℝ) * boxToFin T A p 0 - (m : ℝ)) *
      hat1 (Real.sqrt n * boxToFin T A p 1 + (n : ℝ) * boxToFin T A p 0 / 2 - (j : ℝ))| ≤ 1 := by
    rw [abs_mul]
    calc |hat1 ((n : ℝ) * boxToFin T A p 0 - (m : ℝ))| *
        |hat1 (Real.sqrt n * boxToFin T A p 1 + (n : ℝ) * boxToFin T A p 0 / 2 - (j : ℝ))|
        ≤ 1 * 1 := mul_le_mul hw1 hw2 (abs_nonneg _) (by norm_num)
      _ = 1 := mul_one 1
  calc |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η m j| *
      |hat1 ((n : ℝ) * boxToFin T A p 0 - (m : ℝ)) *
        hat1 (Real.sqrt n * boxToFin T A p 1 + (n : ℝ) * boxToFin T A p 0 / 2 - (j : ℝ))|
      ≤ |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η m j| * 1 :=
        mul_le_mul_of_nonneg_left hwprod (abs_nonneg _)
    _ = |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η m j| := mul_one _

/-! ### The corner sum is integrable -/

/-- `|x| ≤ 1 + x²` for every real `x`. -/
theorem abs_le_one_add_sq (x : ℝ) : |x| ≤ 1 + x ^ 2 := by
  nlinarith [sq_nonneg (|x| - 1), sq_abs x]

/-- **A measurable function whose square is integrable on a probability measure is itself
integrable.** -/
theorem integrable_of_integrable_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    (hsq : Integrable (fun ω => (f ω) ^ 2) μ) : Integrable f μ :=
  Integrable.mono' ((integrable_const 1).add hsq) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; simpa using abs_le_one_add_sq (f ω))

/-- **Each grid reward is integrable**, at any grid indices. -/
theorem integrable_orientedGridReward (ν : Measure ℤ) (hν : CriticalLaw ν) (n N : ℕ) (m j : ℤ) :
    Integrable (fun η : Site 2 → ℝ => orientedGridReward n N η m j) (iidLaw 2 (realLaw ν)) := by
  haveI : IsProbabilityMeasure ν := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI : IsProbabilityMeasure (iidLaw 2 (realLaw ν)) := by unfold iidLaw; infer_instance
  obtain ⟨C, _hC, hb⟩ := exists_orientedGridReward_single_moment ν hν 2 (by norm_num)
  have hsq : Integrable (fun η : Site 2 → ℝ => |orientedGridReward n N η m j| ^ (2 : ℝ))
      (iidLaw 2 (realLaw ν)) := (hb n N m j).1
  have hconv : (fun η : Site 2 → ℝ => |orientedGridReward n N η m j| ^ (2 : ℝ))
      = fun η => (orientedGridReward n N η m j) ^ 2 := by
    funext η
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [hconv] at hsq
  exact integrable_of_integrable_sq (measurable_orientedGridReward n N m j) hsq

/-- **The corner sum is integrable.** -/
theorem integrable_boxCornerSum (ν : Measure ℤ) (hν : CriticalLaw ν) (T : ℝ) (_hT : 0 ≤ T)
    (A : ℝ) (_hA : 0 ≤ A) (n : ℕ) :
    Integrable (fun η : Site 2 → ℝ => ∑ m ∈ boxCornerM T n, ∑ j ∈ boxCornerJ T A n,
        |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η m j|) (iidLaw 2 (realLaw ν)) := by
  haveI : IsProbabilityMeasure ν := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI : IsProbabilityMeasure (iidLaw 2 (realLaw ν)) := by unfold iidLaw; infer_instance
  refine integrable_finsetSum (boxCornerM T n) fun m _ => ?_
  refine integrable_finsetSum (boxCornerJ T A n) fun j _ => ?_
  exact (integrable_orientedGridReward ν hν n ⌊(n : ℝ) * T⌋₊ m j).abs

/-- **The discrete box-reward field's sup norm is integrable.** -/
theorem integrable_norm_boxRewardMap (ν : Measure ℤ) (hν : CriticalLaw ν) (T : ℝ) (hT : 0 ≤ T)
    (A : ℝ) (hA : 0 ≤ A) (n : ℕ) :
    Integrable (fun η : Site 2 → ℝ => ‖boxRewardMap T hT A hA n η‖) (iidLaw 2 (realLaw ν)) := by
  have hnn : ∀ η : Site 2 → ℝ, 0 ≤ ‖boxRewardMap T hT A hA n η‖ := fun η => norm_nonneg _
  refine Integrable.mono' (integrable_boxCornerSum ν hν T hT A hA n)
    (measurable_boxRewardMap T hT A hA n).norm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun η => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn η)]
  exact norm_boxRewardMap_le T hT A hA n η

/-! ### `Y`, `hY` and `hYi` -/

/-- **`Y`**: the cutoff optimal-stopping value of `parking.tex:3199-3203` TOGETHER WITH the
potential at the origin, at horizon `1`, cutoff level `A` and scale `n`, read at the driving
data `w` through its own scenery (`Parking.confReal`) and the discrete rescaled box-reward
field (`Parking.boxRewardMap`). -/
def Y (A n : ℕ) (w : Data 2) : ℝ :=
  orientedCutoffValuePot (T := 1) zero_le_one (Nat.cast_nonneg A) n
    (boxRewardMap 1 zero_le_one (A : ℝ) (Nat.cast_nonneg A) n (confReal w))

/-- **`hY`**: `Y A n` is measurable, as the composition of the measurable scenery map
`Parking.confReal`, the measurable field map `Parking.boxRewardMap`, and the measurable
(`2`-Lipschitz) value map `Parking.orientedCutoffValuePot`. -/
theorem measurable_Y (A n : ℕ) : Measurable (Y A n) :=
  (measurable_orientedCutoffValuePot zero_le_one (Nat.cast_nonneg A) n).comp
    ((measurable_boxRewardMap 1 zero_le_one (A : ℝ) (Nat.cast_nonneg A) n).comp measurable_confReal)

/-- **`hYi`**: `Y A n` is integrable under the oriented law, dominated by twice the sup norm of
the rescaled box-reward field of its own scenery. -/
theorem integrable_Y (ν : Measure ℤ) (hν : CriticalLaw ν) (A n : ℕ) :
    Integrable (Y A n) (orientedLaw 2 ν) := by
  haveI : IsProbabilityMeasure ν := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI : IsProbabilityMeasure (iidLaw 2 (realLaw ν)) := by unfold iidLaw; infer_instance
  set g : (Site 2 → ℝ) → ℝ := fun η =>
      orientedCutoffValuePot (T := 1) zero_le_one (Nat.cast_nonneg A) n
        (boxRewardMap 1 zero_le_one (A : ℝ) (Nat.cast_nonneg A) n η) with hgdef
  have hYeq : Y A n = g ∘ confReal := rfl
  have hgi : Integrable g (iidLaw 2 (realLaw ν)) := by
    refine Integrable.mono' ((integrable_norm_boxRewardMap ν hν 1 zero_le_one (A : ℝ)
      (Nat.cast_nonneg A) n).const_mul 2)
      ((measurable_orientedCutoffValuePot zero_le_one (Nat.cast_nonneg A) n).comp
        (measurable_boxRewardMap 1 zero_le_one (A : ℝ) (Nat.cast_nonneg A) n)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun η => ?_)
    rw [Real.norm_eq_abs]
    exact abs_orientedCutoffValuePot_le zero_le_one (Nat.cast_nonneg A) n
      (boxRewardMap 1 zero_le_one (A : ℝ) (Nat.cast_nonneg A) n η)
  rw [hYeq]
  have hgi' : Integrable g (Measure.map confReal (orientedLaw 2 ν)) := by
    rw [orientedLaw_map_confReal (d := 2) (by norm_num) ν]; exact hgi
  exact hgi'.comp_measurable measurable_confReal

end Parking

end
