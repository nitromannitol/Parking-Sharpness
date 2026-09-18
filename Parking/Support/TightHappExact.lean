/-
The hat-interpolation-at-grid-points exactness of `Parking.oriented_scaling_of_cutoff`'s
`happ` hypothesis, and the walk-position/box-membership correspondence it needs.

`Parking.hatInterp_at_int` already gives the interpolation the exact grid value at an
integer point; this module identifies the box-reward field's own grid point reached by
the oriented walk at time `k`, `((k:ℝ)/n, orientedScaledSite n z)`, and shows that when
the walk's position `z` at time `k` lies inside the cutoff box (`|orientedScaledSite n z|
≤ 2A`), the box-clamp is trivial and the interpolation collapses to the EXACT grid reward
`Parking.orientedGridReward n n η k (-z 0)` — no clamping error at all.  The box membership
condition is then identified, via `Parking.orientedScaledSite`'s definition and
`Parking.walkPartialSum_eq_orientedPath_coord_sub`, with the EXACT threshold
`|Parking.walkPartialSum k p| ≤ 4A√n` of `Parking.measureReal_sup_walkPartialSum_sq_le`
(`TightWalkMaximal.lean`): the two rewards of `parking.tex:3199-3203` differ only on the
event that the rescaled walk's coordinate-difference partial sum exits `[-4A√n, 4A√n]`
before time `n`.
-/
import Parking.Support.TightWalkMaximal
import Parking.Support.TightBoxLaw
import Parking.Support.OrientedMaxMoment

open MeasureTheory LatticeProb Filter Topology

noncomputable section

namespace Parking

/-! ### The layer index of the walk's own position -/

/-- **The origin sits at layer `0`.** -/
theorem orientedLayerIndex_zero : orientedLayerIndex (0 : Site 2) = 0 := by
  simp [orientedLayerIndex]

/-- **The oriented walk started at the origin sits at layer `k` after `k` steps.** -/
theorem orientedLayerIndex_orientedPath_zero (p : ℕ → Fin 2 × Bool) (k : ℕ) :
    orientedLayerIndex (orientedPath (0 : Site 2) p k) = (k : ℤ) := by
  rw [orientedLayerIndex_orientedPath, orientedLayerIndex_zero, zero_add]

/-- **A site at layer `k` is the layer point of its own first coordinate.** -/
theorem eq_orientedLayerPoint_of_layerIndex {z : Site 2} {k : ℕ}
    (hz : orientedLayerIndex z = (k : ℤ)) : z = orientedLayerPoint k (-z 0) := by
  refine (orientedLayerPoint_eq ?_).symm
  rw [layerHeight_two]
  unfold orientedLayerIndex at hz
  omega

/-! ### The rescaled coordinate difference is the walk's own partial sum -/

/-- **`Parking.orientedScaledSite` at the walk's own position is `Parking.walkPartialSum`,
rescaled by `2√n`.** -/
theorem orientedScaledSite_orientedPath (n : ℕ) (p : ℕ → Fin 2 × Bool) (k : ℕ) :
    orientedScaledSite n (orientedPath (0 : Site 2) p k) =
      walkPartialSum k p / (2 * Real.sqrt n) := by
  rw [orientedScaledSite, walkPartialSum_eq_orientedPath_coord_sub]

/-- **Box membership of the walk's rescaled position at time `k` is exactly the maximal
tail event's threshold.** -/
theorem abs_orientedScaledSite_le_iff (n : ℕ) (hn : 1 ≤ n) (p : ℕ → Fin 2 × Bool) (k : ℕ)
    (A : ℝ) :
    |orientedScaledSite n (orientedPath (0 : Site 2) p k)| ≤ 2 * A ↔
      |walkPartialSum k p| ≤ 4 * A * Real.sqrt n := by
  rw [orientedScaledSite_orientedPath]
  have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.sqrt n),
    div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.sqrt n)]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-! ### The exactness of the box-clamped reward at the walk's own grid point -/

/-- **The box-reward field, read at the walk's own rescaled space-time point, is EXACTLY
the grid reward at `(k, -z 0)` whenever the walk's rescaled position lies inside the
cutoff box.** No hat-interpolation error at all: the clamp is trivial and the interpolation
collapses to a single grid value. -/
theorem rewardOfBox_boxRewardMap_eq_orientedGridReward {A : ℝ} (hA : 0 ≤ A) (n : ℕ)
    (hn : 1 ≤ n) (η : Site 2 → ℝ) (k : ℕ) (hk : k ≤ n) (z : Site 2)
    (hz : orientedLayerIndex z = (k : ℤ)) (hbox : |orientedScaledSite n z| ≤ 2 * A) :
    rewardOfBox (zero_le_one) hA (boxRewardMap 1 (zero_le_one) A hA n η)
        ((k : ℝ) / n) (orientedScaledSite n z) =
      orientedGridReward n n η (k : ℤ) (-z 0) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hs : ((k : ℝ) / n) ∈ Set.Icc (0 : ℝ) (1 : ℝ) := by
    constructor
    · positivity
    · rw [div_le_one hnR]; exact_mod_cast hk
  have hy : orientedScaledSite n z ∈ Set.Icc (-(2 * A)) (2 * A) := by
    rw [Set.mem_Icc, ← abs_le]; exact hbox
  show (boxRewardMap 1 (zero_le_one) A hA n η)
      (boxPoint (zero_le_one) hA ((k : ℝ) / n) (orientedScaledSite n z)) = _
  have hbp : boxPoint (zero_le_one) hA ((k : ℝ) / n) (orientedScaledSite n z) =
      (⟨(k : ℝ) / n, hs⟩, ⟨orientedScaledSite n z, hy⟩) := by
    unfold boxPoint
    rw [Set.projIcc_of_mem, Set.projIcc_of_mem]
  rw [hbp]
  show orientedBoxReward 1 n η (boxToFin 1 A (⟨(k : ℝ) / n, hs⟩, ⟨orientedScaledSite n z, hy⟩)) = _
  have hbtf : boxToFin 1 A (⟨(k : ℝ) / n, hs⟩, ⟨orientedScaledSite n z, hy⟩) =
      ![(k : ℝ) / n, orientedScaledSite n z] := by
    unfold boxToFin
    rfl
  rw [hbtf]
  show hatInterp (orientedGridReward n ⌊(n : ℝ) * 1⌋₊ η)
      ((n : ℝ) * ![(k : ℝ) / n, orientedScaledSite n z] 0,
        Real.sqrt n * ![(k : ℝ) / n, orientedScaledSite n z] 1 +
          (n : ℝ) * ![(k : ℝ) / n, orientedScaledSite n z] 0 / 2) = _
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hfl : ⌊(n : ℝ) * 1⌋₊ = n := by rw [mul_one, Nat.floor_natCast]
  rw [hfl]
  have hk1 : (n : ℝ) * ((k : ℝ) / n) = (k : ℝ) := by field_simp
  rw [hk1]
  have hz0z1 : z 0 + z 1 = -(k : ℤ) := by
    unfold orientedLayerIndex at hz; omega
  have hk2 : Real.sqrt n * orientedScaledSite n z + (k : ℝ) / 2 = -(z 0 : ℝ) := by
    rw [orientedScaledSite]
    have hsn : Real.sqrt (n : ℝ) ≠ 0 := by
      have : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnR
      exact this.ne'
    have hz1 : (z 1 : ℝ) = -(k : ℝ) - (z 0 : ℝ) := by
      have := hz0z1
      have hcast : ((z 1 : ℤ) : ℝ) = -((k : ℤ) : ℝ) - ((z 0 : ℤ) : ℝ) := by
        have : (z 1 : ℤ) = -(k : ℤ) - z 0 := by omega
        exact_mod_cast this
      simpa using hcast
    rw [hz1]
    field_simp
    ring
  rw [hk2]
  have hcast : ((-z 0 : ℤ) : ℝ) = -(z 0 : ℝ) := by push_cast; ring
  rw [← hcast]
  exact hatInterp_at_int (orientedGridReward n n η) (k : ℤ) (-z 0)

/-! ### The odometer-side reward is bounded by the walk's own maximal potential functional,
uniformly over every admissible stopping rule -/

/-- **The rescaled remaining-horizon grid reward, read at the walk's own position at time
`k`, is bounded by `n^{-1/4}` times the walk's own maximal potential functional
`Parking.orientedMax`.**  The bound is uniform over `k ≤ n` and hence over every admissible
bounded stopping rule: this is the ingredient `happ` needs for the ODOMETER side of the
Hölder bound, since `Parking.exists_uOriented_two_moment`/`Parking.exists_rescaled_uOriented_
eighth` control `Parking.orientedMax`'s own `L^r` moment (via `Parking.exists_orientedMax_
moment`, already used inside `exists_uOriented_two_moment`'s proof). -/
theorem abs_orientedGridReward_orientedPath_le (n : ℕ) (η : Site 2 → ℝ)
    (p : ℕ → Fin 2 × Bool) (k : ℕ) (hk : k ≤ n) :
    |orientedGridReward n n η (k : ℤ) (-(orientedPath (0 : Site 2) p k) 0)| ≤
      (n : ℝ) ^ (-(1 : ℝ) / 4) * orientedMax (orientedPotential η) n 0 p := by
  set z : Site 2 := orientedPath (0 : Site 2) p k with hzdef
  have hlayer : orientedLayerIndex z = (k : ℤ) := orientedLayerIndex_orientedPath_zero p k
  have hzeq : z = orientedLayerPoint k (-z 0) := eq_orientedLayerPoint_of_layerIndex hlayer
  have htoNat : ((k : ℤ)).toNat = k := Int.toNat_natCast k
  have hgrid : orientedGridReward n n η (k : ℤ) (-z 0) =
      -(n : ℝ) ^ (-(1 : ℝ) / 4) * orientedPotential η (n - k) z := by
    unfold orientedGridReward
    rw [htoNat, ← hzeq]
  rw [hgrid, abs_mul, abs_neg, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  rw [orientedMax_eq_sup]
  exact Finset.le_sup' (fun j => |orientedPotential η (n - j) (orientedPath (0 : Site 2) p j)|)
    (Finset.mem_range.mpr (by omega))

end Parking

end
