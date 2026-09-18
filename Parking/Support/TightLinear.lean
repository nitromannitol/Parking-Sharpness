/-
The linear decomposition of `Parking.orientedBoxReward` in the scenery
(`parking.tex:3192-3203`, Stage 2 of the covariance-to-Gaussian step).

`Parking.orientedBoxReward` is, for each fixed scale `n` and horizon `T`, a
finite linear combination of the i.i.d. scenery `η`: it is the bilinear
interpolation of the grid reward field at the (at most four) corners of the
cell containing the rescaled point, and each grid reward is itself, by
`Parking.orientedPotential_eq_box`, a finite sum of the scenery over a box.
This module assembles the two into one explicit finite linear functional of
`η`, with a coefficient depending only on the deterministic data `(T, n, u)`,
and extends it to a WEIGHTED SUM of finitely many box points, which is what
the finite-dimensional characteristic-function bridge of `TightCLT.lean`
consumes.
-/
import Parking.Support.TightCLT

open MeasureTheory LatticeProb Finset

noncomputable section
namespace Parking

/-- The (at most four) grid corners the interpolation reads at the rescaled
point of the box point `u`: the two candidate time coordinates and the two
candidate space coordinates, paired as `ℤ × ℤ`. -/
def orientedBoxRewardCorners (n : ℕ) (u : Fin 2 → ℝ) : Finset (ℤ × ℤ) :=
  ({⌊(n : ℝ) * u 0⌋, ⌊(n : ℝ) * u 0⌋ + 1} : Finset ℤ) ×ˢ
    ({⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋,
        ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ + 1} : Finset ℤ)

/-- The coefficient of a single site `z` in the grid reward at corner `c`,
before the hat weight: the Green-function coefficient of `Parking.orientedPotential`,
times the reward's own `-n^{-1/4}` prefactor. -/
def orientedGridRewardCoeff (n N : ℕ) (c : ℤ × ℤ) (z : Site 2) : ℝ :=
  -(n : ℝ) ^ (-(1 : ℝ) / 4) *
    orientedGreen 2 (N - c.1.toNat) (z - orientedLayerPoint c.1.toNat c.2)

/-- **The grid reward is the finite sum of `Parking.orientedGridRewardCoeff` against the
scenery**, over the box of sites the Green function actually reads. -/
theorem orientedGridReward_eq_sum (n N : ℕ) (η : Site 2 → ℝ) (c : ℤ × ℤ) :
    orientedGridReward n N η c.1 c.2 =
      ∑ z ∈ boxFinset (orientedLayerPoint c.1.toNat c.2) (N - c.1.toNat),
        orientedGridRewardCoeff n N c z * η z := by
  unfold orientedGridReward orientedGridRewardCoeff
  rw [orientedPotential_eq_box, Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ => by ring

/-- **The coefficient vanishes outside its own box.** -/
theorem orientedGridRewardCoeff_eq_zero_of_notMem {n N : ℕ} {c : ℤ × ℤ} {z : Site 2}
    (hz : z ∉ boxFinset (orientedLayerPoint c.1.toNat c.2) (N - c.1.toNat)) :
    orientedGridRewardCoeff n N c z = 0 := by
  unfold orientedGridRewardCoeff
  rw [orientedGreen_sub_zero_outside hz, mul_zero]

/-- The finite set of sites the box reward at `u` can possibly read: the union, over the
(at most four) corners of the cell, of the box each corner's grid reward reads. -/
def orientedBoxRewardSupport (T : ℝ) (n : ℕ) (u : Fin 2 → ℝ) : Finset (Site 2) :=
  (orientedBoxRewardCorners n u).biUnion fun c =>
    boxFinset (orientedLayerPoint c.1.toNat c.2) (⌊(n : ℝ) * T⌋₊ - c.1.toNat)

/-- **Each corner's own box lies inside the support.** -/
theorem boxFinset_subset_orientedBoxRewardSupport (T : ℝ) (n : ℕ) (u : Fin 2 → ℝ)
    {c : ℤ × ℤ} (hc : c ∈ orientedBoxRewardCorners n u) :
    boxFinset (orientedLayerPoint c.1.toNat c.2) (⌊(n : ℝ) * T⌋₊ - c.1.toNat) ⊆
      orientedBoxRewardSupport T n u :=
  Finset.subset_biUnion_of_mem
    (fun c : ℤ × ℤ => boxFinset (orientedLayerPoint c.1.toNat c.2) (⌊(n : ℝ) * T⌋₊ - c.1.toNat))
    hc

/-- The linear coefficient of the site `z` in `Parking.orientedBoxReward T n · u`: the
hat-weighted sum, over the (at most four) corners of the cell containing the rescaled
point, of the grid reward's own Green-function coefficient at `z`. -/
def orientedBoxRewardCoeff (T : ℝ) (n : ℕ) (u : Fin 2 → ℝ) (z : Site 2) : ℝ :=
  ∑ c ∈ orientedBoxRewardCorners n u,
    (hat1 ((n : ℝ) * u 0 - (c.1 : ℝ)) *
        hat1 (Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2 - (c.2 : ℝ))) *
      orientedGridRewardCoeff n ⌊(n : ℝ) * T⌋₊ c z

/-- **The linear decomposition of the box reward**: `Parking.orientedBoxReward T n η u` is
the finite sum of `Parking.orientedBoxRewardCoeff` against the scenery, over
`Parking.orientedBoxRewardSupport`. -/
theorem orientedBoxReward_eq_sum (T : ℝ) (n : ℕ) (η : Site 2 → ℝ) (u : Fin 2 → ℝ) :
    orientedBoxReward T n η u =
      ∑ z ∈ orientedBoxRewardSupport T n u, orientedBoxRewardCoeff T n u z * η z := by
  have hstep1 : orientedBoxReward T n η u =
      ∑ c ∈ orientedBoxRewardCorners n u,
        orientedGridReward n ⌊(n : ℝ) * T⌋₊ η c.1 c.2 *
          (hat1 ((n : ℝ) * u 0 - (c.1 : ℝ)) *
            hat1 (Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2 - (c.2 : ℝ))) := by
    unfold orientedBoxReward
    rw [hatInterp_eq_corners, orientedBoxRewardCorners, ← Finset.sum_product']
  have hstep2 : ∀ c ∈ orientedBoxRewardCorners n u,
      orientedGridReward n ⌊(n : ℝ) * T⌋₊ η c.1 c.2 *
        (hat1 ((n : ℝ) * u 0 - (c.1 : ℝ)) *
            hat1 (Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2 - (c.2 : ℝ))) =
      ∑ z ∈ boxFinset (orientedLayerPoint c.1.toNat c.2) (⌊(n : ℝ) * T⌋₊ - c.1.toNat),
        (hat1 ((n : ℝ) * u 0 - (c.1 : ℝ)) *
            hat1 (Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2 - (c.2 : ℝ))) *
          (orientedGridRewardCoeff n ⌊(n : ℝ) * T⌋₊ c z * η z) := by
    intro c _
    rw [orientedGridReward_eq_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun z _ => by ring
  have hstep3 : ∀ c ∈ orientedBoxRewardCorners n u,
      ∑ z ∈ boxFinset (orientedLayerPoint c.1.toNat c.2) (⌊(n : ℝ) * T⌋₊ - c.1.toNat),
        (hat1 ((n : ℝ) * u 0 - (c.1 : ℝ)) *
            hat1 (Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2 - (c.2 : ℝ))) *
          (orientedGridRewardCoeff n ⌊(n : ℝ) * T⌋₊ c z * η z) =
      ∑ z ∈ orientedBoxRewardSupport T n u,
        (hat1 ((n : ℝ) * u 0 - (c.1 : ℝ)) *
            hat1 (Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2 - (c.2 : ℝ))) *
          (orientedGridRewardCoeff n ⌊(n : ℝ) * T⌋₊ c z * η z) := by
    intro c hc
    refine Finset.sum_subset (boxFinset_subset_orientedBoxRewardSupport T n u hc) ?_
    intro z _ hz
    rw [orientedGridRewardCoeff_eq_zero_of_notMem hz, zero_mul, mul_zero]
  rw [hstep1, Finset.sum_congr rfl hstep2, Finset.sum_congr rfl hstep3, Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  unfold orientedBoxRewardCoeff
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- **The coefficient vanishes outside the support**: every corner's own contribution
vanishes once `z` lies outside that corner's box, which is guaranteed once `z` lies
outside the whole support. -/
theorem orientedBoxRewardCoeff_eq_zero_of_notMem {T : ℝ} {n : ℕ} {u : Fin 2 → ℝ} {z : Site 2}
    (hz : z ∉ orientedBoxRewardSupport T n u) : orientedBoxRewardCoeff T n u z = 0 := by
  unfold orientedBoxRewardCoeff
  refine Finset.sum_eq_zero fun c hc => ?_
  have hzc : z ∉ boxFinset (orientedLayerPoint c.1.toNat c.2) (⌊(n : ℝ) * T⌋₊ - c.1.toNat) :=
    fun hmem => hz (boxFinset_subset_orientedBoxRewardSupport T n u hc hmem)
  rw [orientedGridRewardCoeff_eq_zero_of_notMem hzc, mul_zero]

/-- **The vector linear decomposition**: any weighted sum of `Parking.orientedBoxReward` at
finitely many box points is itself a single finitely-supported weighted sum of the scenery,
with the weight the corresponding linear combination of `Parking.orientedBoxRewardCoeff`. -/
theorem orientedBoxReward_vec_eq_sum (T : ℝ) (n : ℕ) (η : Site 2 → ℝ) {k : ℕ}
    (u : Fin k → Fin 2 → ℝ) (t : Fin k → ℝ) :
    ∑ l, t l * orientedBoxReward T n η (u l) =
      ∑ z ∈ Finset.univ.biUnion fun l => orientedBoxRewardSupport T n (u l),
        (∑ l, t l * orientedBoxRewardCoeff T n (u l) z) * η z := by
  have hstep1 : ∀ l : Fin k, t l * orientedBoxReward T n η (u l) =
      ∑ z ∈ Finset.univ.biUnion fun l => orientedBoxRewardSupport T n (u l),
        t l * (orientedBoxRewardCoeff T n (u l) z * η z) := by
    intro l
    rw [orientedBoxReward_eq_sum, Finset.mul_sum]
    refine Finset.sum_subset
      (Finset.subset_biUnion_of_mem (fun l => orientedBoxRewardSupport T n (u l))
        (Finset.mem_univ l)) ?_
    intro z _ hz
    rw [orientedBoxRewardCoeff_eq_zero_of_notMem hz, zero_mul, mul_zero]
  rw [Finset.sum_congr rfl fun l _ => hstep1 l, Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

end Parking
end
