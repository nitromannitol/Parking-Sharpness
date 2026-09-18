/-
The rescaled convolved potential of the directed scaling limit as a two-parameter
process on `[0,T] × [-2A, 2A]` (`parking.tex:3192-3203`).

Step 1 of the proof of `prop:oriented-scaling` identifies layer `ℓ` with the
sites `(-j, j-ℓ)`, `j ∈ ℤ`, and rescales the scenery by
`n^{-3/4} ∑_{ℓ≥0} ∑_{j∈ℤ} η(-j,j-ℓ) δ_{(ℓ/n,(j-ℓ/2)/√n)}`.  The convolved
potential of that rescaled scenery at the space-time point `(s,y)` is the
truncated linear potential `Φ_{⌊ns⌋}` of the directed kernel, read at the
lattice site of layer `⌊ns⌋` nearest to `⌊ns⌋/2 + √n y`, and carrying the
prefactor `n^{-1/4}`.

This module builds that reading: `orientedFieldSite` is the lattice site,
`orientedRescaledPotential` is the rescaled potential as a function of the
scenery, and the two structural lemmas below are its measurability and the
identification of its increments with the potential differences that the
scenery moment bound of `Parking.exists_oriented_potential_scenery_bound`
controls.
-/
import Parking.Support.OrientedSceneryMoment

open MeasureTheory LatticeProb

noncomputable section
namespace Parking

/-- The lattice site of the directed scaling limit at the rescaled space-time
point `(s,y)`: the site of layer `⌊ns⌋` whose layer coordinate `j` is the
integer nearest to `⌊ns⌋/2 + √n y`. -/
def orientedFieldSite (n : ℕ) (s y : ℝ) : Site 2 :=
  orientedLayerPoint ⌊(n : ℝ) * s⌋₊
    (round ((⌊(n : ℝ) * s⌋₊ : ℝ) / 2 + Real.sqrt n * y))

/-- The rescaled convolved potential `n^{-1/4} Φ_{⌊ns⌋}` at the rescaled
space-time point `(s,y)`, as a function of the scenery. -/
def orientedRescaledPotential (n : ℕ) (s y : ℝ) (η : Site 2 → ℝ) : ℝ :=
  (n : ℝ) ^ (-(1 : ℝ) / 4) * orientedPotential η ⌊(n : ℝ) * s⌋₊ (orientedFieldSite n s y)

/-- **The rescaled convolved potential is measurable in the scenery.** -/
theorem measurable_orientedRescaledPotential (n : ℕ) (s y : ℝ) :
    Measurable fun η : Site 2 → ℝ => orientedRescaledPotential n s y η :=
  measurable_const.mul (measurable_orientedPotential ⌊(n : ℝ) * s⌋₊ (orientedFieldSite n s y))

/-- **The difference of two field sites is a layer point of the layer
difference.**  This is what puts the increment of the rescaled potential into
the shape of `Parking.exists_oriented_potential_scenery_bound`. -/
theorem orientedFieldSite_sub (n : ℕ) (s y s' y' : ℝ)
    (h : ⌊(n : ℝ) * s'⌋₊ ≤ ⌊(n : ℝ) * s⌋₊) :
    orientedFieldSite n s y - orientedFieldSite n s' y' =
      orientedLayerPoint (⌊(n : ℝ) * s⌋₊ - ⌊(n : ℝ) * s'⌋₊)
        (round ((⌊(n : ℝ) * s⌋₊ : ℝ) / 2 + Real.sqrt n * y)
          - round ((⌊(n : ℝ) * s'⌋₊ : ℝ) / 2 + Real.sqrt n * y')) := by
  funext i
  fin_cases i <;>
    simp only [orientedFieldSite, orientedLayerPoint, Pi.sub_apply] <;>
    push_cast [Nat.cast_sub h] <;>
    ring

/-- **The site displacement**: the later site is the earlier site displaced by
the layer point `p_h(D)`, with `h` the layer difference and `D` the round
difference. -/
theorem orientedFieldSite_eq_add (n : ℕ) (s y s' y' : ℝ)
    (h : ⌊(n : ℝ) * s'⌋₊ ≤ ⌊(n : ℝ) * s⌋₊) :
    orientedFieldSite n s y =
      orientedFieldSite n s' y' + orientedLayerPoint (⌊(n : ℝ) * s⌋₊ - ⌊(n : ℝ) * s'⌋₊)
        (round ((⌊(n : ℝ) * s⌋₊ : ℝ) / 2 + Real.sqrt n * y) -
          round ((⌊(n : ℝ) * s'⌋₊ : ℝ) / 2 + Real.sqrt n * y')) := by
  rw [← orientedFieldSite_sub n s y s' y' h]
  abel

/-- **The site in a prescribed layer with a prescribed layer coordinate.** -/
def orientedFieldSiteLayer (n : ℕ) (s y : ℝ) (N : ℕ) : Site 2 :=
  orientedLayerPoint N (round ((⌊(n : ℝ) * s⌋₊ : ℝ) / 2 + Real.sqrt n * y))

/-- **The spatial piece**: two sites in the same layer differ by a layer point of
layer zero. -/
theorem orientedFieldSiteLayer_sub (n : ℕ) (s y s' y' : ℝ) :
    orientedFieldSite n s y - orientedFieldSiteLayer n s' y' ⌊(n : ℝ) * s⌋₊ =
      orientedLayerPoint 0
        (round ((⌊(n : ℝ) * s⌋₊ : ℝ) / 2 + Real.sqrt n * y) -
          round ((⌊(n : ℝ) * s'⌋₊ : ℝ) / 2 + Real.sqrt n * y')) := by
  funext i
  fin_cases i <;> simp [orientedFieldSite, orientedFieldSiteLayer, orientedLayerPoint]
  ring

/-- **The temporal piece**: the same layer coordinate in two layers differs by a
layer point of the layer difference. -/
theorem orientedFieldSiteLayer_temporal (n : ℕ) (s _y s' y' : ℝ)
    (h : ⌊(n : ℝ) * s'⌋₊ ≤ ⌊(n : ℝ) * s⌋₊) :
    orientedFieldSiteLayer n s' y' ⌊(n : ℝ) * s⌋₊ - orientedFieldSite n s' y' =
      orientedLayerPoint (⌊(n : ℝ) * s⌋₊ - ⌊(n : ℝ) * s'⌋₊) 0 := by
  funext i
  fin_cases i <;>
    simp [orientedFieldSite, orientedFieldSiteLayer, orientedLayerPoint, Nat.cast_sub h]

/-- **The `p`-th power of the absolute increment of the rescaled potential** is
the prefactor `n^{-p/4}` times the `p`-th power of the absolute potential
increment over the layer displacement. -/
theorem orientedRescaledPotential_abs_sub_rpow (n : ℕ) (s y s' y' : ℝ)
    (_h : ⌊(n : ℝ) * s'⌋₊ ≤ ⌊(n : ℝ) * s⌋₊) (p : ℝ) (η : Site 2 → ℝ) :
    |orientedRescaledPotential n s y η - orientedRescaledPotential n s' y' η| ^ p =
      ((n : ℝ) ^ (-(1 : ℝ) / 4)) ^ p *
        |orientedPotential η ⌊(n : ℝ) * s⌋₊ (orientedFieldSite n s y) -
          orientedPotential η ⌊(n : ℝ) * s'⌋₊ (orientedFieldSite n s' y')| ^ p := by
  rw [orientedRescaledPotential, orientedRescaledPotential, ← mul_sub, abs_mul,
    Real.abs_rpow_of_nonneg (by positivity), Real.mul_rpow (by positivity) (abs_nonneg _),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ))]

/-- **The increment decomposition**: the increment of the potential over a
space-time displacement is the sum of a spatial increment at the later layer and
a temporal increment at the displaced site. -/
theorem orientedPotential_increment_decomposition (n : ℕ) (s y s' y' : ℝ)
    (h : ⌊(n : ℝ) * s'⌋₊ ≤ ⌊(n : ℝ) * s⌋₊) (η : Site 2 → ℝ) :
    orientedPotential η ⌊(n : ℝ) * s⌋₊ (orientedFieldSite n s y) -
        orientedPotential η ⌊(n : ℝ) * s'⌋₊ (orientedFieldSite n s' y') =
      (orientedPotential η (⌊(n : ℝ) * s'⌋₊ + (⌊(n : ℝ) * s⌋₊ - ⌊(n : ℝ) * s'⌋₊))
          (orientedFieldSite n s y) -
        orientedPotential η (⌊(n : ℝ) * s'⌋₊ + (⌊(n : ℝ) * s⌋₊ - ⌊(n : ℝ) * s'⌋₊))
          (orientedFieldSite n s' y' + orientedLayerPoint (⌊(n : ℝ) * s⌋₊ - ⌊(n : ℝ) * s'⌋₊)
            (round ((⌊(n : ℝ) * s⌋₊ : ℝ) / 2 + Real.sqrt n * y) -
              round ((⌊(n : ℝ) * s'⌋₊ : ℝ) / 2 + Real.sqrt n * y')))) +
      (orientedPotential η (⌊(n : ℝ) * s'⌋₊ + (⌊(n : ℝ) * s⌋₊ - ⌊(n : ℝ) * s'⌋₊))
          (orientedFieldSite n s' y' + orientedLayerPoint (⌊(n : ℝ) * s⌋₊ - ⌊(n : ℝ) * s'⌋₊)
            (round ((⌊(n : ℝ) * s⌋₊ : ℝ) / 2 + Real.sqrt n * y) -
              round ((⌊(n : ℝ) * s'⌋₊ : ℝ) / 2 + Real.sqrt n * y'))) -
        orientedPotential η ⌊(n : ℝ) * s'⌋₊ (orientedFieldSite n s' y')) := by
  rw [orientedFieldSite_eq_add n s y s' y' h, Nat.add_sub_of_le h]
  ring

end Parking
end
