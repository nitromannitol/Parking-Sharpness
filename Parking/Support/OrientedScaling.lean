/-
The rescaling of the directed lattice used by the scaling limit
(`parking.tex:3192-3196`).

The paper identifies layer `ℓ` with the sites `(-j, j-ℓ)`, `j ∈ ℤ`, and rescales
the scenery by

    `n^{-3/4} ∑_{ℓ≥0} ∑_{j∈ℤ} η(-j, j-ℓ) δ_{(ℓ/n, (j-ℓ/2)/√n)}`,

so a site `z ∈ ℤ²` sits in layer `ℓ(z) = -(z₁+z₂)` at `j = -z₁`, and its
rescaled spatial coordinate is

    `(j - ℓ/2)/√n = (z₂ - z₁)/(2√n)`.

The oriented walk subtracts a unit vector at every step, so `ℓ` increases by one
per step: the layer index of the position after `k` steps from `x` is
`ℓ(x) + k`.  That is why the layer index is the time variable of the limit, and
why the rescaled spatial coordinate has variance `k/4` after `k` steps, which is
the `Var(B_t) = t/4` of `parking.tex:3175`: one step changes `(z₂-z₁)/2` by
`±1/2`.
-/
import Parking.Support.OrientedStopping

noncomputable section

namespace Parking

open LatticeProb

/-- The layer index `ℓ(z) = -(z₁ + z₂)` of a site of `ℤ²`, the time variable of
the directed scaling limit. -/
def orientedLayerIndex (z : Site 2) : ℤ := -(z 0 + z 1)

/-- The rescaled spatial coordinate `(j - ℓ/2)/√n = (z₂ - z₁)/(2√n)` of a site
of `ℤ²` at scale `n`. -/
def orientedScaledSite (n : ℕ) (z : Site 2) : ℝ :=
  ((z 1 : ℝ) - (z 0 : ℝ)) / (2 * Real.sqrt n)

/-- One oriented step raises the layer index by one. -/
theorem orientedLayerIndex_sub_unit (z : Site 2) (i : Fin 2) :
    orientedLayerIndex (z - unit i) = orientedLayerIndex z + 1 := by
  unfold orientedLayerIndex unit
  fin_cases i <;>
    simp [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne] <;> ring

/-- **The layer index is the time of the oriented walk.**  The position after `k`
steps sits `k` layers below the start, which is what makes the layer the time
variable of the scaling limit and the rescaled site a function of the elapsed
time and the rescaled position alone. -/
theorem orientedLayerIndex_orientedPath (x : Site 2) (p : ℕ → Fin 2 × Bool) (k : ℕ) :
    orientedLayerIndex (orientedPath x p k) = orientedLayerIndex x + k := by
  induction k with
  | zero => simp [orientedPath]
  | succ k ih =>
      show orientedLayerIndex (orientedPath x p k - unit (p k).1) = _
      rw [orientedLayerIndex_sub_unit, ih]
      push_cast
      ring

end Parking

end
