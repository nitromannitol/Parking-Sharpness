import Parking.Support.OrientedPotential
import Mathlib.Data.Nat.Choose.Sum

/-!
# Commuting signed averages and their binomial expansion

Commuting signed averages and their binomial expansion.
-/

noncomputable section
namespace Parking
open LatticeProb Finset
variable {d : ℕ}

/-- The linear endomorphism `f ↦ (x ↦ f (x + v))` shifting a function by `v`. -/
def shiftLinear (v : Site d) : Module.End ℝ (Site d → ℝ) where
  toFun f x := f (x + v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Unfolds the action of `shiftLinear v` on `f` at `x`. -/
theorem shiftLinear_apply (v : Site d) (f : Site d → ℝ) (x : Site d) :
    shiftLinear v f x = f (x + v) := rfl

/-- The shifts `shiftLinear v` and `shiftLinear w` commute, since shifting by `v` then `w`
and shifting by `w` then `v` both amount to shifting by `v + w`. -/
theorem shiftLinear_commute (v w : Site d) : Commute (shiftLinear v) (shiftLinear w) := by
  apply LinearMap.ext
  intro f
  funext x
  change f (x + v + w) = f (x + w + v)
  congr 1
  abel

/-- The average of `shiftLinear` over the `d` standard basis directions, taken with a
positive or negative sign according to `positive`. -/
def signedAverage (d : ℕ) (positive : Bool) : Module.End ℝ (Site d → ℝ) :=
  (d : ℝ)⁻¹ • ∑ i : Fin d, shiftLinear (if positive then unit i else -unit i)

/-- Unfolds `signedAverage` as an explicit average of `f` shifted by the `d` signed
directions. -/
theorem signedAverage_apply (positive : Bool) (f : Site d → ℝ) (x : Site d) :
    signedAverage d positive f x =
      (∑ i : Fin d, f (x + if positive then unit i else -unit i)) / d := by
  simp only [signedAverage, LinearMap.smul_apply, LinearMap.sum_apply, Pi.smul_apply,
    Finset.sum_apply, shiftLinear_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The two signed averages commute, being scalar multiples of sums of the pairwise
commuting shifts `shiftLinear_commute`. -/
theorem signedAverage_commute (positive negative : Bool) :
    Commute (signedAverage d positive) (signedAverage d negative) := by
  apply Commute.smul_left
  apply Commute.smul_right
  apply Commute.sum_left
  intro i _
  apply Commute.sum_right
  intro j _
  exact shiftLinear_commute _ _

/-- The negative-signed average `signedAverage d false` agrees with `orientedOp`, both
being the average of `f` over the `d` predecessors `x - unit i`. -/
theorem signedAverage_false (f : Site d → ℝ) (x : Site d) :
    signedAverage d false f x = orientedOp f x := by
  simp only [signedAverage_apply, Bool.false_eq_true, if_false, ← sub_eq_add_neg, orientedOp]

/-- The positive-signed average of the `n`-th oriented layer is the `(n + 1)`-th layer,
matching the recursion `orientedLayer_succ`. -/
theorem signedAverage_true_layer (n : ℕ) (x : Site d) :
    signedAverage d true (orientedLayer d n) x = orientedLayer d (n + 1) x := by
  simp only [signedAverage_apply, if_true, orientedLayer_succ]

/-- The average of the positive- and negative-signed averages, the operator of the
ordinary (undirected) simple random walk. -/
def simpleAverage (d : ℕ) : Module.End ℝ (Site d → ℝ) :=
  (1 / 2 : ℝ) • (signedAverage d true + signedAverage d false)

/-- `simpleAverage` agrees with `walkOp`, the averaging operator of the ordinary simple
random walk over all `2d` neighbors. -/
theorem simpleAverage_apply (f : Site d → ℝ) (x : Site d) :
    simpleAverage d f x = walkOp f x := by
  simp only [simpleAverage, LinearMap.smul_apply, LinearMap.add_apply, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul, signedAverage_apply, if_true, Bool.false_eq_true, if_false,
    ← sub_eq_add_neg, walkOp, nbrSum, sum_add_distrib, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The `n`-th power of `simpleAverage` expands, via the binomial theorem for the
commuting operators `signedAverage d true` and `signedAverage d false`
(`signedAverage_commute`), as a `(1/2)^n`-weighted sum over the antidiagonal. -/
theorem simpleAverage_pow_binomial (n : ℕ) :
    simpleAverage d ^ n = (1 / 2 : ℝ) ^ n •
      ∑ m ∈ antidiagonal n, n.choose m.1 •
        (signedAverage d true ^ m.1 * signedAverage d false ^ m.2) := by
  rw [simpleAverage, smul_pow, (signedAverage_commute (d := d) true false).add_pow']

/-- Applying `signedAverage d true` `n` times to the point mass at `0` gives the `n`-th
oriented layer, by induction using `signedAverage_true_layer`. -/
theorem signedAverage_true_pow_delta (n : ℕ) :
    (signedAverage d true ^ n) (fun x : Site d => if x = 0 then 1 else 0) = orientedLayer d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    funext x
    exact signedAverage_true_layer n x

/-- Applying `simpleAverage d` `n` times to the point mass at `0` gives the `n`-th step
law of the ordinary simple random walk, `srwHeat d n`, by induction using
`simpleAverage_apply`. -/
theorem simpleAverage_pow_delta (n : ℕ) :
    (simpleAverage d ^ n) (fun x : Site d => if x = 0 then 1 else 0) = srwHeat d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    funext x
    exact simpleAverage_apply _ _

end Parking
