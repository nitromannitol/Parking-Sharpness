/- Commuting signed averages and their binomial expansion. -/
import Parking.Support.OrientedPotential
import Mathlib.Data.Nat.Choose.Sum

noncomputable section
namespace Parking
open LatticeProb Finset
variable {d : ℕ}

def shiftLinear (v : Site d) : Module.End ℝ (Site d → ℝ) where
  toFun f x := f (x + v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem shiftLinear_apply (v : Site d) (f : Site d → ℝ) (x : Site d) :
    shiftLinear v f x = f (x + v) := rfl

theorem shiftLinear_commute (v w : Site d) : Commute (shiftLinear v) (shiftLinear w) := by
  apply LinearMap.ext
  intro f
  funext x
  change f (x + v + w) = f (x + w + v)
  congr 1
  abel

def signedAverage (d : ℕ) (positive : Bool) : Module.End ℝ (Site d → ℝ) :=
  (d : ℝ)⁻¹ • ∑ i : Fin d, shiftLinear (if positive then unit i else -unit i)

theorem signedAverage_apply (positive : Bool) (f : Site d → ℝ) (x : Site d) :
    signedAverage d positive f x =
      (∑ i : Fin d, f (x + if positive then unit i else -unit i)) / d := by
  simp only [signedAverage, LinearMap.smul_apply, LinearMap.sum_apply, Pi.smul_apply,
    Finset.sum_apply, shiftLinear_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem signedAverage_commute (positive negative : Bool) :
    Commute (signedAverage d positive) (signedAverage d negative) := by
  apply Commute.smul_left
  apply Commute.smul_right
  apply Commute.sum_left
  intro i _
  apply Commute.sum_right
  intro j _
  exact shiftLinear_commute _ _

theorem signedAverage_false (f : Site d → ℝ) (x : Site d) :
    signedAverage d false f x = orientedOp f x := by
  simp only [signedAverage_apply, Bool.false_eq_true, if_false, ← sub_eq_add_neg, orientedOp]

theorem signedAverage_true_layer (n : ℕ) (x : Site d) :
    signedAverage d true (orientedLayer d n) x = orientedLayer d (n + 1) x := by
  simp only [signedAverage_apply, if_true, orientedLayer_succ]

def simpleAverage (d : ℕ) : Module.End ℝ (Site d → ℝ) :=
  (1 / 2 : ℝ) • (signedAverage d true + signedAverage d false)

theorem simpleAverage_apply (f : Site d → ℝ) (x : Site d) :
    simpleAverage d f x = walkOp f x := by
  simp only [simpleAverage, LinearMap.smul_apply, LinearMap.add_apply, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul, signedAverage_apply, if_true, Bool.false_eq_true, if_false,
    ← sub_eq_add_neg, walkOp, nbrSum, sum_add_distrib, div_eq_mul_inv, mul_inv_rev]
  ring

theorem simpleAverage_pow_binomial (n : ℕ) :
    simpleAverage d ^ n = (1 / 2 : ℝ) ^ n •
      ∑ m ∈ antidiagonal n, n.choose m.1 •
        (signedAverage d true ^ m.1 * signedAverage d false ^ m.2) := by
  rw [simpleAverage, smul_pow, (signedAverage_commute (d := d) true false).add_pow']

theorem signedAverage_true_pow_delta (n : ℕ) :
    (signedAverage d true ^ n) (fun x : Site d => if x = 0 then 1 else 0) = orientedLayer d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    funext x
    exact signedAverage_true_layer n x

theorem simpleAverage_pow_delta (n : ℕ) :
    (simpleAverage d ^ n) (fun x : Site d => if x = 0 then 1 else 0) = srwHeat d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    funext x
    exact simpleAverage_apply _ _

end Parking
