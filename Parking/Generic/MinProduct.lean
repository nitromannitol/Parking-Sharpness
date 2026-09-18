/-
A one-line arithmetic fact about `min`: the product of two minima lower-bounds the minimum of
the cross products, for nonnegative reals.  This module is stated for four arbitrary nonnegative
reals and mentions no object specific to this paper: nothing in the statement refers to
`linPotential`, `Site d`, or any other object of the model.  It is used by
`Parking.Support.LinPotentialMaximal` to collapse the two `d`-dependent kernel-norm constants of
the discrete maximal inequality into a single rate constant.
-/
import Mathlib

noncomputable section
namespace Parking.Generic.MinProduct

/-- **The product of two minima lower-bounds the minimum of the cross products.**  For
nonnegative reals `a, b, x, y`: `min a b * min x y ≤ min (a * x) (b * y)`.  Proof: `min a b ≤ a`
and `min x y ≤ x` combine (both nonnegative) to `min a b * min x y ≤ a * x`, and symmetrically
for `b * y`; take the `min` of both. -/
theorem min_mul_min_le (a b x y : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    min a b * min x y ≤ min (a * x) (b * y) := by
  refine le_min ?_ ?_
  · exact mul_le_mul (min_le_left a b) (min_le_left x y) (le_min hx hy) ha
  · exact mul_le_mul (min_le_right a b) (min_le_right x y) (le_min hx hy) hb

end Parking.Generic.MinProduct
end
