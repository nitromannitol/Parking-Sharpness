import Parking.Support.OrientedLayer
import Parking.Support.Oriented

/-!
# The binomial identification of the directed layers in dimension two

The binomial identification of the directed layers in dimension two.
-/

open LatticeProb.Walk (binomLaw_succ binomLaw_zero conv)

noncomputable section
namespace Parking
open LatticeProb Finset

/-- Integer coordinates on the directed layer in dimension two. -/
def orientedLayerPoint (l : ℕ) (j : ℤ) : Site 2 := ![-j, j - (l : ℤ)]

/-- In dimension two, `layerHeight x` is the coordinate sum `x 0 + x 1`. -/
theorem layerHeight_two (x : Site 2) : layerHeight x = x 0 + x 1 := by
  simp [layerHeight, Fin.sum_univ_two]

/-- The point `orientedLayerPoint l j` lies at layer height `-l`. -/
theorem layerHeight_orientedLayerPoint (l : ℕ) (j : ℤ) :
    layerHeight (orientedLayerPoint l j) = -(l : ℤ) := by
  simp only [layerHeight_two, orientedLayerPoint, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- `orientedLayerPoint l` is injective in its second argument. -/
theorem orientedLayerPoint_injective (l : ℕ) : Function.Injective (orientedLayerPoint l) := by
  intro i j hij
  have h := congrFun hij 0
  simpa [orientedLayerPoint] using h

/-- Every point at layer height `-l` is `orientedLayerPoint l` applied to the negative of
its first coordinate. -/
theorem orientedLayerPoint_eq {l : ℕ} {x : Site 2} (hx : layerHeight x = -(l : ℤ)) :
    orientedLayerPoint l (-x 0) = x := by
  rw [layerHeight_two] at hx
  funext i
  fin_cases i
  · simp [orientedLayerPoint]
  · change -x 0 - (l : ℤ) = x 1
    omega

/-- In dimension two, the directed layer function `orientedLayer 2 l` is supported on
layer height `-l`, where it agrees with the binomial law `binomLaw l` evaluated at the
negative first coordinate. -/
theorem orientedLayer_two (l : ℕ) (x : Site 2) :
    orientedLayer 2 l x = if layerHeight x = -(l : ℤ) then binomLaw l (-x 0) else 0 := by
  classical
  induction l generalizing x with
  | zero =>
    simp only [orientedLayer, binomLaw_zero, Nat.cast_zero, neg_zero]
    by_cases hx : x = 0
    · simp [hx, layerHeight_two]
    · rw [if_neg hx]
      by_cases hh : layerHeight x = 0
      · have hn : -x 0 ≠ 0 := by
          intro hn
          apply hx
          rw [layerHeight_two] at hh
          have h00 : x 0 = 0 := neg_eq_zero.mp hn
          have h11 : x 1 = 0 := by omega
          funext i
          fin_cases i
          · exact h00
          · exact h11
        simp [hh, hn]
      · simp [hh]
  | succ l ih =>
    rw [orientedLayer_succ, Fin.sum_univ_two, ih, ih]
    simp only [layerHeight_add, layerHeight_unit, Nat.cast_ofNat]
    have h0 : (x + unit (0 : Fin 2)) 0 = x 0 + 1 := by simp [unit]
    have h1 : (x + unit (1 : Fin 2)) 0 = x 0 := by simp [unit]
    rw [h0, h1]
    have he : -(x 0 + 1) = -x 0 - 1 := by ring
    rw [he]
    have hh : (layerHeight x + 1 = -(l : ℤ)) ↔ layerHeight x = -((l + 1 : ℕ) : ℤ) := by
      push_cast
      omega
    by_cases hx : layerHeight x = -((l + 1 : ℕ) : ℤ)
    · simp only [if_pos (hh.mpr hx), if_pos hx]
      exact (binomLaw_succ l (-x 0)).symm
    · simp only [if_neg (fun h => hx (hh.mp h)), if_neg hx]
      norm_num

/-- At the point `orientedLayerPoint l j`, the directed layer function equals
`binomLaw l j`. -/
theorem orientedLayer_at_layerPoint (l : ℕ) (j : ℤ) :
    orientedLayer 2 l (orientedLayerPoint l j) = binomLaw l j := by
  rw [orientedLayer_two, if_pos (layerHeight_orientedLayerPoint l j)]
  simp [orientedLayerPoint]

/-- The sum of squares of the directed layer function over layer `l` in dimension two
equals `conv l 0`, the self-convolution of the binomial law at zero. -/
theorem tsum_orientedLayer_two_sq (l : ℕ) :
    (∑' x : Site 2, orientedLayer 2 l x ^ 2) = conv l 0 := by
  have hs : Function.support (fun x : Site 2 => orientedLayer 2 l x ^ 2) ⊆
      Set.range (orientedLayerPoint l) := by
    intro x hx
    have hn : orientedLayer 2 l x ≠ 0 := by
      intro hn
      exact hx (by simp [hn])
    exact ⟨-x 0, orientedLayerPoint_eq (orientedLayer_height hn)⟩
  rw [← (orientedLayerPoint_injective l).tsum_eq hs]
  simp only [orientedLayer_at_layerPoint, conv, add_zero, pow_two]

/-- The sum of squares of the directed Green function at horizon `n` in dimension two is
the sum over layers `l < n` of `conv l 0`. -/
theorem tsum_orientedGreen_two_sq (n : ℕ) :
    (∑' x : Site 2, orientedGreen 2 n x ^ 2) = ∑ l ∈ range n, conv l 0 := by
  rw [tsum_orientedGreen_sq]
  simp only [tsum_orientedLayer_two_sq]

end Parking
