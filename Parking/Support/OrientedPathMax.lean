/- The recursive directed maximum is the maximum over path times. -/
import Parking.Support.OrientedIncrement

noncomputable section
namespace Parking
open LatticeProb MeasureTheory Finset
variable {d : ℕ}

theorem orientedPath_tail (x : Site d) (p : ℕ → Fin d × Bool) (j : ℕ) :
    orientedPath x p (j + 1) = orientedPath (x - unit (p 0).1) (tailNat p) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change orientedPath x p (j + 1) - unit (p (j + 1)).1 =
      orientedPath (x - unit (p 0).1) (tailNat p) j - unit (tailNat p j).1
    rw [ih]
    rfl

theorem orientedMax_le_iff (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d)
    (p : ℕ → Fin d × Bool) (b : ℝ) :
    orientedMax F n x p ≤ b ↔ ∀ j : ℕ, j ≤ n → |F (n - j) (orientedPath x p j)| ≤ b := by
  induction n generalizing x p with
  | zero => simp [orientedMax, orientedPath]
  | succ n ih =>
    rw [orientedMax, max_le_iff, ih]
    constructor
    · rintro ⟨h0, hs⟩ j hj
      cases j with
      | zero => simpa only [Nat.sub_zero, orientedPath] using h0
      | succ j => simpa only [Nat.add_sub_add_right, orientedPath_tail] using hs j (by omega)
    · intro h
      refine ⟨by simpa only [Nat.sub_zero, orientedPath] using h 0 (by omega), ?_⟩
      intro j hj
      simpa only [Nat.add_sub_add_right, orientedPath_tail] using h (j + 1) (by omega)

theorem orientedMax_eq_sup (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d)
    (p : ℕ → Fin d × Bool) :
    orientedMax F n x p = (range (n + 1)).sup' (by simp)
      (fun j => |F (n - j) (orientedPath x p j)|) := by
  apply le_antisymm
  · apply (orientedMax_le_iff F n x p _).mpr
    intro j hj
    exact le_sup' (fun j => |F (n - j) (orientedPath x p j)|) (mem_range.mpr (by omega))
  · apply sup'_le
    intro j hj
    exact (orientedMax_le_iff F n x p _).mp le_rfl j (by have := mem_range.mp hj; omega)

theorem measurable_orientedPotentialMax (n : ℕ) :
    Measurable fun ω : (ℕ → Fin d × Bool) × (Site d → ℝ) =>
      orientedMax (orientedPotential ω.2) n 0 ω.1 := by
  simp only [orientedMax_eq_sup]
  exact Finset.measurable_range_sup'' (fun j _ => (measurable_orientedPotentialAlong (d := d) n j).abs)

end Parking
