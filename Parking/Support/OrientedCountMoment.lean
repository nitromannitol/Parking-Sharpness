import Parking.Support.CenteredSumMoment
import Parking.Support.OrientedMaximum
import Parking.Support.OrientedBinomial

/-!
# Directed coordinate count moments

Uniform centered moments and the displacement identity for directed coordinate counts.
-/

open LatticeProb (measurable_from_countable')

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset

/-- The number of first-coordinate steps in a time interval. -/
def orientedFirstCount (p : ℕ → Fin 2 × Bool) (j h : ℕ) : ℕ :=
  ∑ k ∈ Ico j (j + h), if (p k).1 = 0 then 1 else 0

/-- A centered first-coordinate direction. -/
def orientedCenteredDirection (b : Fin 2 × Bool) : ℝ := if b.1 = 0 then 1 / 2 else -(1 / 2)

/-- `orientedCenteredDirection` always has absolute value `1 / 2`, by cases on the
`if`-branch in its definition. -/
theorem abs_orientedCenteredDirection (b : Fin 2 × Bool) :
    |orientedCenteredDirection b| = 1 / 2 := by
  unfold orientedCenteredDirection
  split_ifs <;> norm_num

/-- `orientedCenteredDirection` has mean zero under the uniform step law `stepLaw 2`,
since its two values `± 1 / 2` are taken with equal probability. -/
theorem integral_orientedCenteredDirection : ∫ b, orientedCenteredDirection b ∂(stepLaw 2) = 0 := by
  rw [integral_stepLaw (by norm_num), Fintype.sum_prod_type]
  norm_num [Fin.sum_univ_two, Fintype.sum_bool, orientedCenteredDirection]

/-- Summing `orientedCenteredDirection (p k)` over `k ∈ [j, j + h)` recovers the centered
first-coordinate count `orientedFirstCount p j h - h / 2`, by rewriting each summand as an
indicator minus `1 / 2` and simplifying the resulting sum. -/
theorem sum_orientedCenteredDirection (p : ℕ → Fin 2 × Bool) (j h : ℕ) :
    (∑ k ∈ Ico j (j + h), orientedCenteredDirection (p k)) =
      (orientedFirstCount p j h : ℝ) - (h : ℝ) / 2 := by
  have he : ∀ k : ℕ, orientedCenteredDirection (p k) =
      ((if (p k).1 = 0 then 1 else 0 : ℕ) : ℝ) - 1 / 2 := by
    intro k
    by_cases hk : (p k).1 = 0 <;> norm_num [orientedCenteredDirection, hk]
  simp only [sum_congr rfl (fun k _ => he k), sum_sub_distrib, sum_const,
    Nat.card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul, orientedFirstCount, Nat.cast_sum]
  ring

/-- The centered first-coordinate count has a uniform `p`-th moment bound of order
`h`, for `p ≥ 2`, transported from `exists_centered_sum_moment` applied to the i.i.d.
centered summands `orientedCenteredDirection` via `sum_orientedCenteredDirection`. -/
theorem exists_orientedCount_moment (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ j h : ℕ,
      Integrable (fun ω : ℕ → Fin 2 × Bool => |(orientedFirstCount ω j h : ℝ) - (h : ℝ) / 2| ^ p)
        (walkLaw 2) ∧
      (∫ ω : ℕ → Fin 2 × Bool,
        |(orientedFirstCount ω j h : ℝ) - (h : ℝ) / 2| ^ p ∂(walkLaw 2)) ^ (2 / p) ≤
        C * (h : ℝ) := by
  haveI := stepLaw_isProbability (d := 2) (by norm_num)
  have hi : Integrable (fun b => |orientedCenteredDirection b| ^ p) (stepLaw 2) := by
    simp only [abs_orientedCenteredDirection]
    exact integrable_const _
  obtain ⟨C, hC, hb⟩ := exists_centered_sum_moment (ι := ℕ) (stepLaw 2)
    orientedCenteredDirection (measurable_from_countable' _) p hp hi
    integral_orientedCenteredDirection
  refine ⟨C, hC, fun j h => ?_⟩
  have hB := hb (Ico j (j + h))
  simpa only [sum_orientedCenteredDirection, Nat.card_Ico, Nat.add_sub_cancel_left,
    walkLaw] using hB

/-- Extending the interval by one step adds the new step's contribution to
`orientedFirstCount`, by splitting off the top term of the defining sum
(`sum_Ico_succ_top`). -/
theorem orientedFirstCount_succ (p : ℕ → Fin 2 × Bool) (j h : ℕ) :
    orientedFirstCount p j (h + 1) = orientedFirstCount p j h +
      if (p (j + h)).1 = 0 then 1 else 0 := by
  rw [orientedFirstCount, Nat.add_succ, sum_Ico_succ_top (by omega)]
  rfl

/-- Incrementing the height `h` while adding one to the coordinate `D` exactly when
`i = 0` shifts `orientedLayerPoint h D` back by the unit vector `unit i`; checked by
cases on `i` and its coordinates. -/
theorem orientedLayerPoint_step (h : ℕ) (D : ℤ) (i : Fin 2) :
    orientedLayerPoint (h + 1) (D + if i = 0 then 1 else 0) = orientedLayerPoint h D - unit i := by
  fin_cases i <;> funext k <;> fin_cases k <;>
    simp [orientedLayerPoint, unit] <;> ring

/-- The increment over an interval is the layer point indexed by its first-coordinate count. -/
theorem orientedPath_interval (p : ℕ → Fin 2 × Bool) (j h : ℕ) (x : Site 2) :
    orientedPath x p (j + h) =
      orientedPath x p j + orientedLayerPoint h (orientedFirstCount p j h) := by
  induction h with
  | zero =>
    have he : orientedLayerPoint 0 0 = (0 : Site 2) := by
      funext i
      fin_cases i <;> rfl
    simp [orientedFirstCount, he]
  | succ h ih =>
    rw [Nat.add_succ, orientedPath, ih, orientedFirstCount_succ]
    push_cast
    rw [orientedLayerPoint_step]
    abel

end Parking
