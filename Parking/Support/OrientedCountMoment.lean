/- Uniform centered moments and the displacement identity for directed coordinate counts. -/
import Parking.Support.CenteredSumMoment
import Parking.Support.OrientedMaximum
import Parking.Support.OrientedBinomial

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset

/-- The number of first-coordinate steps in a time interval. -/
def orientedFirstCount (p : ℕ → Fin 2 × Bool) (j h : ℕ) : ℕ :=
  ∑ k ∈ Ico j (j + h), if (p k).1 = 0 then 1 else 0

/-- A centered first-coordinate direction. -/
def orientedCenteredDirection (b : Fin 2 × Bool) : ℝ := if b.1 = 0 then 1 / 2 else -(1 / 2)

theorem abs_orientedCenteredDirection (b : Fin 2 × Bool) : |orientedCenteredDirection b| = 1 / 2 := by
  unfold orientedCenteredDirection
  split_ifs <;> norm_num

theorem integral_orientedCenteredDirection : ∫ b, orientedCenteredDirection b ∂(stepLaw 2) = 0 := by
  rw [integral_stepLaw (by norm_num), Fintype.sum_prod_type]
  norm_num [Fin.sum_univ_two, Fintype.sum_bool, orientedCenteredDirection]

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

theorem exists_orientedCount_moment (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ j h : ℕ,
      Integrable (fun ω : ℕ → Fin 2 × Bool => |(orientedFirstCount ω j h : ℝ) - (h : ℝ) / 2| ^ p)
        (walkLaw 2) ∧
      (∫ ω : ℕ → Fin 2 × Bool, |(orientedFirstCount ω j h : ℝ) - (h : ℝ) / 2| ^ p ∂(walkLaw 2)) ^ (2 / p) ≤
        C * (h : ℝ) := by
  haveI := stepLaw_isProbability (d := 2) (by norm_num)
  have hi : Integrable (fun b => |orientedCenteredDirection b| ^ p) (stepLaw 2) := by
    simp only [abs_orientedCenteredDirection]
    exact integrable_const _
  obtain ⟨C, hC, hb⟩ := exists_centered_sum_moment (ι := ℕ) (stepLaw 2)
    orientedCenteredDirection (measurable_from_countable' _) p hp hi integral_orientedCenteredDirection
  refine ⟨C, hC, fun j h => ?_⟩
  have hB := hb (Ico j (j + h))
  simpa only [sum_orientedCenteredDirection, Nat.card_Ico, Nat.add_sub_cancel_left, walkLaw] using hB

theorem orientedFirstCount_succ (p : ℕ → Fin 2 × Bool) (j h : ℕ) :
    orientedFirstCount p j (h + 1) = orientedFirstCount p j h +
      if (p (j + h)).1 = 0 then 1 else 0 := by
  rw [orientedFirstCount, Nat.add_succ, sum_Ico_succ_top (by omega)]
  rfl

theorem orientedLayerPoint_step (h : ℕ) (D : ℤ) (i : Fin 2) :
    orientedLayerPoint (h + 1) (D + if i = 0 then 1 else 0) = orientedLayerPoint h D - unit i := by
  fin_cases i <;> funext k <;> fin_cases k <;>
    simp [orientedLayerPoint, unit] <;> ring

/-- The increment over an interval is the layer point indexed by its first-coordinate count. -/
theorem orientedPath_interval (p : ℕ → Fin 2 × Bool) (j h : ℕ) (x : Site 2) :
    orientedPath x p (j + h) = orientedPath x p j + orientedLayerPoint h (orientedFirstCount p j h) := by
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
