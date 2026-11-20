import Parking.Support.OrientedBellman
import Parking.Support.OrientedWalkProjection
import Sandpile.Support.MainExplWalkValue

/-!
# Stopping values under the oriented-walk projection

The coordinate-difference path has the one-dimensional simple-walk law. Backward
induction supplies an optimal oriented rule that ignores the Boolean directions,
so it can be expressed as a stopping time of the projected path.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Parking

open LatticeProb

/-- The difference of the two coordinates as a one-dimensional lattice site. -/
def orientedProjectSite (z : Site 2) : Sandpile.Site 1 := fun _ => z 0 - z 1

/-- Decode one-dimensional path increments as oriented coordinate choices. -/
def orientedDecode (X : ℕ → Sandpile.Site 1) (j : ℕ) : Fin 2 × Bool :=
  (if X (j + 1) 0 - X j 0 = -1 then 0 else 1, false)

/-- Decoding a projected oriented path recovers each coordinate choice. -/
theorem orientedDecode_projectedPath_fst (p : ℕ → Fin 2 × Bool) (j : ℕ) :
    (orientedDecode (orientedProjectedPath p) j).1 = (p j).1 := by
  rw [orientedProjectedPath_eq_walkPath]
  rcases h : p j with ⟨c, b⟩
  fin_cases c <;>
    simp [orientedDecode, Sandpile.walkPath, Finset.sum_range_succ, orientedProjectedStep,
      LatticeProb.unit, h]

/-- A stopping rule on all sandpile paths pulls back to an oriented stopping rule. -/
theorem isStoppingTimeLE_projectedPath {n : ℕ} {τ : (ℕ → Sandpile.Site 1) → ℕ}
    (hτ : Sandpile.IsWalkStopping τ) (hτn : ∀ X, τ X ≤ n) :
    IsStoppingTimeLE n (fun p => τ (orientedProjectedPath p)) := by
  refine ⟨fun p => hτn _, ?_⟩
  intro p q hpq
  apply hτ (τ (orientedProjectedPath p)) (orientedProjectedPath p) (orientedProjectedPath q) _ rfl
  intro j hj
  have hp : orientedPath (0 : Site 2) p j = orientedPath (0 : Site 2) q j :=
    orientedPath_congr 0 j (fun i hi => hpq i (lt_of_lt_of_le hi hj))
  change (fun _ => orientedPath (0 : Site 2) p j 0 - orientedPath 0 p j 1) =
    (fun _ => orientedPath (0 : Site 2) q j 0 - orientedPath 0 q j 1)
  rw [hp]

/-- The optimal oriented rule descends to a stopping time on every lattice path. -/
theorem isWalkStopping_orientedOptimalRule (n : ℕ) (F : ℕ → Site 2 → ℝ) :
    Sandpile.IsWalkStopping (fun X => orientedOptimalRule n F 0 (orientedDecode X)) := by
  intro k X Y hXY hk
  rw [← hk]
  apply (orientedOptimalRule_bounded_and_congr n F 0).2
  intro j hj
  have hjk : j < k := by rwa [← hk]
  simp only [orientedDecode]
  rw [hXY j (by omega), hXY (j + 1) (by omega)]

/-- The descended optimal rule agrees with the original rule on projected paths. -/
theorem orientedOptimalRule_decode_projectedPath (n : ℕ) (F : ℕ → Site 2 → ℝ)
    (p : ℕ → Fin 2 × Bool) :
    orientedOptimalRule n F 0 (orientedDecode (orientedProjectedPath p)) =
      orientedOptimalRule n F 0 p := by
  have h := (orientedOptimalRule_bounded_and_congr n F 0).2 p
    (orientedDecode (orientedProjectedPath p))
  exact h (fun j _ => (orientedDecode_projectedPath_fst p j).symm)

/-- The projected path is a measurable function of the direction sequence. -/
theorem measurable_orientedProjectedPath : Measurable orientedProjectedPath := by
  apply Measurable.of_eval
  intro k
  apply Measurable.of_eval
  intro i
  have hm := measurable_orientedPath (0 : Site 2) k
  change Measurable (fun p => orientedPath (0 : Site 2) p k 0 - orientedPath 0 p k 1)
  exact (measurable_pi_apply 0 |>.comp hm).sub (measurable_pi_apply 1 |>.comp hm)

/-- A sandpile stopping payoff agrees with its pullback to the oriented path. -/
theorem orientedTerminalValue_projectedPath {n : ℕ}
    (F : ℕ → Sandpile.Site 1 → ℝ) {τ : (ℕ → Sandpile.Site 1) → ℕ}
    (hτ : Sandpile.IsWalkStopping τ) (hτn : ∀ X, τ X ≤ n) :
    orientedTerminalValue (fun k z => F k (orientedProjectSite z)) 0
      (fun p => τ (orientedProjectedPath p)) =
      ∫ X, F (τ X) (X (τ X)) ∂(Sandpile.walkLaw 1 0) := by
  have hm := Sandpile.measurable_stopped_value n F hτ hτn
  rw [← map_orientedProjectedPath_walkLaw,
    integral_map measurable_orientedProjectedPath.aemeasurable hm.aestronglyMeasurable]
  rfl

/-- The oriented and one-dimensional simple-walk stopping values coincide for
    every finite-horizon reward on the projected site. -/
theorem orientedStoppingSup_eq_sandpile_stoppingSup (n : ℕ) (F : ℕ → Sandpile.Site 1 → ℝ) :
    orientedStoppingSup 2 (fun k z => F k (orientedProjectSite z)) n 0 =
      Sandpile.stoppingSup n 0 (fun k X => F k (X k)) := by
  let G : ℕ → Site 2 → ℝ := fun k z => F k (orientedProjectSite z)
  let τ : (ℕ → Sandpile.Site 1) → ℕ := fun X => orientedOptimalRule n G 0 (orientedDecode X)
  have hτ : Sandpile.IsWalkStopping τ := isWalkStopping_orientedOptimalRule n G
  have hτn : ∀ X, τ X ≤ n := fun X => (orientedOptimalRule_bounded_and_congr n G 0).1 _
  have hbS := Sandpile.bddAbove_walk_stopped_value (d := 1) (by norm_num) 0 n F
  have hbP : BddAbove (orientedTerminalValues 2 G n 0) := by
    refine ⟨orientedBellman n G 0, ?_⟩
    rintro a ⟨σ, hσ, rfl⟩
    exact orientedTerminalValue_le_orientedBellman (by norm_num) n G 0 σ hσ
  apply le_antisymm
  · have hval : orientedTerminalValue G 0 (fun p => τ (orientedProjectedPath p)) =
        orientedStoppingSup 2 G n 0 := by
      rw [orientedStoppingSup_eq_orientedBellman (by norm_num),
        ← orientedTerminalValue_orientedOptimalRule (by norm_num)]
      congr 1
      funext p
      exact orientedOptimalRule_decode_projectedPath n G p
    rw [← hval, orientedTerminalValue_projectedPath F hτ hτn]
    exact le_csSup hbS ⟨τ, hτ, hτn, rfl⟩
  · apply csSup_le
    · exact ⟨_, ⟨fun _ => 0, Sandpile.isWalkStopping_const 0, fun _ => Nat.zero_le _, rfl⟩⟩
    · rintro a ⟨σ, hσ, hσn, rfl⟩
      rw [← orientedTerminalValue_projectedPath F hσ hσn]
      exact le_csSup hbP ⟨_, isStoppingTimeLE_projectedPath hσ hσn, rfl⟩

end Parking
