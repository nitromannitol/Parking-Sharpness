import Parking.Support.ValueLipschitz
import Sandpile.Support.MainExplWalkValue
import Sandpile.Support.StoppedOdometer
import Sandpile.Support.MembraneStopping
import Mathlib.Probability.Independence.InfinitePi

/-!
# The simple random walk on path space

The lattice path of a sequence of signed directions has the law of the simple random walk on
path space that the divisible sandpile stopping problem uses.  A direction is read off the
increment of the path, so stopping rules of the directions and stopping rules of the path
correspond, and every finite-horizon stopping value of the direction sequence equals the
corresponding sandpile stopping value.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- The walk from `x` is the sandpile path with the increments `stepVec (p j)`. -/
theorem walkPath_eq_sandpile_walkPath (x : Site d) (p : ℕ → Fin d × Bool) :
    walkPath x p = Sandpile.walkPath x (fun j => stepVec (p j)) := by
  funext k
  induction k with
  | zero => simp [walkPath, Sandpile.walkPath]
  | succ k ih =>
    rw [walkPath, ih]
    simp only [Sandpile.walkPath, Finset.sum_range_succ, add_assoc]

/-- The signed directions give distinct lattice steps. -/
theorem stepVec_injective : Function.Injective (stepVec (d := d)) := by
  rintro ⟨i, s⟩ ⟨j, t⟩ h
  have hi := congrFun h i
  have hj := congrFun h j
  cases s <;> cases t <;>
    simp only [stepVec, LatticeProb.unit, Pi.neg_apply, Pi.single_apply, ite_true,
      ite_false, Bool.false_eq_true] at hi hj ⊢ <;>
    by_cases hij : i = j <;> simp_all

/-- One signed direction, mapped to its lattice step, has the sandpile step law. -/
theorem map_stepVec_stepLaw : (stepLaw d).map stepVec = Sandpile.stepLaw d := by
  classical
  rw [stepLaw, Sandpile.stepLaw, LatticeProb.instructionLaw,
    Measure.map_smul _ (Measurable.of_discrete : Measurable (stepVec (d := d))).aemeasurable,
    Measure.map_finset_sum' (Measurable.of_discrete : Measurable (stepVec (d := d))).aemeasurable]
  simp only [Measure.map_dirac, Fintype.sum_prod_type, Fintype.sum_bool, stepVec, ite_true,
    Bool.false_eq_true, ite_false, zero_add, zero_sub]

/-- The lattice path of the direction sequence has the sandpile walk law. -/
theorem map_walkPath_walkLaw (hd : 1 ≤ d) :
    (walkLaw d).map (walkPath (0 : Site d)) = Sandpile.walkLaw d 0 := by
  have := stepLaw_isProbability hd
  have hstep : Measurable (stepVec (d := d)) := Measurable.of_discrete
  have hmap : (walkLaw d).map (fun p j => stepVec (p j)) =
      Measure.infinitePi (fun _ : ℕ => Sandpile.stepLaw d) := by
    rw [walkLaw, Measure.infinitePi_map_pi _ (fun _ => hstep)]
    simp only [map_stepVec_stepLaw]
  have hpath : Measurable (Sandpile.walkPath (0 : Site d)) := by
    apply Measurable.of_eval
    intro k
    unfold Sandpile.walkPath
    fun_prop
  rw [Sandpile.walkLaw, ← hmap, Measure.map_map hpath (by fun_prop)]
  congr 1
  funext p
  exact walkPath_eq_sandpile_walkPath 0 p

/-- The path of the direction sequence is a measurable function of it. -/
theorem measurable_walkPath_seq (x : Site d) :
    Measurable (walkPath x : (ℕ → Fin d × Bool) → ℕ → Site d) :=
  Measurable.of_eval fun j => measurable_walkPath x j

/-- The direction of the increment of a lattice path at step `j`; `b₀` is used where the
increment is not a unit step. -/
def stepDecode (b₀ : Fin d × Bool) (X : ℕ → Site d) (j : ℕ) : Fin d × Bool :=
  haveI : Nonempty (Fin d × Bool) := ⟨b₀⟩
  Function.invFun stepVec (X (j + 1) - X j)

/-- Decoding the path of a direction sequence recovers the sequence. -/
theorem stepDecode_walkPath (b₀ : Fin d × Bool) (x : Site d) (p : ℕ → Fin d × Bool) :
    stepDecode b₀ (walkPath x p) = p := by
  funext j
  have : Nonempty (Fin d × Bool) := ⟨b₀⟩
  have hinc : walkPath x p (j + 1) - walkPath x p j = stepVec (p j) := by
    rw [walkPath]
    abel
  simp only [stepDecode, hinc]
  exact Function.leftInverse_invFun stepVec_injective (p j)

/-- A stopping rule of the lattice path pulls back to a stopping rule of the directions. -/
theorem isStoppingTimeLE_comp_walkPath {n : ℕ} {τ : (ℕ → Site d) → ℕ}
    (hτ : Sandpile.IsWalkStopping τ) (hτn : ∀ X, τ X ≤ n) (x : Site d) :
    IsStoppingTimeLE n (fun p => τ (walkPath x p)) := by
  refine ⟨fun p => hτn _, ?_⟩
  intro p q hpq
  apply hτ (τ (walkPath x p)) (walkPath x p) (walkPath x q) _ rfl
  intro j hj
  exact walkPath_congr x (fun i hi => hpq i (lt_of_lt_of_le hi hj))

/-- A stopping rule of the directions descends to a stopping rule of the lattice path. -/
theorem isWalkStopping_comp_stepDecode (b₀ : Fin d × Bool) {n : ℕ}
    {σ : (ℕ → Fin d × Bool) → ℕ} (hσ : IsStoppingTimeLE n σ) :
    Sandpile.IsWalkStopping (fun X => σ (stepDecode b₀ X)) := by
  intro k X Y hXY hk
  rw [← hk]
  apply hσ.2
  intro j hj
  have hjk : j < k := by rwa [← hk]
  simp only [stepDecode]
  rw [hXY j (by omega), hXY (j + 1) (by omega)]

/-- A sandpile stopping payoff equals the payoff of its pullback to the directions. -/
theorem terminalValue_comp_walkPath (hd : 1 ≤ d) {n : ℕ} (F : ℕ → Site d → ℝ)
    {τ : (ℕ → Site d) → ℕ} (hτ : Sandpile.IsWalkStopping τ) (hτn : ∀ X, τ X ≤ n) :
    terminalValue F 0 (fun p => τ (walkPath 0 p)) =
      ∫ X, F (τ X) (X (τ X)) ∂(Sandpile.walkLaw d 0) := by
  have hm := Sandpile.measurable_stopped_value n F hτ hτn
  rw [← map_walkPath_walkLaw hd,
    integral_map (measurable_walkPath_seq 0).aemeasurable hm.aestronglyMeasurable]
  rfl

/-- **The stopping values of the direction sequence are the sandpile stopping values.** -/
theorem stoppingSup_eq_sandpile_stoppingSup (hd : 1 ≤ d) (n : ℕ) (F : ℕ → Site d → ℝ) :
    stoppingSup d F n 0 = Sandpile.stoppingSup n 0 (fun k X => F k (X k)) := by
  let b₀ : Fin d × Bool := (⟨0, hd⟩, true)
  have hbS := Sandpile.bddAbove_walk_stopped_value hd 0 n F
  apply le_antisymm
  · apply csSup_le (terminalValues_nonempty d F n 0)
    rintro a ⟨σ, hσ, rfl⟩
    let τ : (ℕ → Site d) → ℕ := fun X => σ (stepDecode b₀ X)
    have hτ : Sandpile.IsWalkStopping τ := isWalkStopping_comp_stepDecode b₀ hσ
    have hτn : ∀ X, τ X ≤ n := fun X => hσ.1 _
    have hval : terminalValue F 0 σ = terminalValue F 0 (fun p => τ (walkPath 0 p)) := by
      congr 1
      funext p
      simp only [τ, stepDecode_walkPath]
    rw [hval, terminalValue_comp_walkPath hd F hτ hτn]
    exact le_csSup hbS ⟨τ, hτ, hτn, rfl⟩
  · apply csSup_le
    · exact ⟨_, ⟨fun _ => 0, Sandpile.isWalkStopping_const 0, fun _ => Nat.zero_le _, rfl⟩⟩
    · rintro a ⟨τ, hτ, hτn, rfl⟩
      have hbP : BddAbove (terminalValues d F n 0) := by
        obtain ⟨M, hM⟩ := hbS
        refine ⟨M, ?_⟩
        rintro b ⟨σ, hσ, rfl⟩
        let τ' : (ℕ → Site d) → ℕ := fun X => σ (stepDecode b₀ X)
        have hτ' : Sandpile.IsWalkStopping τ' := isWalkStopping_comp_stepDecode b₀ hσ
        have hτ'n : ∀ X, τ' X ≤ n := fun X => hσ.1 _
        have hval : terminalValue F 0 σ = terminalValue F 0 (fun p => τ' (walkPath 0 p)) := by
          congr 1
          funext p
          simp only [τ', stepDecode_walkPath]
        rw [hval, terminalValue_comp_walkPath hd F hτ' hτ'n]
        exact hM ⟨τ', hτ', hτ'n, rfl⟩
      rw [← terminalValue_comp_walkPath hd F hτ hτn]
      exact le_csSup hbP ⟨_, isStoppingTimeLE_comp_walkPath hτ hτn 0, rfl⟩

end Parking
