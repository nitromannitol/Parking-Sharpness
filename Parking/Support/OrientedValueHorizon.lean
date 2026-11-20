import Parking.Support.OrientedValueLipschitz

/-!
# Reward perturbations on a finite horizon

A bounded stopping rule only evaluates its reward up to its horizon. Thus a
uniform bound on the difference over those times controls the stopping value.
-/

open MeasureTheory

noncomputable section

namespace Parking

open LatticeProb
variable {d : ℕ}

/-- The difference of terminal values is bounded by the reward difference on
    the stopping horizon. -/
theorem abs_orientedTerminalValue_sub_le_of_le (hd : 1 ≤ d) {n : ℕ}
    {σ : (ℕ → Fin d × Bool) → ℕ} (hσ : IsStoppingTimeLE n σ)
    (F G : ℕ → Site d → ℝ) (x : Site d) {c : ℝ}
    (hdiff : ∀ k ≤ n, ∀ y, |F k y - G k y| ≤ c) :
    |orientedTerminalValue F x σ - orientedTerminalValue G x σ| ≤ c := by
  have := stepLaw_isProbability hd
  have : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  have hF := integrable_orientedTerminalReward hd hσ F x
  have hG := integrable_orientedTerminalReward hd hσ G x
  rw [orientedTerminalValue, orientedTerminalValue, ← integral_sub hF hG]
  calc
    |∫ p, (F (σ p) (orientedPath x p (σ p)) - G (σ p) (orientedPath x p (σ p)))
        ∂(walkLaw d)|
        ≤ ∫ p, |F (σ p) (orientedPath x p (σ p)) - G (σ p) (orientedPath x p (σ p))|
          ∂(walkLaw d) := abs_integral_le_integral_abs
    _ ≤ ∫ _p : ℕ → Fin d × Bool, c ∂(walkLaw d) :=
      integral_mono (hF.sub hG).abs (integrable_const c) (fun p => hdiff _ (hσ.1 p) _)
    _ = c := by simp

/-- The finite-horizon stopping value is Lipschitz in rewards restricted to
    times at or before the horizon. -/
theorem abs_orientedStoppingSup_sub_le_of_le (hd : 1 ≤ d) (F G : ℕ → Site d → ℝ)
    (n : ℕ) (x : Site d) {c M : ℝ}
    (hFb : ∀ k y, |F k y| ≤ M) (hGb : ∀ k y, |G k y| ≤ M)
    (hdiff : ∀ k ≤ n, ∀ y, |F k y - G k y| ≤ c) :
    |orientedStoppingSup d F n x - orientedStoppingSup d G n x| ≤ c := by
  have hbF := bddAbove_orientedTerminalValues hd F n x hFb
  have hbG := bddAbove_orientedTerminalValues hd G n x hGb
  have hneF := orientedTerminalValues_nonempty d F n x
  have hneG := orientedTerminalValues_nonempty d G n x
  have key : ∀ (F' G' : ℕ → Site d → ℝ),
      BddAbove (orientedTerminalValues d G' n x) →
      (orientedTerminalValues d F' n x).Nonempty →
      (∀ k ≤ n, ∀ y, |F' k y - G' k y| ≤ c) →
      orientedStoppingSup d F' n x ≤ orientedStoppingSup d G' n x + c := by
    intro F' G' hb hne hd'
    refine csSup_le hne ?_
    rintro a ⟨σ, hσ, rfl⟩
    have h1 : orientedTerminalValue G' x σ ≤ orientedStoppingSup d G' n x :=
      le_csSup hb ⟨σ, hσ, rfl⟩
    have h2 := abs_orientedTerminalValue_sub_le_of_le hd hσ F' G' x hd'
    have := (abs_sub_le_iff.mp h2).1
    linarith
  have h1 := key F G hbG hneF hdiff
  have h2 := key G F hbF hneG (fun k hk y => by
    rw [abs_sub_comm]; exact hdiff k hk y)
  rw [abs_sub_le_iff]
  constructor <;> linarith

end Parking
