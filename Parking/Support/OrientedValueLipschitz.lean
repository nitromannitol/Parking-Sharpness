/-
The discrete optimal-stopping value is `1`-Lipschitz in its terminal reward for
the supremum norm.

This is what makes the extended continuous mapping theorem applicable to the
values of `parking.tex:3199-3203`: the map that sends a reward to the value of
the discrete problem is continuous, uniformly in the horizon and in the
starting point, so the local uniform hypothesis of the extended theorem follows
from the convergence of the values at a single fixed reward.

There is no junk value to worry about on the discrete side: a bounded stopping
rule reads finitely many directions, so its terminal reward is integrable
whatever the reward field (`Parking.integrable_orientedTerminalReward`).
-/
import Parking.Support.OrientedTerminal

open MeasureTheory

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- The expected terminal reward is `1`-Lipschitz in the reward, rule by rule. -/
theorem abs_orientedTerminalValue_sub_le (hd : 1 ≤ d) {n : ℕ}
    {σ : (ℕ → Fin d × Bool) → ℕ} (hσ : IsStoppingTimeLE n σ) (F G : ℕ → Site d → ℝ)
    (x : Site d) {c : ℝ} (hdiff : ∀ (k : ℕ) (y : Site d), |F k y - G k y| ≤ c) :
    |orientedTerminalValue F x σ - orientedTerminalValue G x σ| ≤ c := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  have hF := integrable_orientedTerminalReward hd hσ F x
  have hG := integrable_orientedTerminalReward hd hσ G x
  have hsub : orientedTerminalValue F x σ - orientedTerminalValue G x σ
      = ∫ p, (F (σ p) (orientedPath x p (σ p)) - G (σ p) (orientedPath x p (σ p)))
        ∂(walkLaw d) := by
    rw [orientedTerminalValue, orientedTerminalValue, ← integral_sub hF hG]
  rw [hsub]
  calc |∫ p, (F (σ p) (orientedPath x p (σ p)) - G (σ p) (orientedPath x p (σ p)))
          ∂(walkLaw d)|
      ≤ ∫ p, |F (σ p) (orientedPath x p (σ p)) - G (σ p) (orientedPath x p (σ p))|
          ∂(walkLaw d) := abs_integral_le_integral_abs
    _ ≤ ∫ _p : ℕ → Fin d × Bool, c ∂(walkLaw d) :=
        integral_mono (hF.sub hG).abs (integrable_const c) (fun p => hdiff _ _)
    _ = c := by simp

/-- A bound on the reward bounds every rule's value from below as well. -/
theorem neg_le_orientedTerminalValue (hd : 1 ≤ d) {n : ℕ}
    {σ : (ℕ → Fin d × Bool) → ℕ} (hσ : IsStoppingTimeLE n σ) (F : ℕ → Site d → ℝ)
    (x : Site d) {M : ℝ} (hbound : ∀ (k : ℕ) (y : Site d), |F k y| ≤ M) :
    |orientedTerminalValue F x σ| ≤ M := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  have hF := integrable_orientedTerminalReward hd hσ F x
  calc |orientedTerminalValue F x σ|
      ≤ ∫ p, |F (σ p) (orientedPath x p (σ p))| ∂(walkLaw d) := abs_integral_le_integral_abs
    _ ≤ ∫ _p : ℕ → Fin d × Bool, M ∂(walkLaw d) :=
        integral_mono hF.abs (integrable_const M) (fun p => hbound _ _)
    _ = M := by simp

/-- The set of values of the bounded rules is bounded above by any bound on the
reward. -/
theorem bddAbove_orientedTerminalValues (hd : 1 ≤ d) (F : ℕ → Site d → ℝ) (n : ℕ)
    (x : Site d) {M : ℝ} (hbound : ∀ (k : ℕ) (y : Site d), |F k y| ≤ M) :
    BddAbove (orientedTerminalValues d F n x) := by
  refine ⟨M, ?_⟩
  rintro a ⟨σ, hσ, rfl⟩
  exact le_of_abs_le (neg_le_orientedTerminalValue hd hσ F x hbound)

/-- **The value of the discrete optimal-stopping problem is `1`-Lipschitz in
the terminal reward for the supremum norm.**  The bound is uniform in the
horizon and in the starting point. -/
theorem abs_orientedStoppingSup_sub_le (hd : 1 ≤ d) (F G : ℕ → Site d → ℝ) (n : ℕ)
    (x : Site d) {c M : ℝ}
    (hFb : ∀ (k : ℕ) (y : Site d), |F k y| ≤ M) (hGb : ∀ (k : ℕ) (y : Site d), |G k y| ≤ M)
    (hdiff : ∀ (k : ℕ) (y : Site d), |F k y - G k y| ≤ c) :
    |orientedStoppingSup d F n x - orientedStoppingSup d G n x| ≤ c := by
  have hbF := bddAbove_orientedTerminalValues hd F n x hFb
  have hbG := bddAbove_orientedTerminalValues hd G n x hGb
  have hneF := orientedTerminalValues_nonempty d F n x
  have hneG := orientedTerminalValues_nonempty d G n x
  have key : ∀ (F' G' : ℕ → Site d → ℝ),
      BddAbove (orientedTerminalValues d G' n x) →
      (orientedTerminalValues d F' n x).Nonempty →
      (∀ (k : ℕ) (y : Site d), |F' k y - G' k y| ≤ c) →
      orientedStoppingSup d F' n x ≤ orientedStoppingSup d G' n x + c := by
    intro F' G' hb hne hd'
    refine csSup_le hne ?_
    rintro a ⟨σ, hσ, rfl⟩
    have h1 : orientedTerminalValue G' x σ ≤ orientedStoppingSup d G' n x :=
      le_csSup hb ⟨σ, hσ, rfl⟩
    have h2 := abs_orientedTerminalValue_sub_le hd hσ F' G' x hd'
    have := (abs_sub_le_iff.mp h2).1
    linarith
  have h1 := key F G hbG hneF hdiff
  have h2 := key G F hbF hneG (fun k y => by
    rw [abs_sub_comm]; exact hdiff k y)
  rw [abs_sub_le_iff]
  constructor <;> linarith

end Parking

end
