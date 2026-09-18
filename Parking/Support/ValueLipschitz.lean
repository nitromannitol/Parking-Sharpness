/-
The discrete optimal-stopping value of the SIMPLE RANDOM WALK (`Parking.stoppingSup`,
`Parking/Support/Terminal.lean`) is `1`-Lipschitz in its terminal reward for the supremum
norm.  Transposed from `Parking/Support/OrientedValueLipschitz.lean`, with
`terminalValue`/`terminalValues`/`stoppingSup`/`walkPath` in place of
`orientedTerminalValue`/`orientedTerminalValues`/`orientedStoppingSup`/`orientedPath`.

This is what makes the extended continuous mapping theorem
(`Parking.Support.ExtendedMapping.extended_continuous_mapping`, which is general-purpose and
needs no transposition) applicable to the SPATIAL value transfer, just as it is for the
ORIENTED node: the map that sends a reward to the value of the discrete problem is continuous,
uniformly in the horizon and in the starting point, so the local uniform hypothesis of the
extended theorem (`Parking.Support.ExtendedMapping.locallyUniform_of_lipschitz`) follows from
the convergence of the values at a single fixed reward, i.e. from
`Parking.External.SpatialStoppingStability` alone.

There is no junk value to worry about on the discrete side, exactly as for the oriented walk:
a bounded stopping rule reads finitely many directions, so its terminal reward is integrable
whatever the reward field (`Parking.integrable_terminalReward`).
-/
import Parking.Support.Terminal

open MeasureTheory

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- The terminal reward of a bounded stopping rule reads only the directions the rule may
read.  Transposed from `Parking.orientedTerminalReward_congr`. -/
theorem terminalReward_congr {n : ℕ} {σ : (ℕ → Fin d × Bool) → ℕ}
    (hσ : IsStoppingTimeLE n σ) (F : ℕ → Site d → ℝ) (x : Site d)
    {p q : ℕ → Fin d × Bool} (h : ∀ i, i < n → p i = q i) :
    F (σ p) (walkPath x p (σ p)) = F (σ q) (walkPath x q (σ q)) := by
  have hle : σ p ≤ n := hσ.1 p
  have hsame : σ q = σ p := hσ.2 p q (fun j hj => h j (lt_of_lt_of_le hj hle))
  rw [hsame, walkPath_congr x (fun i hi => h i (lt_of_lt_of_le hi hle))]

/-- **The terminal reward of a bounded rule is always integrable**, whatever the reward
field.  Transposed from `Parking.integrable_orientedTerminalReward`. -/
theorem integrable_terminalReward (hd : 1 ≤ d) {n : ℕ} {σ : (ℕ → Fin d × Bool) → ℕ}
    (hσ : IsStoppingTimeLE n σ) (F : ℕ → Site d → ℝ) (x : Site d) :
    Integrable (fun p => F (σ p) (walkPath x p (σ p))) (walkLaw d) :=
  integrable_of_finite_dependence hd n _ (fun _ _ h => terminalReward_congr hσ F x h)

/-- The expected terminal reward is `1`-Lipschitz in the reward, rule by rule.  Transposed
from `Parking.abs_orientedTerminalValue_sub_le`. -/
theorem abs_terminalValue_sub_le (hd : 1 ≤ d) {n : ℕ} {σ : (ℕ → Fin d × Bool) → ℕ}
    (hσ : IsStoppingTimeLE n σ) (F G : ℕ → Site d → ℝ) (x : Site d) {c : ℝ}
    (hdiff : ∀ (k : ℕ) (y : Site d), |F k y - G k y| ≤ c) :
    |terminalValue F x σ - terminalValue G x σ| ≤ c := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  have hF := integrable_terminalReward hd hσ F x
  have hG := integrable_terminalReward hd hσ G x
  have hsub : terminalValue F x σ - terminalValue G x σ
      = ∫ p, (F (σ p) (walkPath x p (σ p)) - G (σ p) (walkPath x p (σ p))) ∂(walkLaw d) := by
    rw [terminalValue, terminalValue, ← integral_sub hF hG]
  rw [hsub]
  calc |∫ p, (F (σ p) (walkPath x p (σ p)) - G (σ p) (walkPath x p (σ p))) ∂(walkLaw d)|
      ≤ ∫ p, |F (σ p) (walkPath x p (σ p)) - G (σ p) (walkPath x p (σ p))| ∂(walkLaw d) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _p : ℕ → Fin d × Bool, c ∂(walkLaw d) :=
        integral_mono (hF.sub hG).abs (integrable_const c) (fun p => hdiff _ _)
    _ = c := by simp

/-- A bound on the reward bounds every rule's value.  Transposed from
`Parking.neg_le_orientedTerminalValue`. -/
theorem abs_terminalValue_le (hd : 1 ≤ d) {n : ℕ} {σ : (ℕ → Fin d × Bool) → ℕ}
    (hσ : IsStoppingTimeLE n σ) (F : ℕ → Site d → ℝ) (x : Site d) {M : ℝ}
    (hbound : ∀ (k : ℕ) (y : Site d), |F k y| ≤ M) :
    |terminalValue F x σ| ≤ M := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  have hF := integrable_terminalReward hd hσ F x
  calc |terminalValue F x σ|
      ≤ ∫ p, |F (σ p) (walkPath x p (σ p))| ∂(walkLaw d) := abs_integral_le_integral_abs
    _ ≤ ∫ _p : ℕ → Fin d × Bool, M ∂(walkLaw d) :=
        integral_mono hF.abs (integrable_const M) (fun p => hbound _ _)
    _ = M := by simp

/-- The set of values of the bounded rules is bounded above by any bound on the reward.
Transposed from `Parking.bddAbove_orientedTerminalValues`. -/
theorem bddAbove_terminalValues (hd : 1 ≤ d) (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d)
    {M : ℝ} (hbound : ∀ (k : ℕ) (y : Site d), |F k y| ≤ M) :
    BddAbove (terminalValues d F n x) := by
  refine ⟨M, ?_⟩
  rintro a ⟨σ, hσ, rfl⟩
  exact le_of_abs_le (abs_terminalValue_le hd hσ F x hbound)

/-- **The value of the discrete optimal-stopping problem for the SIMPLE RANDOM WALK is
`1`-Lipschitz in the terminal reward for the supremum norm.**  The bound is uniform in the
horizon and in the starting point.  Transposed from `Parking.abs_orientedStoppingSup_sub_le`. -/
theorem abs_stoppingSup_sub_le (hd : 1 ≤ d) (F G : ℕ → Site d → ℝ) (n : ℕ) (x : Site d)
    {c M : ℝ} (hFb : ∀ (k : ℕ) (y : Site d), |F k y| ≤ M)
    (hGb : ∀ (k : ℕ) (y : Site d), |G k y| ≤ M)
    (hdiff : ∀ (k : ℕ) (y : Site d), |F k y - G k y| ≤ c) :
    |stoppingSup d F n x - stoppingSup d G n x| ≤ c := by
  have hbF := bddAbove_terminalValues hd F n x hFb
  have hbG := bddAbove_terminalValues hd G n x hGb
  have hneF := terminalValues_nonempty d F n x
  have hneG := terminalValues_nonempty d G n x
  have key : ∀ (F' G' : ℕ → Site d → ℝ),
      BddAbove (terminalValues d G' n x) →
      (terminalValues d F' n x).Nonempty →
      (∀ (k : ℕ) (y : Site d), |F' k y - G' k y| ≤ c) →
      stoppingSup d F' n x ≤ stoppingSup d G' n x + c := by
    intro F' G' hb hne hd'
    refine csSup_le hne ?_
    rintro a ⟨σ, hσ, rfl⟩
    have h1 : terminalValue G' x σ ≤ stoppingSup d G' n x := le_csSup hb ⟨σ, hσ, rfl⟩
    have h2 := abs_terminalValue_sub_le hd hσ F' G' x hd'
    have := (abs_sub_le_iff.mp h2).1
    linarith
  have h1 := key F G hbG hneF hdiff
  have h2 := key G F hbF hneG (fun k y => by rw [abs_sub_comm]; exact hdiff k y)
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The expected terminal reward is `1`-Lipschitz in the reward RESTRICTED to `k ≤ n`, rule
by rule: a bounded rule only ever reads its reward at `k = σ p ≤ n` (`hσ.1 p`), so only the
difference on that range matters, not on all of `ℕ`.  The `k ≤ n`-restricted form of
`abs_terminalValue_sub_le`, needed for the spatial-modulus transfer, where the reward's OWN
modulus is naturally stated only over the relevant time range. -/
theorem abs_terminalValue_sub_le_of_le (hd : 1 ≤ d) {n : ℕ} {σ : (ℕ → Fin d × Bool) → ℕ}
    (hσ : IsStoppingTimeLE n σ) (F G : ℕ → Site d → ℝ) (x : Site d) {c : ℝ}
    (hdiff : ∀ k ≤ n, ∀ (y : Site d), |F k y - G k y| ≤ c) :
    |terminalValue F x σ - terminalValue G x σ| ≤ c := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  have hF := integrable_terminalReward hd hσ F x
  have hG := integrable_terminalReward hd hσ G x
  have hsub : terminalValue F x σ - terminalValue G x σ
      = ∫ p, (F (σ p) (walkPath x p (σ p)) - G (σ p) (walkPath x p (σ p))) ∂(walkLaw d) := by
    rw [terminalValue, terminalValue, ← integral_sub hF hG]
  rw [hsub]
  calc |∫ p, (F (σ p) (walkPath x p (σ p)) - G (σ p) (walkPath x p (σ p))) ∂(walkLaw d)|
      ≤ ∫ p, |F (σ p) (walkPath x p (σ p)) - G (σ p) (walkPath x p (σ p))| ∂(walkLaw d) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _p : ℕ → Fin d × Bool, c ∂(walkLaw d) :=
        integral_mono (hF.sub hG).abs (integrable_const c) (fun p => hdiff (σ p) (hσ.1 p) _)
    _ = c := by simp

/-- **The `k ≤ n`-restricted form of `abs_stoppingSup_sub_le`**: the value of the discrete
optimal-stopping problem is `1`-Lipschitz in the reward's difference over `k ≤ n` alone (the
only range a rule bounded by `n` can read), given a GLOBAL bound on each reward (needed only
so the two sets of terminal values are bounded above, not to control the difference). -/
theorem abs_stoppingSup_sub_le_of_le (hd : 1 ≤ d) (F G : ℕ → Site d → ℝ) (n : ℕ) (x : Site d)
    {c M : ℝ} (hFb : ∀ (k : ℕ) (y : Site d), |F k y| ≤ M)
    (hGb : ∀ (k : ℕ) (y : Site d), |G k y| ≤ M)
    (hdiff : ∀ k ≤ n, ∀ (y : Site d), |F k y - G k y| ≤ c) :
    |stoppingSup d F n x - stoppingSup d G n x| ≤ c := by
  have hbF := bddAbove_terminalValues hd F n x hFb
  have hbG := bddAbove_terminalValues hd G n x hGb
  have hneF := terminalValues_nonempty d F n x
  have hneG := terminalValues_nonempty d G n x
  have key : ∀ (F' G' : ℕ → Site d → ℝ),
      BddAbove (terminalValues d G' n x) →
      (terminalValues d F' n x).Nonempty →
      (∀ k ≤ n, ∀ (y : Site d), |F' k y - G' k y| ≤ c) →
      stoppingSup d F' n x ≤ stoppingSup d G' n x + c := by
    intro F' G' hb hne hd'
    refine csSup_le hne ?_
    rintro a ⟨σ, hσ, rfl⟩
    have h1 : terminalValue G' x σ ≤ stoppingSup d G' n x := le_csSup hb ⟨σ, hσ, rfl⟩
    have h2 := abs_terminalValue_sub_le_of_le hd hσ F' G' x hd'
    have := (abs_sub_le_iff.mp h2).1
    linarith
  have h1 := key F G hbG hneF hdiff
  have h2 := key G F hbF hneG (fun k hk y => by rw [abs_sub_comm]; exact hdiff k hk y)
  rw [abs_sub_le_iff]
  constructor <;> linarith

end Parking

end
