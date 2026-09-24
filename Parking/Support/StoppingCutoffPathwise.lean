/-
**The pathwise cutoff-to-true bound for the stopping-value summand, at an arbitrary starting
site, with the bounding constant supplied by the CALLER's own cutoff at a second radius.**

`Parking.abs_stoppingSup_sub_cutoffStoppingSup_le'` (`Parking/Support/SpatialStoppingCutoff.lean`)
needs a GLOBAL deterministic bound `M` on the reward, but the true reward
`F k y := -Parking.linPotential η (n₀-k) y`, as it arises in the randomized discrete
cutoff-to-true bound, is only a.s. LOCALLY finite (unbounded as `y` ranges over all of
`Site d`).  The fix is a DETERMINISTIC (not probabilistic) fact about the simple random walk
itself: `Parking.graphNorm (Parking.walkPath x p k - x) ≤ k` for EVERY path `p` (each step
changes `Parking.graphNorm`-distance from the start by at most `1`, `LatticeProb.graphNorm_add_le`
+ `graphNorm_stepVec`), so a stopping rule bounded by the horizon `n` can NEVER see the reward
outside `Parking.graphNorm`-radius `n` of the start: `Parking.stoppingSup d F n z0` is UNCHANGED
by cutting `F` at ANY radius `A₂ ≥ n` (`Parking.stoppingSup_eq_cutoffStoppingSup_of_le`, no
probability, no `M`).

This turns the caller's own problem into an application of
`Parking.abs_stoppingSup_sub_cutoffStoppingSup_le'` to a reward that is genuinely globally
bounded: `Parking.cutoffReward F' A₂` (for the reachability radius `A₂ ≥ n`), which is compactly
supported and hence automatically bounded by ITS OWN sup over the finite box (a RANDOM but FINITE
quantity, tail-controlled by `Parking.exists_linPotential_maximal_tail_time_shift`,
`Parking/Support/LinPotentialMaximalTime.lean`).
`Parking.abs_stoppingSup_sub_cutoffStoppingSup_pathwise` is the resulting pathwise (`M` still a
hypothesis, supplied by the caller) comparison at the TARGET cutoff radius `A ≤ A₂`, via the
cutoff-composition identity `Parking.cutoffReward_cutoffReward_eq_of_le`.  This is the pathwise
lemma used for the randomized wrapping: the caller instantiates `M` at the tail-controlled
`Finset.sup'` of `Parking.linPotential` over the finite time-space grid
`(Finset.range (n+1)) ×ˢ (Parking.boxFinset 0 A₂)` and combines with
`Parking.exists_linPotential_maximal_tail_time_shift`'s tail bound via a good/bad event split.
With the concrete rate choice `A(R) := ⌈R³⌉₊`, `M₀(R) := n₀(R)·R`, both the pathwise error and
the exceptional-event probability vanish as `R → ∞`; this final `Tendsto` assembly is carried
out in `Parking/Support/StoppingCutoffRandomized.lean`.

No `External` is registered or consumed: every theorem here is proved, not cited.
-/
import Parking.Support.LinPotentialMaximal
import Parking.Support.SpatialStoppingCutoff
import Parking.Support.StoppingShift

noncomputable section

namespace Parking

open MeasureTheory LatticeProb Finset

variable {d : ℕ}

/-! ### The walk cannot leave a `graphNorm`-ball of its own horizon: a deterministic fact -/

theorem graphNorm_stepVec (b : Fin d × Bool) : Parking.graphNorm (stepVec b) = 1 := by
  unfold stepVec Parking.graphNorm LatticeProb.unit
  by_cases h : b.2
  · simp [h, Pi.single_apply]
    rw [Finset.sum_eq_single b.1] <;> simp
  · simp [h, Pi.single_apply]
    rw [Finset.sum_eq_single b.1] <;> simp

/-- **The walk's `graphNorm`-distance from its own start is at most the elapsed step count.**
Each step (`Parking.stepVec`) changes exactly one coordinate by `±1`, so `Parking.graphNorm`
increases by at most `1` per step (`LatticeProb.graphNorm_add_le`); induction on `k`. -/
theorem graphNorm_walkPath_le (x : Site d) (p : ℕ → Fin d × Bool) (k : ℕ) :
    Parking.graphNorm (walkPath x p k - x) ≤ k := by
  induction k with
  | zero => simp [walkPath, Parking.graphNorm]
  | succ k ih =>
      rw [walkPath]
      have heq : walkPath x p k + stepVec (p k) - x = (walkPath x p k - x) + stepVec (p k) := by
        abel
      rw [heq]
      calc Parking.graphNorm (walkPath x p k - x + stepVec (p k))
          ≤ Parking.graphNorm (walkPath x p k - x) + Parking.graphNorm (stepVec (p k)) :=
            LatticeProb.graphNorm_add_le _ _
        _ ≤ k + 1 := by rw [graphNorm_stepVec]; omega

/-- **A reward's value at any site the walk can reach within a horizon `n` is unchanged by a
cutoff at radius `A ≥ n`**, for one fixed stopping rule. -/
theorem terminalValue_eq_cutoffReward_of_le (F : ℕ → Site d → ℝ) {A : ℝ} {n : ℕ}
    (hAn : (n : ℝ) ≤ A) {σ : (ℕ → Fin d × Bool) → ℕ} (hσ : IsStoppingTimeLE n σ) :
    terminalValue F (0 : Site d) σ = terminalValue (cutoffReward F A) (0 : Site d) σ := by
  unfold terminalValue
  congr 1
  funext p
  have h1 : Parking.graphNorm (walkPath (0 : Site d) p (σ p) - 0) ≤ σ p :=
    graphNorm_walkPath_le 0 p (σ p)
  rw [sub_zero] at h1
  have h2 : σ p ≤ n := hσ.1 p
  have h3 : (Parking.graphNorm (walkPath (0 : Site d) p (σ p)) : ℝ) ≤ A := by
    have h4 : (Parking.graphNorm (walkPath (0 : Site d) p (σ p)) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast h1.trans h2
    linarith
  rw [cutoffReward_eq_of_le F A (σ p) _ h3]

/-- **`Parking.stoppingSup` equals its own cutoff once the cutoff radius reaches the horizon.**
No probability, no bound `M`: a PATHWISE consequence of the walk's own reachability. -/
theorem stoppingSup_eq_cutoffStoppingSup_of_le (F : ℕ → Site d → ℝ) {A : ℝ} {n : ℕ}
    (hAn : (n : ℝ) ≤ A) :
    stoppingSup d F n (0 : Site d) = cutoffStoppingSup F A n := by
  unfold stoppingSup cutoffStoppingSup
  congr 1
  unfold terminalValues
  ext a
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ, hσ, terminalValue_eq_cutoffReward_of_le F hAn hσ⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ, hσ, (terminalValue_eq_cutoffReward_of_le F hAn hσ).symm⟩

/-! ### Composing two cutoffs -/

/-- **Composing two cutoffs at radii `A ≤ A₂` is the cutoff at the smaller radius.** -/
theorem cutoffReward_cutoffReward_eq_of_le (F : ℕ → Site d → ℝ) {A A2 : ℝ} (hA : A ≤ A2) :
    cutoffReward (cutoffReward F A2) A = cutoffReward F A := by
  funext k z
  unfold cutoffReward
  by_cases h : (Parking.graphNorm z : ℝ) ≤ A
  · rw [if_pos h, if_pos h, if_pos (h.trans hA)]
  · rw [if_neg h, if_neg h]

/-! ### The pathwise cutoff-to-true bound, assembled -/

/-- **The pathwise cutoff-to-true bound for the stopping-value summand, at an arbitrary
starting site `z0`.**  The bounding constant `M` is supplied by the caller as a bound on the
reward cut off at a SECOND (larger, or equal) radius `A₂ ≥ n`: since `Parking.cutoffReward F' A2`
is compactly supported, such an `M` is always available (e.g. its own finite sup over a finite
grid), unlike a global bound on the unbounded true reward.  Used by the randomized wrapping
(`Parking/Support/StoppingCutoffRandomized.lean`), which instantiates `M` at the
tail-controlled `Finset.sup'` of `Parking.linPotential` supplied by
`Parking.exists_linPotential_maximal_tail_time_shift`
(`Parking/Support/LinPotentialMaximalTime.lean`). -/
theorem abs_stoppingSup_sub_cutoffStoppingSup_pathwise (hd1 : 1 ≤ d) (F : ℕ → Site d → ℝ)
    (z0 : Site d) {A A2 : ℝ} (hA : 0 < A) {n : ℕ} (hnA2 : (n : ℝ) ≤ A2) (hAA2 : A ≤ A2)
    {M : ℝ} (hM : ∀ k y, |cutoffReward (fun k y => F k (z0 + y)) A2 k y| ≤ M) :
    |stoppingSup d F n z0 - cutoffStoppingSup (fun k y => F k (z0 + y)) A n|
      ≤ M * ((n : ℝ) * d ^ 2 / A ^ 2) := by
  set F' : ℕ → Site d → ℝ := fun k y => F k (z0 + y) with hF'def
  have hshift : stoppingSup d F n z0 = stoppingSup d F' n (0 : Site d) := stoppingSup_eq_shift F n z0
  have heq1 : stoppingSup d F' n (0 : Site d) = cutoffStoppingSup F' A2 n :=
    stoppingSup_eq_cutoffStoppingSup_of_le F' hnA2
  have heq2 : cutoffStoppingSup (cutoffReward F' A2) A n = cutoffStoppingSup F' A n := by
    unfold cutoffStoppingSup
    rw [cutoffReward_cutoffReward_eq_of_le F' hAA2]
  have hbound := abs_stoppingSup_sub_cutoffStoppingSup_le' hd1 (cutoffReward F' A2) hA hM n
  rw [heq2] at hbound
  rw [hshift, heq1]
  exact hbound

end Parking

end
