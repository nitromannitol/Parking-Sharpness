/-
**Truncating a stopping rule to a smaller horizon is again a stopping rule for that smaller
horizon.**

Infrastructure toward the TEMPORAL half of the Dynkin-decomposition transfer lemma
(`Parking.Generic.StoppingModulus` has the SPATIAL half): comparing
`Parking.stoppingSup d F n' x` to `Parking.stoppingSup d F n x` for `n ≤ n'` needs, for every
rule `σ` admissible at horizon `n'`, a rule admissible at horizon `n` close to it — the standard
choice is the TRUNCATION `σ ⊓ n` (`fun p => min (σ p) n`).  This module proves that truncation
is again a genuine stopping rule, `IsStoppingTimeLE n (σ ⊓ n)`, the fact on which every
subsequent step of the temporal transfer is built.  Bounding the reward gap on the untruncated
event is a separate step; it needs a walk-displacement estimate,
`Parking.measureReal_sup_walkPath_graphNorm_le` (`Parking/Support/WalkMaximal.lean`), and is not
carried out in this module.
-/
import Parking.Support.Walk

noncomputable section

namespace Parking

variable {d : ℕ}

/-- **Truncating a stopping rule at a smaller horizon `n` is again a stopping rule bounded by
`n`.**  The first clause is immediate (`min _ n ≤ n`).  For the second: if `σ p ⊓ n = σ p`
(i.e. `σ p ≤ n`), agreement of `p, q` up to `σ p ⊓ n = σ p` is exactly the hypothesis
`σ`'s own stopping property needs, giving `σ q = σ p` and hence `σ q ⊓ n = σ p ⊓ n`
directly.  If instead `σ p ⊓ n = n` (i.e. `σ p > n`), agreement up to `n` gives, by `σ`'s own
stopping property read from `q`'s side, that `σ q < n` would force `σ p = σ q < n`,
contradicting `σ p > n`; so `σ q ≥ n`, i.e. `σ q ⊓ n = n = σ p ⊓ n`. -/
theorem isStoppingTimeLE_min {n n' : ℕ} {σ : (ℕ → Fin d × Bool) → ℕ}
    (hσ : IsStoppingTimeLE n' σ) (_hn : n ≤ n') :
    IsStoppingTimeLE n (fun p => min (σ p) n) := by
  refine ⟨fun p => min_le_right _ _, fun p q hagree => ?_⟩
  dsimp only at hagree ⊢
  by_cases hp : σ p ≤ n
  · have hmin : min (σ p) n = σ p := min_eq_left hp
    rw [hmin] at hagree
    have hσq : σ q = σ p := hσ.2 p q hagree
    rw [hσq]
  · have hp' : n < σ p := not_le.mp hp
    have hmin : min (σ p) n = n := min_eq_right hp'.le
    rw [hmin] at hagree
    by_contra hne
    have hminq : min (σ q) n ≠ n := fun h => hne (h.trans hmin.symm)
    have hqlt : σ q < n := by
      by_contra hcon
      exact hminq (min_eq_right (not_lt.mp hcon))
    have hagree' : ∀ j < σ q, q j = p j := fun j hj => (hagree j (hj.trans_le hqlt.le)).symm
    have hσp : σ p = σ q := hσ.2 q p hagree'
    omega

end Parking

end
