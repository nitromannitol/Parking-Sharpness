/-
Lemma 3.4 of parking.tex, frozen.  `parking.tex:712-717` (label
`lem:tagged-monotonicity`):

  "In the coupling of Lemma 3.3, every particle present in both processes stays
   active in the process started from $\widetilde\eta$ at least as long as in
   the process started from $\eta$."

"At least as long" is the implication at every fixed round.  The labels of the
particles present in both processes are exactly the labels active in the first
one; a label active in the first process is a particle of both, so the
quantifier over all labels states no more than the paper's.
-/
import Parking.Support.Coupling

-- The dimension bound is part of the standing setting of the paper, not of the
-- argument; the proof does not read it.
set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.tagged_monotonicity (d : ℕ) (hd : 1 ≤ d) (D : Parking.PDriver d)
    (x₀ : Parking.Site d) (t : ℕ) (p : Parking.Label d) :
    (Parking.pState D t).active p = true →
      (Parking.pState (Parking.addParticleDriver x₀ D) t).active p = true
-- FROZEN-STATEMENT-END
:= fun h => ((Parking.tagged_invariant D x₀ t).1 p h).1
