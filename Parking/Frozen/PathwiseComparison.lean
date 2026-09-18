/-
Lemma 5.1 of parking.tex, frozen.  `parking.tex:966-975` (label
`lem:pathwise-comparison`):

  "For every $n\geq0$ and every $x\in\Z^d$,
   $|U_n(x)-w_n(x)-u_n(x)|\leq w_n^\star(x)$, and therefore
   $|U_n(x)-u_n(x)|\leq2\,w_n^\star(x)$."

Both bounds hold for every realization of the model.  As in `lem:parallel`,
whose identity the proof uses, the instructions of a realization are neighbours
of the site carrying them, since `ρ_j(y)` has the law `P(y,·)`
(`parking.tex:632-636`); without that the identity itself fails.
-/
import Parking.Support.Pathwise

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.pathwise_comparison (d : ℕ) (hd : 1 ≤ d) (ω : Parking.Data d)
    (hstep : ∀ q : Parking.Site d × ℕ, ω.2.1 q ∈ LatticeProb.nbrFinset q.1)
    (n : ℕ) (x : Parking.Site d) :
    |(Parking.U ω n x : ℝ) - Parking.wErr ω n x - Parking.uOf ω n x|
        ≤ Parking.wStar ω n x ∧
      |(Parking.U ω n x : ℝ) - Parking.uOf ω n x| ≤ 2 * Parking.wStar ω n x
-- FROZEN-STATEMENT-END
:= Parking.pathwise_comparison_of_labelOrder hd hstep n x
