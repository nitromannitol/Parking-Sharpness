/-
Lemma 3.1 of parking.tex, frozen.  `parking.tex:647-653` (label `lem:parallel`):

  "Let $U_n(x)$ be the number of steps taken from $x$ during the first $n$
   rounds.  Then $U_0=0$, and for every $n\geq0$ and every $x\in\Z^d$,
   $U_{n+1}(x)=(\eta(x)+\sum_y I_{y,x}(U_n(y)))^+$."

This is the identity that lets the odometer be computed from the stacks
alone; it holds for every realization of the model.  The instructions of the
model are neighbours of the site that carries them, since `ρ_j(y)` has the law
`P(y,·)` (`parking.tex:632-636`), and the identity needs that: a realization
whose instructions send particles to sites that are not neighbours breaks both
sides, since the arrivals at `x` in a round come from the neighbours of `x`
and a particle that has moved `t` times is within distance `t` of where it
started.  So the hypothesis `hstep` is part of what "realization" means here.
-/
import Parking.Support.Parallel

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.parallel {d : ℕ} (ω : Parking.Data d)
    (hstep : ∀ q : Parking.Site d × ℕ, ω.2.1 q ∈ LatticeProb.nbrFinset q.1) :
    (∀ x, Parking.U ω 0 x = 0) ∧
    ∀ (n : ℕ) (x : Parking.Site d),
      (Parking.U ω (n + 1) x : ℤ) =
        max 0 (ω.1 x + ∑ y ∈ LatticeProb.nbrFinset x,
          (LatticeProb.arrivals ω.2.1 y x (Parking.U ω n y) : ℤ))
-- FROZEN-STATEMENT-END
:= Parking.parallel_of_labelOrder (Parking.labelOrder d) hstep
