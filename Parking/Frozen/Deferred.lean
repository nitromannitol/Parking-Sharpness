/-
Lemma 3.2 of parking.tex, frozen.  `parking.tex:659-667` (label `lem:deferred`):

  "For every $n\geq0$, every $y$ and $x$ in $\Z^d$ and every $j\geq1$, the event
   $\{U_n(y)\geq j\}$ is measurable with respect to the initial configuration
   together with the instructions other than $\rho_j(y)$.  Consequently
   $\E[\one\{U_n(y)\geq j\}\one\{\rho_j(y)=x\}\mid\eta]
    =P(y,x)\,\P(U_n(y)\geq j\mid\eta)$."

The paper's instructions are numbered from one and ours from zero, so
$\rho_{j+1}(y)$ is `ω.2.1 (y, j)` and the event $\{U_n(y)\geq j+1\}$ is
`j + 1 ≤ U ω n y`.  The measurability clause is stated pathwise, as the
independence of the event from the one instruction it excludes; that is what
the paper's proof establishes and it is the form the second clause uses.  It
holds for the realizations of the model, whose instructions are neighbours of
the site carrying them, since `ρ_j(y)` has the law `P(y,·)`: without that, a
particle can stand at a site it is not a candidate for and read an instruction
of an index the round does not count, and the state after a round is then no
longer a function of the instructions the odometer has reached.  The second
clause needs no such hypothesis, because the law of the stacks is carried by
the realizations that satisfy it.
Conditioning on `η` is integration over the stacks and the uniform variables
with `η` held fixed, which is a version of the conditional expectation because
the law of the data is a product.
-/
import Parking.Support.DeferredIntegral

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.deferred (d : ℕ) (hd : 1 ≤ d) (n : ℕ) (y x : Site d) (j : ℕ) :
    (∀ ω ω' : Parking.Data d,
        (∀ q : Parking.Site d × ℕ, ω.2.1 q ∈ LatticeProb.nbrFinset q.1) →
        (∀ q : Parking.Site d × ℕ, ω'.2.1 q ∈ LatticeProb.nbrFinset q.1) →
        ω.1 = ω'.1 → ω.2.2 = ω'.2.2 →
        (∀ q : Parking.Site d × ℕ, q ≠ (y, j) → ω.2.1 q = ω'.2.1 q) →
        (j + 1 ≤ Parking.U ω n y ↔ j + 1 ≤ Parking.U ω' n y)) ∧
    ∀ η : Parking.Site d → ℤ,
      Parking.probGiven d η {ω | j + 1 ≤ Parking.U ω n y ∧ ω.2.1 (y, j) = x} =
        Parking.kern d y x * Parking.probGiven d η {ω | j + 1 ≤ Parking.U ω n y}
-- FROZEN-STATEMENT-END
:= ⟨fun ω ω' hs hs' heta hrank hne =>
      Parking.odometer_ge_congr (D := Parking.toDriver ω) (D' := Parking.toDriver ω')
        (Parking.stepsToNeighbour_of_mem hs) (Parking.stepsToNeighbour_of_mem hs')
        heta hrank y j n hne,
    fun η => Parking.deferred_factorization hd n y x j η⟩
