/-
Lemma 9.3 of parking.tex, frozen.  `parking.tex:2184-2189` (label
`lem:nearest-close-pair`), in the setting of `parking.tex:1835-1866`:

  "For every $t\geq0$ and distinct $x,z\in\Z^d$,
   $\P(H_t(x)=H_t(z)=1)\leq2p\,h_t$."
-/
import Parking.Support.ClosePair

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.nearest_close_pair (d : ℕ) (hd : 5 ≤ d) (p : ℝ)
    (hp : 0 < p) (hp4 : p ≤ 1 / 4) (t : ℕ) (x z : Parking.Site d) (hxz : x ≠ z) :
    ((Parking.law d (Parking.threePointLaw p))
        {ω | Parking.H ω t x = 1 ∧ Parking.H ω t z = 1}).toReal
      ≤ 2 * p * Parking.holeProb d (Parking.threePointLaw p) t
-- FROZEN-STATEMENT-END
:= Parking.close_pair (by omega) hp hp4 t x z hxz
