/-
Lemma 12.1 of parking.tex, frozen.  `parking.tex:3032-3037` (label
`lem:shift`), in the setting of `parking.tex:3024-3031` ("When $d=2$, the
number of steps in direction $-e_1$ identifies the support of $\vec p_\ell$
with $\{0,\ldots,\ell\}$.  Under this identification $\vec p_\ell$ is the
binomial law with $\ell$ trials and success probability $1/2$"):

  "If $d=2$, then for every integer $q$,
   $\sum_{\ell\geq0}\|\vec p_\ell(\cdot-q)-\vec p_\ell\|_2^2=4|q|$."

The layer law is `binomLaw`, the binomial law of `l` trials and success
probability `1/2` extended by zero to the integers.  Summability of both sums
is asserted alongside the identity, so that a divergent series cannot satisfy
it through the junk value of a nonsummable `tsum`.
-/
import Parking.Support.Shift

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.shift (q : ℤ) :
    (∀ l : ℕ, Summable fun j : ℤ =>
        (Parking.binomLaw l (j - q) - Parking.binomLaw l j) ^ 2) ∧
      Summable (fun l : ℕ => ∑' j : ℤ,
        (Parking.binomLaw l (j - q) - Parking.binomLaw l j) ^ 2) ∧
      ∑' l : ℕ, ∑' j : ℤ, (Parking.binomLaw l (j - q) - Parking.binomLaw l j) ^ 2
        = 4 * |(q : ℝ)|
-- FROZEN-STATEMENT-END
:= Parking.shift_energy q
