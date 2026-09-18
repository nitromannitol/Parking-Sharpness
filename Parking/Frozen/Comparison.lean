/-
Theorem 4.1 of parking.tex, frozen.  `parking.tex:879-885` (label
`thm:comparison`):

  "Fix an integer-valued initial configuration $\eta$.  For every $n\geq0$ and
   $x\in\Z^d$, $u_n(x)\leq\E[U_n(x)\mid\eta]$."

Conditioning on `η` is integration over the stacks and the uniform variables
with `η` held fixed, which is a version of the conditional expectation because
the law of the data is a product.
-/
import Parking.Support.Comparison

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.comparison (d : ℕ) (hd : 1 ≤ d) (η : Parking.Site d → ℤ)
    (n : ℕ) (x : Parking.Site d) :
    Parking.u (fun y => ((η y : ℤ) : ℝ)) n x ≤ Parking.meanUgiven d η n x
-- FROZEN-STATEMENT-END
:= Parking.comparison_of_labelOrder hd η n x
