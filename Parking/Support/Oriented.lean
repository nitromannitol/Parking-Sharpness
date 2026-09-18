/-
The oriented walk of Section 10 of `parking.tex`: its layer laws, its
truncated Green function, and the binomial law that identifies the layer law
in dimension two.

`orientedKern d y x` is `\vec P(y, x)`, which is `1/d` when `x = y - e_i` for
some `i` and zero otherwise.  `orientedLayer d l` is `\vec p_l = \vec P^l(0,\cdot)`.
In dimension two the number of steps in direction `-e_1` identifies the
support of `\vec p_l` with `{0,…,l}` and `\vec p_l` with the binomial law of
`l` trials and success probability `1/2`; `binomLaw` is that law, extended by
zero to the integers.
-/
import Parking.Support.Kernel

noncomputable section

namespace Parking

open LatticeProb

/-- `\vec P(y, x)`, the oriented transition probability. -/
def orientedKern (d : ℕ) (y x : Site d) : ℝ :=
  if ∃ i : Fin d, x = y - unit i then (d : ℝ)⁻¹ else 0

/-- `\vec p_l = \vec P^l(0, \cdot)`. -/
def orientedLayer (d : ℕ) : ℕ → Site d → ℝ
  | 0 => fun x => if x = 0 then 1 else 0
  | l + 1 => fun x => ∑ y ∈ boxFinset x 1, orientedLayer d l y * orientedKern d y x

/-- `g_n = ∑_{l<n} \vec p_l`. -/
def orientedGreen (d : ℕ) (n : ℕ) (x : Site d) : ℝ :=
  ∑ l ∈ Finset.range n, orientedLayer d l x

/-- The binomial law of `l` trials and success probability `1/2`, extended by
zero to the integers. -/
def binomLaw (l : ℕ) (j : ℤ) : ℝ :=
  (if 0 ≤ j then (Nat.choose l j.toNat : ℝ) else 0) / 2 ^ l

end Parking

end
