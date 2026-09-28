import Parking.Support.Oriented

/-!
# The binomial local central limit theorem

External input: the local central limit theorem for the simple symmetric walk on the
integers, with the error term the proof of `prop:oriented-scaling` uses.

The proof at `parking.tex:3177-3237` says, of the rescaled scenery of Step 1, "the binomial
local central limit theorem gives convergence of the convolved potentials". The convolved
potentials are sums over `O(n)` layers of the binomial kernel against the scenery, carrying
the prefactor `n^{-1/4}`, so the error of the kernel approximation is summed over the layers:
an error `C/m` at layer `m` is what the argument consumes, and an error `C/sqrt m` would not
do.

Writing `binomLaw m k` for the chance of `k` heads in `m` fair tosses, the sum of `m`
independent signs equals `j` exactly when the number of heads is `(j+m)/2`, which is an
integer precisely under the stated parity constraint. Without the parity constraint the
statement is false, not merely weaker: the left-hand side vanishes at every second integer.

Source: Lawler and Limic, *Random Walk: a Modern Introduction*, Theorem 2.1.1 (the local
central limit theorem for aperiodic and bipartite walks with the `O(n^{-3/2})` error on the
transition probability, which is the `C/m` error here after the factor `sqrt m`); equivalently
Spitzer, *Principles of Random Walk*, P7.6. This is an explicit input to this library; no
proof of this `Prop` is asserted here.
-/

open MeasureTheory

-- Formerly wrapped in FROZEN-STATEMENT markers; this Prop is now discharged
-- by `Parking.External.binomialLocalCLT` in `BinomialLocalCLTProved.lean`,
-- which owns the sealed node in `ledger/manifest.yaml`.  The `def` body below
-- is byte-for-byte the statement that was frozen.
/-- The local central limit theorem for the simple symmetric walk on `ℤ`, with
the error `C/m` uniform in the endpoint, in the form cited at
`parking.tex:3207-3218`. -/
def Parking.External.BinomialLocalCLT : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ j : ℤ, (j - (m : ℤ)) % 2 = 0 →
    |Real.sqrt (m : ℝ) * Parking.binomLaw m ((j + (m : ℤ)) / 2)
        - 2 * (Real.exp (-((j : ℝ) / Real.sqrt (m : ℝ)) ^ 2 / 2) /
            Real.sqrt (2 * Real.pi))| ≤ C / (m : ℝ)
