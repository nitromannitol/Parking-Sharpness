/-
Lemma 6.1 of parking.tex, frozen.  `parking.tex:1240-1248` (label
`lem:critical-density`):

  "Let $\eta=(\eta(x))_{x\in\Z^d}$ be independent copies of a nonconstant
   integer-valued $\eta(0)$ with mean zero.  There is a universal $c>0$ such
   that $\liminf_{t\to\infty}tS_t\geq c$, and there is $C<\infty$ such that,
   for every $n\geq2$, $\E U_n(0)\geq c\log n-C$."

The constant `c` is universal, so it is bound before the dimension and the
law; `C` depends on both, so it is bound after them.  The mean-zero
hypothesis carries with it the integrability that gives it meaning.

The paper's `liminf_{t}tS_t\geq c` is transcribed as the eventual bound
`\forall^f t, c \leq tS_t`, which is what the paper's Step 3 proves and what a
`liminf` in the reals cannot express here.  In `ℝ` the `liminf` of a sequence
with no eventual upper bound is `sSup` of an unbounded set, which is the junk
value `0`, so the clause would read `c \leq 0`; and below dimension four
`eq:activity` makes `tS_t` of order `t^{(4-d)/4}`, which is unbounded.  The
eventual bound implies the paper's assertion wherever the `liminf` is honest,
and is the form Step 3 establishes.
-/
import Parking.Support.CouplingProof

open MeasureTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.critical_density :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (ν : Measure ℤ), IsProbabilityMeasure ν →
      (∀ k : ℤ, ν {k} ≠ 1) → Integrable (fun k : ℤ => |(k : ℝ)|) ν →
      ∫ k, (k : ℝ) ∂ν = 0 →
      (∀ᶠ t : ℕ in atTop, c ≤ (t : ℝ) * Parking.S (Parking.law d ν) t) ∧
        ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
          c * Real.log n - C ≤ Parking.meanU (Parking.law d ν) n
-- FROZEN-STATEMENT-END
:= by
  refine ⟨1 / 16, by norm_num, ?_⟩
  intro d hd ν hprob hnc hint hmean
  haveI := hprob
  exact Parking.critical_density_of_coupling hd ν hprob hnc hint
    (Parking.coupling_bound hd ν hint hmean)
