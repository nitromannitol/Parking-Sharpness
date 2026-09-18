/-
External input: the asymptotics of the two norms of the truncated Green
function of the simple random walk, as the paper quotes them
(`parking.tex:1366-1386`, label `eq:green-norms`) from the Green estimates
collected in Bou-Rabee and Panagiotis, Section 3.1 there.  The paper states the
display and attributes it to that section, so no proof of it is given in
`parking.tex` and it enters here as a hypothesis.

Assumed here.  It enters only as an explicit hypothesis of the results whose
proofs use it.
-/
import Parking.Support.Kernel

open MeasureTheory

noncomputable section

namespace Parking.External

/-- The rate of `‖g_n‖₂` in `eq:green-norms`: `n^{3/4}`, `n^{1/2}`, `n^{1/4}`,
`√(log n)` and `1` in dimensions one, two, three, four and five upward. -/
def greenL2Rate (d : ℕ) (n : ℕ) : ℝ :=
  if d = 1 then (n : ℝ) ^ ((3 : ℝ) / 4)
  else if d = 2 then (n : ℝ) ^ ((1 : ℝ) / 2)
  else if d = 3 then (n : ℝ) ^ ((1 : ℝ) / 4)
  else if d = 4 then Real.sqrt (Real.log n)
  else 1

/-- The rate of `max_x g_n(x)` in `eq:green-norms`: `n^{1/2}`, `log n` and `1`
in dimensions one, two and three upward. -/
def greenMaxRate (d : ℕ) (n : ℕ) : ℝ :=
  if d = 1 then (n : ℝ) ^ ((1 : ℝ) / 2)
  else if d = 2 then Real.log n
  else 1

end Parking.External

-- FROZEN-STATEMENT-BEGIN
/-- "The Green estimates collected in \\citet[Section~3.1]{BP} give
$\\|g_n\\|_2\\asymp n^{3/4}\\ (d=1)$, $n^{1/2}\\ (d=2)$, $n^{1/4}\\ (d=3)$,
$\\sqrt{\\log n}\\ (d=4)$, $1\\ (d\\geq5)$, and
$\\max_xg_n(x)\\asymp n^{1/2}\\ (d=1)$, $\\log n\\ (d=2)$, $1\\ (d\\geq3)$."

Each of the two relations `≍` carries its own pair of constants, as the paper's
two displays do, and each holds on the range `n ≥ 2` in which the paper reads
them.  Both quantities and both rates are positive and finite at every `n ≥ 2`,
so this is the same assertion as the one for all large `n`. -/
def Parking.External.GreenNorms : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        c * Parking.External.greenL2Rate d n ≤ Parking.l2Norm (Parking.green d n) ∧
          Parking.l2Norm (Parking.green d n) ≤ C * Parking.External.greenL2Rate d n) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        c * Parking.External.greenMaxRate d n ≤ Parking.greenMax d n ∧
          Parking.greenMax d n ≤ C * Parking.External.greenMaxRate d n)
-- FROZEN-STATEMENT-END

end
