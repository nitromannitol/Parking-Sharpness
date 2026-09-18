/-
A σ-uniform comparison of two optimal-stopping values, needed for `happ`
(`parking.tex:3199-3203`).

`Parking.abs_orientedStoppingSup_sub_le` (`OrientedValueLipschitz.lean`) bounds
`|orientedStoppingSup d F n x - orientedStoppingSup d G n x|` from a POINTWISE
bound `|F k y - G k y| ≤ c` holding at EVERY `(k, y)`.  That bound is not
available for the two rewards of `happ`: the true (unclamped) reward is
unbounded, so no single constant `c` bounds `|F - G|` at every site.

What IS available is a bound on the DIFFERENCE OF EXPECTED TERMINAL VALUES,
`|orientedTerminalValue F x σ - orientedTerminalValue G x σ| ≤ c`, uniform
over every admissible stopping rule `σ`, even though no such uniform bound
holds pointwise in `(k, y)`.  This module extracts the `sSup`-comparison
argument inside `abs_orientedStoppingSup_sub_le`'s own proof and exposes it
under this weaker, σ-indexed hypothesis: the argument itself never uses the
POINTWISE bound directly, only the terminal-value bound it produces.
-/
import Parking.Support.OrientedValueLipschitz

open MeasureTheory

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- **The value of the discrete optimal-stopping problem is close whenever
the expected terminal value of EVERY admissible rule is close**, even when no
pointwise bound on the two rewards is available. -/
theorem abs_orientedStoppingSup_sub_le_of_terminal (_hd : 1 ≤ d) (F G : ℕ → Site d → ℝ)
    (n : ℕ) (x : Site d) {c : ℝ}
    (hBddF : BddAbove (orientedTerminalValues d F n x))
    (hBddG : BddAbove (orientedTerminalValues d G n x))
    (hbound : ∀ σ, IsStoppingTimeLE n σ →
      |orientedTerminalValue F x σ - orientedTerminalValue G x σ| ≤ c) :
    |orientedStoppingSup d F n x - orientedStoppingSup d G n x| ≤ c := by
  have hneF := orientedTerminalValues_nonempty d F n x
  have hneG := orientedTerminalValues_nonempty d G n x
  have key : ∀ (F' G' : ℕ → Site d → ℝ),
      BddAbove (orientedTerminalValues d G' n x) →
      (orientedTerminalValues d F' n x).Nonempty →
      (∀ σ, IsStoppingTimeLE n σ →
        |orientedTerminalValue F' x σ - orientedTerminalValue G' x σ| ≤ c) →
      orientedStoppingSup d F' n x ≤ orientedStoppingSup d G' n x + c := by
    intro F' G' hb hne hd'
    refine csSup_le hne ?_
    rintro a ⟨σ, hσ, rfl⟩
    have h1 : orientedTerminalValue G' x σ ≤ orientedStoppingSup d G' n x :=
      le_csSup hb ⟨σ, hσ, rfl⟩
    have h2 := hd' σ hσ
    have h3 := (abs_sub_le_iff.mp h2).1
    linarith
  have h1 := key F G hBddG hneF hbound
  have h2 := key G F hBddF hneG (fun σ hσ => by
    rw [abs_sub_comm]; exact hbound σ hσ)
  rw [abs_sub_le_iff]
  constructor <;> linarith

end Parking

end
