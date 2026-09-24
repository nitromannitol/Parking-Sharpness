/-
**Shift invariance of the simple random walk's driving law, and the excursion decomposition
of `Parking.walkPath`.**  These serve the temporal half of `prop:spatial-scaling`'s
equicontinuity clause: the reward gap on the truncated event needs a bound on the walk's OWN
displacement over an excursion `[n, n']`, and that bound rests on two facts: (1) the law of
the walk directions read from step `n` onward is again `Parking.walkLaw d` (a standard
i.i.d.-sequence fact), and (2) the walk's own position increment over that excursion is a
deterministic function of the shifted direction sequence alone.

**(1)** is `LatticeProb.measurePreserving_coordShift`, from the shared library
(`LatticeProb/Prob/ZeroOne.lean` in Lattice-Probability): the coordinate shift along an
injective, law-preserving reindexing of an i.i.d. product measure preserves the product
measure.  `Parking.walkLaw d = Measure.infinitePi (fun _ : ℕ => Parking.stepLaw d)` has the
SAME (constant) factor at every index, so the shift `p ↦ p(· + n)` (`LatticeProb.coordShift
(· + n)`, injective since `k ↦ k + n` is) preserves it.

**(2)** is immediate from `Parking.walkPath`'s own recursive definition, by induction: the
position after `n + j` steps of `p` is the position after `n` steps, walked `j` further steps
along the SHIFTED direction sequence.  Combined with `Parking.walkPath_eq_add_walkPath_zero`
(`Parking/Support/StoppingShift.lean`), the excursion `walkPath x p (n+j) - walkPath x p n`
equals `walkPath 0 (coordShift (·+n) p) j` EXACTLY, independent of `x` and of `n`'s own
history: a pure identity, no probability needed for it.

Combining (1) and (2) with the already-proved maximal-displacement tail
(`Parking.measureReal_sup_walkPath_graphNorm_le`, `Parking/Support/WalkMaximal.lean`) gives the
SAME tail bound for the EXCURSION from any step `n`, uniform in `n`: the walk cannot travel far
in `m` further steps, whichever step it starts counting from.
-/
import Parking.Support.WalkMaximal
import Parking.Support.StoppingShift

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Parking

variable {d : ℕ}

/-! ### Shift invariance of the driving law -/

/-- **The law of the direction sequence, read from step `n` onward, is again
`Parking.walkLaw d`.**  The shift `p ↦ p(· + n)` preserves the i.i.d. product measure since
every coordinate carries the SAME factor law `Parking.stepLaw d`. -/
theorem measurePreserving_walkShift (hd : 1 ≤ d) (n : ℕ) :
    MeasurePreserving (LatticeProb.coordShift (X := Fin d × Bool) (fun k => k + n))
      (Parking.walkLaw d) (Parking.walkLaw d) := by
  haveI := Parking.stepLaw_isProbability hd
  unfold Parking.walkLaw
  exact LatticeProb.measurePreserving_coordShift (fun _ : ℕ => Parking.stepLaw d)
    (add_left_injective n) (fun _ => rfl)

/-! ### The excursion decomposition of `walkPath` -/

/-- **The walk after `n + j` steps is the walk after `n` steps, walked `j` further steps
along the SHIFTED direction sequence.**  A pure identity from `Parking.walkPath`'s own
recursion, by induction on `j`. -/
theorem walkPath_add (x : Site d) (p : ℕ → Fin d × Bool) (n j : ℕ) :
    Parking.walkPath x p (n + j)
      = Parking.walkPath (Parking.walkPath x p n) (LatticeProb.coordShift (fun k => k + n) p)
          j := by
  induction j with
  | zero => simp [Parking.walkPath]
  | succ j ih =>
      rw [show n + (j + 1) = (n + j) + 1 from rfl, Parking.walkPath, ih, Parking.walkPath]
      have hidx : (LatticeProb.coordShift (fun k => k + n) p) j = p (n + j) := by
        show p (j + n) = p (n + j)
        rw [add_comm]
      rw [hidx]

/-- **The excursion `[n, n+j]` of the walk is a deterministic function of the shifted
direction sequence alone**: `walkPath x p (n+j) - walkPath x p n = walkPath 0 (shift p n) j`,
independent of the starting site `x` and of the history before step `n`. -/
theorem walkPath_excursion_eq (x : Site d) (p : ℕ → Fin d × Bool) (n j : ℕ) :
    Parking.walkPath x p (n + j) - Parking.walkPath x p n
      = Parking.walkPath (0 : Site d) (LatticeProb.coordShift (fun k => k + n) p) j := by
  rw [walkPath_add x p n j,
    Parking.walkPath_eq_add_walkPath_zero (Parking.walkPath x p n)
      (LatticeProb.coordShift (fun k => k + n) p) j]
  abel

/-! ### The maximal-displacement tail of an excursion -/

/-- **The walk's own maximal displacement over the excursion `[n, n+m]`, uniform in `n`.**
The excursion has, EXACTLY (not merely in distribution), the walk's own position at step `m`
of the shifted direction sequence, and the shift preserves `Parking.walkLaw d`
(`Parking.measurePreserving_walkShift`), so the event has the SAME probability as the
un-shifted event `Parking.measureReal_sup_walkPath_graphNorm_le` already bounds. -/
theorem measurableSet_walkPath_graphNorm_ge (m : ℕ) (A' : ℝ) :
    MeasurableSet {p : ℕ → Fin d × Bool |
      ∃ j ≤ m, A' ≤ (Parking.graphNorm (Parking.walkPath (0 : Site d) p j) : ℝ)} := by
  have heq : {p : ℕ → Fin d × Bool |
        ∃ j ≤ m, A' ≤ (Parking.graphNorm (Parking.walkPath (0 : Site d) p j) : ℝ)}
      = ⋃ j ∈ Finset.range (m + 1),
          {p : ℕ → Fin d × Bool | A' ≤ (Parking.graphNorm (Parking.walkPath (0 : Site d) p j) : ℝ)} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, Nat.lt_succ_iff, exists_prop]
  rw [heq]
  refine Finset.measurableSet_biUnion _ (fun j _ => ?_)
  exact measurableSet_le measurable_const
    ((Measurable.of_discrete (f := fun z : Site d => (Parking.graphNorm z : ℝ))).comp
      (Parking.measurable_walkPath (0 : Site d) j))

theorem measureReal_sup_walkPath_excursion_le (hd : 1 ≤ d) (x : Site d) (n m : ℕ) {A : ℝ}
    (hA : 0 < A) :
    (Parking.walkLaw d).real
        {p | ∃ j ≤ m, (d : ℝ) * A
          ≤ (Parking.graphNorm (Parking.walkPath x p (n + j) - Parking.walkPath x p n) : ℝ)}
      ≤ (m : ℝ) / A ^ 2 := by
  set S : Set (ℕ → Fin d × Bool) :=
    {p | ∃ j ≤ m, (d : ℝ) * A ≤ (Parking.graphNorm (Parking.walkPath (0 : Site d) p j) : ℝ)}
    with hS
  set f : (ℕ → Fin d × Bool) → (ℕ → Fin d × Bool) :=
    LatticeProb.coordShift (fun k => k + n) with hf
  have heq : {p | ∃ j ≤ m, (d : ℝ) * A
      ≤ (Parking.graphNorm (Parking.walkPath x p (n + j) - Parking.walkPath x p n) : ℝ)}
      = f ⁻¹' S := by
    ext p
    simp only [hS, hf, Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · rintro ⟨j, hjm, hj⟩
      exact ⟨j, hjm, (walkPath_excursion_eq x p n j) ▸ hj⟩
    · rintro ⟨j, hjm, hj⟩
      exact ⟨j, hjm, (walkPath_excursion_eq x p n j).symm ▸ hj⟩
  rw [heq]
  have hSmeas : MeasurableSet S := measurableSet_walkPath_graphNorm_ge m ((d : ℝ) * A)
  have hpres := measurePreserving_walkShift hd n
  have hmapeq : (Parking.walkLaw d).map f S = (Parking.walkLaw d) S := by
    rw [hpres.map_eq]
  have hpre : (Parking.walkLaw d).map f S = (Parking.walkLaw d) (f ⁻¹' S) :=
    Measure.map_apply hpres.measurable hSmeas
  have hfinal : (Parking.walkLaw d) (f ⁻¹' S) = (Parking.walkLaw d) S := by
    rw [← hpre, hmapeq]
  rw [Measure.real, hfinal, ← Measure.real]
  exact Parking.measureReal_sup_walkPath_graphNorm_le hd m hA

end Parking

end
