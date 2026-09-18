/-
Infinitely many distinct particles leave a site with an infinite odometer.

The last clause of `prop:everyone-settles` (`parking.tex:1530-1532`): "Since
every particle takes finitely many steps, infinitely many distinct particles
leave every site."  Every particle settles, so it is active for finitely many
rounds; if only finitely many labels ever left `x`, all of them would be
inactive from one round on, the active count at `x` would vanish from then on,
and the odometer at `x` would stop growing.  A particle standing at `x` and
still active leaves `x`, because an instruction points at a neighbour and no
site is its own neighbour.
-/
import Parking.Support.StackHits

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Filter Topology
open scoped ENNReal

variable {d : ℕ}

theorem notMem_nbrFinset_self (x : Site d) : x ∉ nbrFinset x := by
  classical
  simp only [nbrFinset, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, not_exists]
  intro i hi
  rcases hi with h | h
  · refine unit_ne_zero i ?_
    have h2 : x + unit i = x + 0 := by rw [← h, add_zero]
    exact add_left_cancel h2
  · refine unit_ne_zero i ?_
    have h2 : x - unit i = x - 0 := by rw [← h, sub_zero]
    exact sub_right_injective h2

/-- **Infinitely many distinct particles leave every site with an infinite
odometer.**  Every particle settles, so it is active for finitely many rounds;
if only finitely many labels ever left `x`, all of them would be inactive from
some round on, the active count at `x` would vanish from then on, and the
odometer at `x` would be finite. -/
theorem infinite_departers {ω : Data d}
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ LatticeProb.nbrFinset q.1)
    (hsettle : ∀ p : Label d, ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      (LatticeProb.state (toDriver ω) t).active p = false)
    {x : Site d} (hU : Parking.Ulimit ω x = ⊤) :
    {p : Label d | ∃ t : ℕ,
      (LatticeProb.state (toDriver ω) t).active p = true ∧
        (LatticeProb.state (toDriver ω) t).pos p = x ∧
        (LatticeProb.state (toDriver ω) (t + 1)).pos p ≠ x}.Infinite := by
  classical
  have hsteps : LatticeProb.StepsToNeighbour (toDriver ω) := by
    refine stepsToNeighbour_of_mem ?_
    intro q
    have := hstep q
    simpa [toDriver] using this
  set D := toDriver ω with hD
  set S := {p : Label d | ∃ t : ℕ,
      (LatticeProb.state D t).active p = true ∧ (LatticeProb.state D t).pos p = x ∧
        (LatticeProb.state D (t + 1)).pos p ≠ x} with hS
  -- every label active at `x` after round `t` belongs to `S`
  have hmem : ∀ (t : ℕ) (p : Label d),
      p ∈ LatticeProb.activeAt D (LatticeProb.state D t) t x → p ∈ S := by
    intro t p hp
    obtain ⟨hact, hpos⟩ := (LatticeProb.mem_activeAt_iff hsteps t x p).mp hp
    refine ⟨t, hact, hpos, ?_⟩
    have hnext : (LatticeProb.state D (t + 1)).pos p
        = D.stack ((LatticeProb.state D t).pos p,
            LatticeProb.instructionIndex D (LatticeProb.state D t) t p) := by
      show LatticeProb.nextPos D (LatticeProb.state D t) t p = _
      unfold LatticeProb.nextPos
      rw [if_pos hact]
    rw [hnext, hpos]
    intro hc
    have hin : D.stack (x, LatticeProb.instructionIndex D (LatticeProb.state D t) t p)
        ∈ nbrFinset x := by
      have := hstep (x, LatticeProb.instructionIndex D (LatticeProb.state D t) t p)
      simpa [hD, toDriver] using this
    rw [hc] at hin
    exact notMem_nbrFinset_self x hin
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨F, hF⟩ := hfin.exists_finset_coe
  -- a round after which no label of `F` is active
  set M : ℕ := F.sup (fun p => Nat.find (hsettle p)) with hM
  have hzero : ∀ t : ℕ, M ≤ t → LatticeProb.activeCount D t x = 0 := by
    intro t ht
    rw [LatticeProb.activeCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro p hp
    have hpS : p ∈ S := hmem t p hp
    have hpF : p ∈ F := by rw [← Finset.mem_coe, hF]; exact hpS
    have hle : Nat.find (hsettle p) ≤ M :=
      Finset.le_sup (f := fun p : Label d => Nat.find (hsettle p)) hpF
    have hact := (LatticeProb.mem_activeAt_iff hsteps t x p).mp hp |>.1
    have := Nat.find_spec (hsettle p) t (le_trans hle ht)
    rw [this] at hact
    exact absurd hact (by simp)
  have hconst : ∀ n : ℕ, M ≤ n → Parking.U ω n x = Parking.U ω M x := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
        have hA0 : Parking.A ω n x = 0 := hzero n hn
        rw [show Parking.U ω (n + 1) x = Parking.U ω n x + Parking.A ω n x from rfl,
          ih, hA0, Nat.add_zero]
  rw [Ulimit_eq_top_iff] at hU
  obtain ⟨n, hn⟩ := hU (Parking.U ω M x + 1)
  rcases Nat.lt_or_ge n M with h | h
  · have := LatticeProb.particleOdometer_mono (toDriver ω) x (le_of_lt h)
    have h2 : Parking.U ω n x ≤ Parking.U ω M x := this
    omega
  · rw [hconst n h] at hn
    omega

end Parking
