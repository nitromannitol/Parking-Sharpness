import Parking.Support.OrthantCube
import Parking.Support.HoleCloserEvent
import Parking.Support.NoBoth
import Parking.Support.Equivariance

/-!
# Isolated holes and their safe orthant

`IsolatedHole ω t K y` says the hole at `y` is the only unit hole in its `K`-box, and
`GoodHole` strengthens this to at most one active site nearby. `safeSites ω t R y`
collects the sites in the `R`-box around `y` lying in the orthant opposite every
nearby active site; `card_safeSites_lower` shows this set contains a full orthant
cube whenever there is at most one such active site, and `safeSites_closer` shows
every safe site is strictly closer (in graph distance) to the hole `y` than to any
active site. `isolatedHole_unique` records that two isolated holes with overlapping
boxes must coincide.
-/

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- A unit hole with no other unit hole in the specified box. -/
def IsolatedHole (ω : Data d) (t K : ℕ) (y : Site d) : Prop :=
  H ω t y = 1 ∧ ∀ z ∈ boxFinset y K, z ≠ y → H ω t z ≠ 1

/-- The active sites in a finite box. -/
def activeSites (ω : Data d) (t K : ℕ) (y : Site d) : Finset (Site d) :=
  (boxFinset y K).filter fun a => 0 < A ω t a

/-- An isolated hole with at most one nearby active site. -/
def GoodHole (ω : Data d) (t R : ℕ) (y : Site d) : Prop :=
  IsolatedHole ω t (4 * d * R) y ∧ (activeSites ω t (2 * d * R) y).card ≤ 1

/-- Sites in every orthant opposite a nearby active site. -/
def safeSites (ω : Data d) (t R : ℕ) (y : Site d) : Finset (Site d) := by
  classical
  exact (boxFinset y R).filter fun w => ∀ a ∈ activeSites ω t (2 * d * R) y, Opposite y a w

/-- Characterizes membership in `safeSites`: `w` lies in the box of radius `R` around
`y` and is on the opposite side of `y` from every nearby active site. -/
theorem mem_safeSites {ω : Data d} {t R : ℕ} {y w : Site d} :
    w ∈ safeSites ω t R y ↔ w ∈ boxFinset y R ∧
      ∀ a ∈ activeSites ω t (2 * d * R) y, Opposite y a w := by
  classical
  simp only [safeSites, Finset.mem_filter]

/-- Characterizes membership in `activeSites`: `a` lies in the box of radius `K`
around `y` and carries at least one active particle. -/
theorem mem_activeSites {ω : Data d} {t K : ℕ} {y a : Site d} :
    a ∈ activeSites ω t K y ↔ a ∈ boxFinset y K ∧ 0 < A ω t a := by
  simp only [activeSites, Finset.mem_filter]

/-- When there is at most one active site near `y`, the safe sites contain a full
orthant cube (opposite the unique active site, or an arbitrary orthant when there
is none), giving the lower bound `(R + 1) ^ d ≤ (safeSites ω t R y).card`. -/
theorem card_safeSites_lower {ω : Data d} {t R : ℕ} {y : Site d}
    (h : (activeSites ω t (2 * d * R) y).card ≤ 1) :
    (R + 1) ^ d ≤ (safeSites ω t R y).card := by
  classical
  by_cases he : (activeSites ω t (2 * d * R) y).Nonempty
  · obtain ⟨a, ha⟩ := he
    rw [← card_orthantCube y a R]
    apply Finset.card_le_card
    intro w hw
    apply mem_safeSites.mpr
    refine ⟨orthantCube_subset_box y a R hw, fun b hb => ?_⟩
    have hba := Finset.card_le_one.mp h b hb a ha
    rw [hba]
    exact orthantCube_opposite hw
  · rw [← card_orthantCube y y R]
    apply Finset.card_le_card
    intro w hw
    apply mem_safeSites.mpr
    exact ⟨orthantCube_subset_box y y R hw, fun a ha => (he ⟨a, ha⟩).elim⟩

/-- A safe site `w` near a unit hole `y` is strictly closer to `y` than to every
active site: opposite active sites within the doubled box are handled by
`graphNorm_sub_add_of_opposite`, and active sites far outside the box are handled
by `closer_of_far`. -/
theorem safeSites_closer {ω : Data d} {t R : ℕ} {y w : Site d}
    (hy : H ω t y = 1) (hw : w ∈ safeSites ω t R y) : CloserAt ω t w := by
  obtain ⟨hwB, hwO⟩ := mem_safeSites.mp hw
  refine ⟨y, by omega, fun a ha => ?_⟩
  by_cases hab : a ∈ boxFinset y (2 * d * R)
  · have hop := hwO a (mem_activeSites.mpr ⟨hab, ha⟩)
    rw [graphNorm_sub_add_of_opposite hop]
    have hne : a ≠ y := by
      intro he
      have hz := H_eq_zero_of_A_pos ω t a ha
      rw [he] at hz
      omega
    have hn : graphNorm (a - y) ≠ 0 := by
      intro hz
      have he : a - y = 0 := LatticeProb.graphNorm_eq_zero_iff.mp hz
      exact hne (sub_eq_zero.mp he)
    omega
  · exact closer_of_far hwB hab

/-- Two isolated holes whose `K`-boxes share a common site must coincide: each
isolated hole excludes any other unit hole from its own `2K`-box. -/
theorem isolatedHole_unique {ω : Data d} {t K : ℕ} {w y z : Site d}
    (hy : IsolatedHole ω t (2 * K) y) (hz : IsolatedHole ω t (2 * K) z)
    (hwy : w ∈ boxFinset y K) (hwz : w ∈ boxFinset z K) : y = z := by
  by_contra hne
  have hwz' : z ∈ boxFinset w K := by
    apply mem_boxFinset_iff.mpr
    intro i
    simpa only [abs_sub_comm] using mem_boxFinset_iff.mp hwz i
  have hzB : z ∈ boxFinset y (2 * K) := by
    simpa only [two_mul] using mem_boxFinset_add hwy hwz'
  exact hy.2 z hzB (Ne.symm hne) hz.1

end Parking
