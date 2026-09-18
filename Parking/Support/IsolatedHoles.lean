import Parking.Support.OrthantCube
import Parking.Support.HoleCloserEvent
import Parking.Support.NoBoth
import Parking.Support.Equivariance

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

theorem mem_safeSites {ω : Data d} {t R : ℕ} {y w : Site d} :
    w ∈ safeSites ω t R y ↔ w ∈ boxFinset y R ∧
      ∀ a ∈ activeSites ω t (2 * d * R) y, Opposite y a w := by
  classical
  simp only [safeSites, Finset.mem_filter]

theorem mem_activeSites {ω : Data d} {t K : ℕ} {y a : Site d} :
    a ∈ activeSites ω t K y ↔ a ∈ boxFinset y K ∧ 0 < A ω t a := by
  simp only [activeSites, Finset.mem_filter]

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
