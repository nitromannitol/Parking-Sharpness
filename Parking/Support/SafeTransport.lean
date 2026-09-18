import Parking.Support.IsolatedMeasurable
import Parking.Support.IsolatedShift

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
open scoped Classical
variable {d : ℕ}

/-- Unit mass from a good hole to every site in its safe region. -/
def goodSafeMass (ω : Data d) (t R : ℕ) (y w : Site d) : ℕ :=
  if GoodHole ω t R y ∧ w ∈ safeSites ω t R y then 1 else 0

theorem goodSafeMass_le_one (ω : Data d) (t R : ℕ) (y w : Site d) :
    goodSafeMass ω t R y w ≤ 1 := by
  unfold goodSafeMass
  split_ifs <;> omega

theorem goodSafeMass_shift (v : Site d) (ω : Data d) (t R : ℕ) (y w : Site d) :
    goodSafeMass (shiftData v ω) t R y w = goodSafeMass ω t R (y + v) (w + v) := by
  simp only [goodSafeMass, GoodHole_shift, mem_safeSites_shift]

theorem measurable_goodSafeMass (t R : ℕ) (y w : Site d) :
    Measurable (fun ω : Data d => goodSafeMass ω t R y w) :=
  Measurable.ite ((measurableSet_GoodHole t R y).inter (measurableSet_mem_safeSites t R y w))
    measurable_const measurable_const

theorem goodSafeMass_out (ω : Data d) (t R : ℕ) :
    (∑ w ∈ boxFinset 0 R, goodSafeMass ω t R 0 w) =
      if GoodHole ω t R 0 then (safeSites ω t R 0).card else 0 := by
  by_cases h : GoodHole ω t R 0
  · simp only [goodSafeMass, h, true_and, if_true]
    rw [← Finset.card_filter]
    congr 1
    ext w
    simp only [Finset.mem_filter, mem_safeSites]
    tauto
  · simp only [goodSafeMass, h, false_and, if_false, Finset.sum_const_zero]

theorem goodSafeMass_in (hd : 1 ≤ d) (ω : Data d) (t R : ℕ) :
    (∑ y ∈ boxFinset 0 R, goodSafeMass ω t R y 0) ≤ if HoleCloser ω t then 1 else 0 := by
  have huniq : ∀ y z, GoodHole ω t R y → GoodHole ω t R z →
      0 ∈ safeSites ω t R y → 0 ∈ safeSites ω t R z → y = z := by
    intro y z hy hz hwy hwz
    have hR : R ≤ 2 * d * R := by nlinarith
    have hyI : IsolatedHole ω t (2 * (2 * d * R)) y := by
      convert hy.1 using 1
      ring
    have hzI : IsolatedHole ω t (2 * (2 * d * R)) z := by
      convert hz.1 using 1
      ring
    exact isolatedHole_unique hyI hzI
      (boxFinset_mono hR (mem_safeSites.mp hwy).1)
      (boxFinset_mono hR (mem_safeSites.mp hwz).1)
  by_cases h : HoleCloser ω t
  · simp only [h, if_true, goodSafeMass]
    rw [← Finset.card_filter]
    apply Finset.card_le_one.mpr
    intro y hy z hz
    exact huniq y z (Finset.mem_filter.mp hy).2.1 (Finset.mem_filter.mp hz).2.1
      (Finset.mem_filter.mp hy).2.2 (Finset.mem_filter.mp hz).2.2
  · have he : ∀ y, goodSafeMass ω t R y 0 = 0 := by
      intro y
      unfold goodSafeMass
      apply if_neg
      rintro ⟨hy, hwy⟩
      apply h
      exact (HoleCloser_iff ω t).mpr (safeSites_closer hy.1.1 hwy)
    simp only [he, Finset.sum_const_zero, h, if_false, le_refl]

end Parking
