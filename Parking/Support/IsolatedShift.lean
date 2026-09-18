import Parking.Support.IsolatedHoles
import Parking.Support.BoxTranslation

noncomputable section
namespace Parking
open LatticeProb
variable {d : ℕ}

theorem mem_activeSites_shift (v : Site d) (ω : Data d) (t K : ℕ) (y a : Site d) :
    a ∈ activeSites (shiftData v ω) t K y ↔ a + v ∈ activeSites ω t K (y + v) := by
  simp only [mem_activeSites, A_shiftData, mem_boxFinset_translate]

theorem activeSites_shift_image (v : Site d) (ω : Data d) (t K : ℕ) (y : Site d) :
    (activeSites (shiftData v ω) t K y).image (fun a => a + v) =
      activeSites ω t K (y + v) := by
  ext a
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (mem_activeSites_shift v ω t K y b).mp hb
  · intro ha
    refine ⟨a - v, ?_, sub_add_cancel a v⟩
    apply (mem_activeSites_shift v ω t K y (a - v)).mpr
    simpa only [sub_add_cancel] using ha

theorem activeSites_shift_card (v : Site d) (ω : Data d) (t K : ℕ) (y : Site d) :
    (activeSites (shiftData v ω) t K y).card = (activeSites ω t K (y + v)).card := by
  rw [← activeSites_shift_image v ω t K y, Finset.card_image_of_injective _ (add_left_injective v)]

theorem IsolatedHole_shift (v : Site d) (ω : Data d) (t K : ℕ) (y : Site d) :
    IsolatedHole (shiftData v ω) t K y ↔ IsolatedHole ω t K (y + v) := by
  constructor
  · rintro ⟨hy, hi⟩
    refine ⟨by simpa only [H_shiftData] using hy, fun z hz hne => ?_⟩
    have hz' : z - v ∈ boxFinset y K := by
      apply (mem_boxFinset_translate v y (z - v) K).mp
      simpa only [sub_add_cancel] using hz
    have hne' : z - v ≠ y := by
      intro he
      apply hne
      exact sub_eq_iff_eq_add.mp he
    have h := hi (z - v) hz' hne'
    simpa only [H_shiftData, sub_add_cancel] using h
  · rintro ⟨hy, hi⟩
    refine ⟨by simpa only [H_shiftData] using hy, fun z hz hne => ?_⟩
    have hz' := (mem_boxFinset_translate v y z K).mpr hz
    have hne' : z + v ≠ y + v := by exact fun he => hne (add_right_cancel he)
    simpa only [H_shiftData] using hi (z + v) hz' hne'

theorem GoodHole_shift (v : Site d) (ω : Data d) (t R : ℕ) (y : Site d) :
    GoodHole (shiftData v ω) t R y ↔ GoodHole ω t R (y + v) := by
  simp only [GoodHole, IsolatedHole_shift, activeSites_shift_card]

theorem mem_safeSites_shift (v : Site d) (ω : Data d) (t R : ℕ) (y w : Site d) :
    w ∈ safeSites (shiftData v ω) t R y ↔ w + v ∈ safeSites ω t R (y + v) := by
  simp only [mem_safeSites, mem_boxFinset_translate]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h a ha
    have ha' : a - v ∈ activeSites (shiftData v ω) t (2 * d * R) y := by
      apply (mem_activeSites_shift v ω t (2 * d * R) y (a - v)).mpr
      simpa only [sub_add_cancel] using ha
    have ho := (Opposite.translate v).mpr (h (a - v) ha')
    simpa only [sub_add_cancel] using ho
  · intro h a ha
    apply (Opposite.translate v).mp
    exact h (a + v) ((mem_activeSites_shift v ω t (2 * d * R) y a).mp ha)

end Parking
