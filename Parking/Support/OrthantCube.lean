import Parking.Basic
import LatticeProb.Walk.SRW
import LatticeProb.ParticleHoleLemmas

noncomputable section
namespace Parking
open LatticeProb
variable {d : ℕ}

/-- A cube in the closed orthant opposite a specified site. -/
def orthantPoint (y a : Site d) {R : ℕ} (k : Fin d → Fin (R + 1)) : Site d :=
  fun i => y i + if y i < a i then -(k i : ℤ) else (k i : ℤ)

def orthantCube (y a : Site d) (R : ℕ) : Finset (Site d) :=
  Finset.univ.image (orthantPoint y a (R := R))

theorem orthantPoint_injective (y a : Site d) (R : ℕ) :
    Function.Injective (orthantPoint y a (R := R)) := by
  intro k l h
  funext i
  have hi := congrFun h i
  dsimp only [orthantPoint] at hi
  split_ifs at hi <;> exact Fin.ext (by omega)

theorem card_orthantCube (y a : Site d) (R : ℕ) :
    (orthantCube y a R).card = (R + 1) ^ d := by
  rw [orthantCube, Finset.card_image_of_injective _ (orthantPoint_injective y a R)]
  simp

theorem orthantCube_subset_box (y a : Site d) (R : ℕ) :
    orthantCube y a R ⊆ boxFinset y R := by
  intro w hw
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hw
  apply mem_boxFinset_iff.mpr
  intro i
  have hk := (k i).isLt
  dsimp only [orthantPoint]
  split_ifs <;> rw [abs_le] <;> omega

theorem graphNorm_sub_le_of_mem_box {y w : Site d} {R : ℕ}
    (hw : w ∈ boxFinset y R) : graphNorm (w - y) ≤ d * R := by
  have hsum : ∑ i : Fin d, ((w - y) i).natAbs ≤ ∑ _i : Fin d, R := by
    apply Finset.sum_le_sum
    intro i _
    have hi := mem_boxFinset_iff.mp hw i
    have hn : (((w i - y i).natAbs : ℕ) : ℤ) ≤ (R : ℤ) := by simpa using hi
    exact_mod_cast hn
  simpa [graphNorm] using hsum

theorem graphNorm_orthant_add {y a w : Site d} {R : ℕ}
    (hw : w ∈ orthantCube y a R) :
    graphNorm (w - a) = graphNorm (w - y) + graphNorm (a - y) := by
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hw
  unfold graphNorm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hk : (0 : ℤ) ≤ (k i : ℤ) := by omega
  apply Int.natCast_inj.mp
  push_cast
  dsimp only [Pi.sub_apply, orthantPoint]
  split_ifs with h
  · rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega), abs_of_nonneg (by omega)]
    omega
  · rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega), abs_of_nonpos (by omega)]
    omega

theorem orthantCube_closer {y a w : Site d} {R : ℕ} (hya : y ≠ a)
    (hw : w ∈ orthantCube y a R) : graphNorm (w - y) < graphNorm (w - a) := by
  rw [graphNorm_orthant_add hw]
  have hn : graphNorm (a - y) ≠ 0 := by
    intro h
    have ha : a - y = 0 := LatticeProb.graphNorm_eq_zero_iff.mp h
    exact hya (sub_eq_zero.mp ha).symm
  omega

/-- The coordinatewise order defining the opposite orthant. -/
def Opposite (y a w : Site d) : Prop :=
  ∀ i, if y i < a i then w i ≤ y i else y i ≤ w i

theorem orthantCube_opposite {y a w : Site d} {R : ℕ}
    (hw : w ∈ orthantCube y a R) : Opposite y a w := by
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hw
  intro i
  dsimp only [orthantPoint]
  split_ifs <;> omega

theorem graphNorm_sub_add_of_opposite {y a w : Site d} (hw : Opposite y a w) :
    graphNorm (w - a) = graphNorm (w - y) + graphNorm (a - y) := by
  unfold graphNorm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := hw i
  apply Int.natCast_inj.mp
  push_cast
  dsimp only [Pi.sub_apply]
  by_cases h : y i < a i
  · simp only [h, if_true] at hi
    rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega), abs_of_nonneg (by omega)]
    omega
  · simp only [h, if_false] at hi
    rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega), abs_of_nonpos (by omega)]
    omega

theorem Opposite.translate (v : Site d) {y a w : Site d} :
    Opposite (y + v) (a + v) (w + v) ↔ Opposite y a w := by
  simp only [Opposite, Pi.add_apply, add_lt_add_iff_right, add_le_add_iff_right]

theorem graphNorm_sub_comm (y a : Site d) : graphNorm (y - a) = graphNorm (a - y) := by
  unfold graphNorm
  apply Finset.sum_congr rfl
  intro i _
  apply Int.natCast_inj.mp
  simp [abs_sub_comm]

theorem closer_of_far {y w v : Site d} {R : ℕ} (hw : w ∈ boxFinset y R)
    (hv : v ∉ boxFinset y (2 * d * R)) : graphNorm (w - y) < graphNorm (w - v) := by
  have hwR := graphNorm_sub_le_of_mem_box hw
  have hvR : 2 * d * R < graphNorm (v - y) := by
    by_contra h
    apply hv
    apply mem_boxFinset_iff.mpr
    intro i
    have hn : (v i - y i).natAbs ≤ graphNorm (v - y) := by
      apply Finset.single_le_sum (f := fun j : Fin d => (v j - y j).natAbs)
      · intro _ _; omega
      · exact Finset.mem_univ i
    have hn' : (v i - y i).natAbs ≤ 2 * d * R := hn.trans (by omega)
    have hc := (Int.ofNat_le).mpr hn'
    simpa using hc
  have ht : graphNorm (v - y) ≤ graphNorm (v - w) + graphNorm (w - y) := by
    unfold graphNorm
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have h := Int.natAbs_add_le (v i - w i) (w i - y i)
    simpa only [sub_add_sub_cancel, Pi.sub_apply] using h
  rw [graphNorm_sub_comm v w] at ht
  nlinarith

end Parking
