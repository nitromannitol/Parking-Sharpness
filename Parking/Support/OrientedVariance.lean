/- The telescoping instruction variance of the directed Green function. -/
import Parking.Support.OrientedLayer

noncomputable section
namespace Parking
open LatticeProb Finset
variable {d : ℕ}

/-- The centered increment from a single directed layer. -/
def orientedDifference (d l : ℕ) (x : Site d) (i : Fin d) : ℝ :=
  orientedLayer d l (x + unit i) - orientedLayer d (l + 1) x

/-- The variance contributed by one layer to a departure instruction. -/
def orientedCharge (d l : ℕ) (x : Site d) : ℝ :=
  (∑ i : Fin d, orientedDifference d l x i ^ 2) / d

/-- The variance of the truncated Green function under the particle kernel. -/
def orientedGamma (d m : ℕ) (x : Site d) : ℝ :=
  (∑ i : Fin d, (orientedGreen d m (x + unit i) -
    (∑ j : Fin d, orientedGreen d m (x + unit j)) / d) ^ 2) / d

theorem orientedCharge_nonneg (l : ℕ) (x : Site d) : 0 ≤ orientedCharge d l x := by
  exact div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)

theorem orientedDifference_height {l : ℕ} {x : Site d} {i : Fin d}
    (h : orientedDifference d l x i ≠ 0) : layerHeight x = -((l + 1 : ℕ) : ℤ) := by
  by_cases hp : orientedLayer d l (x + unit i) = 0
  · have hq : orientedLayer d (l + 1) x ≠ 0 := by
      intro hq
      exact h (by simp [orientedDifference, hp, hq])
    exact orientedLayer_height hq
  · have he := orientedLayer_height hp
    rw [layerHeight_add, layerHeight_unit] at he
    push_cast
    omega

theorem orientedDifference_mul_eq_zero {l k : ℕ} (hlk : l ≠ k) (x : Site d) (i : Fin d) :
    orientedDifference d l x i * orientedDifference d k x i = 0 := by
  by_contra h
  obtain ⟨hl, hk⟩ := mul_ne_zero_iff.mp h
  have he := orientedDifference_height hl
  have he' := orientedDifference_height hk
  exact hlk (by omega)

theorem orientedCharge_eq (hd : 1 ≤ d) (l : ℕ) (x : Site d) :
    orientedCharge d l x = (∑ i : Fin d, orientedLayer d l (x + unit i) ^ 2) / d -
      orientedLayer d (l + 1) x ^ 2 := by
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hd)
  have hmass : (∑ i : Fin d, orientedLayer d l (x + unit i)) =
      (d : ℝ) * orientedLayer d (l + 1) x := by
    rw [orientedLayer_succ]
    field_simp
  have he : (∑ i : Fin d, orientedDifference d l x i ^ 2) =
      (∑ i : Fin d, orientedLayer d l (x + unit i) ^ 2) -
        2 * (∑ i : Fin d, orientedLayer d l (x + unit i)) * orientedLayer d (l + 1) x +
        (d : ℝ) * orientedLayer d (l + 1) x ^ 2 := by
    simp only [orientedDifference, sub_sq, sum_add_distrib, sum_sub_distrib,
      ← sum_mul, ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [orientedCharge, he, hmass]
  field_simp
  ring

theorem summable_orientedCharge (hd : 1 ≤ d) (l : ℕ) : Summable (orientedCharge d l) := by
  have hs : ∀ i : Fin d, Summable fun x : Site d => orientedLayer d l (x + unit i) ^ 2 := by
    intro i
    exact ((Equiv.addRight (unit i)).summable_iff
      (f := fun x : Site d => orientedLayer d l x ^ 2)).mpr (summable_orientedLayer_sq l)
  have h := ((summable_sum (s := univ) (fun i _ => hs i)).div_const (d : ℝ)).sub
    (summable_orientedLayer_sq (d := d) (l + 1))
  exact h.congr fun x => (orientedCharge_eq hd l x).symm

theorem tsum_orientedCharge (hd : 1 ≤ d) (l : ℕ) :
    (∑' x, orientedCharge d l x) = (∑' x : Site d, orientedLayer d l x ^ 2) -
      ∑' x : Site d, orientedLayer d (l + 1) x ^ 2 := by
  have hs : ∀ i : Fin d, Summable fun x : Site d => orientedLayer d l (x + unit i) ^ 2 := by
    intro i
    exact ((Equiv.addRight (unit i)).summable_iff
      (f := fun x : Site d => orientedLayer d l x ^ 2)).mpr (summable_orientedLayer_sq l)
  rw [tsum_congr (orientedCharge_eq hd l),
    (((summable_sum (s := univ) (fun i _ => hs i)).div_const (d : ℝ)).tsum_sub
      (summable_orientedLayer_sq (l + 1))), tsum_div_const,
    Summable.tsum_finsetSum (fun i _ => hs i)]
  have he : ∀ i : Fin d, (∑' x : Site d, orientedLayer d l (x + unit i) ^ 2) =
      ∑' x : Site d, orientedLayer d l x ^ 2 := by
    intro i
    exact (Equiv.addRight (unit i)).tsum_eq (fun x : Site d => orientedLayer d l x ^ 2)
  simp only [he, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  exact mul_div_cancel_left₀ _ (ne_of_gt (show (0 : ℝ) < d by exact_mod_cast hd))

theorem orientedGreen_centered (m : ℕ) (x : Site d) (i : Fin d) :
    orientedGreen d m (x + unit i) - (∑ j : Fin d, orientedGreen d m (x + unit j)) / d =
      ∑ l ∈ range m, orientedDifference d l x i := by
  simp only [orientedGreen, orientedDifference, sum_sub_distrib, orientedLayer_succ,
    sum_div]
  rw [sum_comm]

theorem orientedDifference_sum_sq (m : ℕ) (x : Site d) (i : Fin d) :
    (∑ l ∈ range m, orientedDifference d l x i) ^ 2 =
      ∑ l ∈ range m, orientedDifference d l x i ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hz : (∑ l ∈ range m, orientedDifference d l x i) * orientedDifference d m x i = 0 := by
      rw [sum_mul]
      exact sum_eq_zero fun l hl => orientedDifference_mul_eq_zero (ne_of_lt (mem_range.mp hl)) x i
    rw [sum_range_succ, sum_range_succ, ← ih]
    nlinarith

theorem orientedGamma_eq_sum (m : ℕ) (x : Site d) :
    orientedGamma d m x = ∑ l ∈ range m, orientedCharge d l x := by
  simp only [orientedGamma, orientedGreen_centered, orientedDifference_sum_sq,
    orientedCharge, ← sum_div]
  rw [sum_comm]

theorem orientedGamma_mono (x : Site d) : Monotone fun m => orientedGamma d m x := by
  intro m n hmn
  simp only [orientedGamma_eq_sum]
  exact sum_le_sum_of_subset_of_nonneg (range_mono hmn) (fun l _ _ => orientedCharge_nonneg l x)

theorem tsum_orientedGamma (hd : 1 ≤ d) (m : ℕ) :
    (∑' x, orientedGamma d m x) = 1 - ∑' x : Site d, orientedLayer d m x ^ 2 := by
  rw [tsum_congr (orientedGamma_eq_sum m),
    Summable.tsum_finsetSum (fun l _ => summable_orientedCharge hd l)]
  simp only [tsum_orientedCharge hd]
  rw [sum_range_sub' (fun l => ∑' x : Site d, orientedLayer d l x ^ 2) m]
  simp [orientedLayer]

theorem tsum_orientedGamma_le_one (hd : 1 ≤ d) (m : ℕ) : ∑' x, orientedGamma d m x ≤ 1 := by
  rw [tsum_orientedGamma hd]
  exact sub_le_self _ (tsum_nonneg fun _ => sq_nonneg _)

end Parking
