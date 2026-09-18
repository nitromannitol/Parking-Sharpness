/- The squared coefficient bound for two times of the directed linear potential. -/
import Parking.Support.OrientedNorm
import Parking.Support.BinomialDelay
import Parking.Support.BinomialMoments

noncomputable section
namespace Parking
open LatticeProb Finset

theorem layerHeight_sub {d : ℕ} (x y : Site d) : layerHeight (x - y) = layerHeight x - layerHeight y := by
  simp [layerHeight, sum_sub_distrib]

/-- The difference of two layer coefficients viewed from the endpoints of a
directed path with length `h` and first-coordinate displacement `D`. -/
def orientedLayerDelay (h : ℕ) (D : ℤ) (n : ℕ) (z : Site 2) : ℝ :=
  orientedLayer 2 (n + h) z - orientedLayer 2 n (z - orientedLayerPoint h D)

theorem orientedLayerDelay_height {h n : ℕ} {D : ℤ} {z : Site 2}
    (hz : orientedLayerDelay h D n z ≠ 0) : layerHeight z = -((n + h : ℕ) : ℤ) := by
  by_cases hp : orientedLayer 2 (n + h) z = 0
  · have hq : orientedLayer 2 n (z - orientedLayerPoint h D) ≠ 0 := by
      intro hq
      exact hz (by simp [orientedLayerDelay, hp, hq])
    have he := orientedLayer_height hq
    rw [layerHeight_sub, layerHeight_orientedLayerPoint] at he
    push_cast
    omega
  · exact orientedLayer_height hp

theorem orientedLayerDelay_mul_eq_zero {h n m : ℕ} (D : ℤ) (hnm : n ≠ m) (z : Site 2) :
    orientedLayerDelay h D n z * orientedLayerDelay h D m z = 0 := by
  by_contra hc
  obtain ⟨hn, hm⟩ := mul_ne_zero_iff.mp hc
  have h1 := orientedLayerDelay_height hn
  have h2 := orientedLayerDelay_height hm
  exact hnm (by omega)

theorem orientedLayer_mul_delay_eq_zero {h l n : ℕ} (D : ℤ) (hln : l ≠ n + h) (z : Site 2) :
    orientedLayer 2 l z * orientedLayerDelay h D n z = 0 := by
  by_contra hc
  obtain ⟨hl, hn⟩ := mul_ne_zero_iff.mp hc
  have h1 := orientedLayer_height hl
  have h2 := orientedLayerDelay_height hn
  exact hln (by omega)

theorem orientedLayerPoint_sub (n h : ℕ) (j D : ℤ) :
    orientedLayerPoint (n + h) j - orientedLayerPoint h D = orientedLayerPoint n (j - D) := by
  funext i
  fin_cases i
  · change -j - -D = -(j - D)
    ring
  · change (j - ((n + h : ℕ) : ℤ)) - (D - (h : ℤ)) = (j - D) - (n : ℤ)
    push_cast
    ring

theorem orientedLayerDelay_at_point (n h : ℕ) (j D : ℤ) :
    orientedLayerDelay h D n (orientedLayerPoint (n + h) j) =
      binomLaw (n + h) j - binomLaw n (j - D) := by
  rw [orientedLayerDelay, orientedLayerPoint_sub, orientedLayer_at_layerPoint,
    orientedLayer_at_layerPoint]

theorem tsum_orientedLayerDelay_sq (n h : ℕ) (D : ℤ) :
    (∑' z : Site 2, orientedLayerDelay h D n z ^ 2) =
      ∑' j : ℤ, (binomLaw (n + h) j - binomLaw n (j - D)) ^ 2 := by
  have hs : Function.support (fun z : Site 2 => orientedLayerDelay h D n z ^ 2) ⊆
      Set.range (orientedLayerPoint (n + h)) := by
    intro z hz
    have hn : orientedLayerDelay h D n z ≠ 0 := by
      intro hn
      exact hz (by simp [hn])
    exact ⟨-z 0, orientedLayerPoint_eq (orientedLayerDelay_height hn)⟩
  rw [← (orientedLayerPoint_injective (n + h)).tsum_eq hs]
  simp only [orientedLayerDelay_at_point]

theorem summable_orientedLayerDelay_sq (n h : ℕ) (D : ℤ) :
    Summable fun z : Site 2 => orientedLayerDelay h D n z ^ 2 := by
  classical
  let S := boxFinset (0 : Site 2) (n + h) ∪
    (boxFinset (0 : Site 2) n).image (fun z => z + orientedLayerPoint h D)
  refine summable_of_ne_finset_zero (s := S) fun z hz => ?_
  have hp : z ∉ boxFinset (0 : Site 2) (n + h) := fun hp => hz (mem_union_left _ hp)
  have hq : z - orientedLayerPoint h D ∉ boxFinset (0 : Site 2) n := by
    intro hq
    exact hz (mem_union_right _ (mem_image.mpr ⟨z - orientedLayerPoint h D, hq, sub_add_cancel _ _⟩))
  rw [orientedLayerDelay, orientedLayer_eq_zero_of_notMem hp, orientedLayer_eq_zero_of_notMem hq]
  norm_num

theorem sum_sq_of_pairwise_mul_eq_zero {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → f i * f j = 0) :
    (∑ i ∈ S, f i) ^ 2 = ∑ i ∈ S, f i ^ 2 := by
  classical
  rw [pow_two, sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [mul_sum, sum_eq_single i]
  · exact (pow_two _).symm
  · intro j hj hji
    exact hf i hi j hj hji.symm
  · exact fun h => (h hi).elim

theorem orientedGreen_delay_split (N h : ℕ) (D : ℤ) (z : Site 2) :
    orientedGreen 2 (N + h) z - orientedGreen 2 N (z - orientedLayerPoint h D) =
      orientedGreen 2 h z + ∑ n ∈ range N, orientedLayerDelay h D n z := by
  simp only [orientedGreen, orientedLayerDelay, sum_sub_distrib]
  rw [show N + h = h + N by omega, sum_range_add]
  have he : (∑ x ∈ range N, orientedLayer 2 (h + x) z) = ∑ x ∈ range N, orientedLayer 2 (x + h) z := by
    apply sum_congr rfl
    intro x _
    rw [Nat.add_comm h x]
  rw [he]
  ring

theorem orientedGreen_delay_sq (N h : ℕ) (D : ℤ) (z : Site 2) :
    (orientedGreen 2 (N + h) z - orientedGreen 2 N (z - orientedLayerPoint h D)) ^ 2 =
      orientedGreen 2 h z ^ 2 + ∑ n ∈ range N, orientedLayerDelay h D n z ^ 2 := by
  have hcross : orientedGreen 2 h z * (∑ n ∈ range N, orientedLayerDelay h D n z) = 0 := by
    rw [orientedGreen, sum_mul]
    apply sum_eq_zero
    intro l hl
    rw [mul_sum]
    apply sum_eq_zero
    intro n _
    exact orientedLayer_mul_delay_eq_zero D (by have := mem_range.mp hl; omega) z
  have hsq := sum_sq_of_pairwise_mul_eq_zero (range N) (fun n => orientedLayerDelay h D n z)
    (fun n _ m _ hnm => orientedLayerDelay_mul_eq_zero D hnm z)
  rw [orientedGreen_delay_split]
  nlinarith

theorem tsum_orientedGreen_delay_sq (N h : ℕ) (D : ℤ) :
    (∑' z : Site 2, (orientedGreen 2 (N + h) z - orientedGreen 2 N (z - orientedLayerPoint h D)) ^ 2) =
      (∑ l ∈ range h, conv l 0) +
        ∑ n ∈ range N, ∑' j : ℤ, (binomLaw (n + h) j - binomLaw n (j - D)) ^ 2 := by
  have hg : Summable fun z : Site 2 => orientedGreen 2 h z ^ 2 :=
    (summable_sum (s := range h) (fun l _ => summable_orientedLayer_sq l)).congr
      (fun z => (orientedGreen_sq h z).symm)
  have hd := summable_sum (s := range N) (fun n _ => summable_orientedLayerDelay_sq n h D)
  rw [tsum_congr (orientedGreen_delay_sq N h D), hg.tsum_add hd,
    tsum_orientedGreen_two_sq, Summable.tsum_finsetSum (fun n _ => summable_orientedLayerDelay_sq n h D)]
  simp only [tsum_orientedLayerDelay_sq]

/-- The coefficient bound for two times of the directed potential. -/
theorem orientedGreen_delay_bound (N h : ℕ) (D : ℤ) :
    (∑' z : Site 2, (orientedGreen 2 (N + h) z - orientedGreen 2 N (z - orientedLayerPoint h D)) ^ 2) ≤
      4 * (Real.sqrt h + |(D : ℝ) - (h : ℝ) / 2|) := by
  rw [tsum_orientedGreen_delay_sq]
  have h1 := sum_conv_zero_upper h
  have h2 := sum_binom_delay_difference_le N h D
  have h3 := sum_binom_abs_shift_le h D
  linarith

end Parking
