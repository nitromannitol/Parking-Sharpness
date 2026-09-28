import Parking.Support.OrientedNorm
import Parking.Support.BinomialDelay
import Parking.Support.BinomialMoments

/-!
# Squared coefficient bound for two times

The squared coefficient bound for two times of the directed linear potential.
-/

open LatticeProb.Walk (conv)

noncomputable section
namespace Parking
open LatticeProb Finset

/-- `layerHeight` is additive under subtraction of sites, by unfolding its definition as
a coordinate sum. -/
theorem layerHeight_sub {d : ℕ} (x y : Site d) :
    layerHeight (x - y) = layerHeight x - layerHeight y := by
  simp [layerHeight, sum_sub_distrib]

/-- The difference of two layer coefficients viewed from the endpoints of a
directed path with length `h` and first-coordinate displacement `D`. -/
def orientedLayerDelay (h : ℕ) (D : ℤ) (n : ℕ) (z : Site 2) : ℝ :=
  orientedLayer 2 (n + h) z - orientedLayer 2 n (z - orientedLayerPoint h D)

/-- If the layer delay `orientedLayerDelay h D n z` is nonzero, then `z` lies at height
`-(n + h)`: when the first term `orientedLayer 2 (n + h) z` vanishes the second term must
be nonzero, and `orientedLayer_height` together with `layerHeight_orientedLayerPoint`
pins down the height; otherwise `orientedLayer_height` applies directly to the first
term. -/
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

/-- For `n ≠ m` the layer delays `orientedLayerDelay h D n z` and
`orientedLayerDelay h D m z` cannot both be nonzero, since `orientedLayerDelay_height`
would force `n` and `m` to give the same height; hence their product is zero. -/
theorem orientedLayerDelay_mul_eq_zero {h n m : ℕ} (D : ℤ) (hnm : n ≠ m) (z : Site 2) :
    orientedLayerDelay h D n z * orientedLayerDelay h D m z = 0 := by
  by_contra hc
  obtain ⟨hn, hm⟩ := mul_ne_zero_iff.mp hc
  have h1 := orientedLayerDelay_height hn
  have h2 := orientedLayerDelay_height hm
  exact hnm (by omega)

/-- For `l ≠ n + h` the plain layer `orientedLayer 2 l z` and the delay
`orientedLayerDelay h D n z` cannot both be nonzero, since `orientedLayer_height` and
`orientedLayerDelay_height` would force incompatible heights; hence their product is
zero. -/
theorem orientedLayer_mul_delay_eq_zero {h l n : ℕ} (D : ℤ) (hln : l ≠ n + h) (z : Site 2) :
    orientedLayer 2 l z * orientedLayerDelay h D n z = 0 := by
  by_contra hc
  obtain ⟨hl, hn⟩ := mul_ne_zero_iff.mp hc
  have h1 := orientedLayer_height hl
  have h2 := orientedLayerDelay_height hn
  exact hln (by omega)

/-- Layer points satisfy the additive shift identity
`orientedLayerPoint (n + h) j - orientedLayerPoint h D = orientedLayerPoint n (j - D)`,
checked coordinatewise on `Fin 2`. -/
theorem orientedLayerPoint_sub (n h : ℕ) (j D : ℤ) :
    orientedLayerPoint (n + h) j - orientedLayerPoint h D = orientedLayerPoint n (j - D) := by
  funext i
  fin_cases i
  · change -j - -D = -(j - D)
    ring
  · change (j - ((n + h : ℕ) : ℤ)) - (D - (h : ℤ)) = (j - D) - (n : ℤ)
    push_cast
    ring

/-- Evaluating the layer delay at the layer point `orientedLayerPoint (n + h) j` gives the
difference of binomial laws `binomLaw (n + h) j - binomLaw n (j - D)`, via
`orientedLayerPoint_sub` and `orientedLayer_at_layerPoint`. -/
theorem orientedLayerDelay_at_point (n h : ℕ) (j D : ℤ) :
    orientedLayerDelay h D n (orientedLayerPoint (n + h) j) =
      binomLaw (n + h) j - binomLaw n (j - D) := by
  rw [orientedLayerDelay, orientedLayerPoint_sub, orientedLayer_at_layerPoint,
    orientedLayer_at_layerPoint]

/-- The sum over all sites of the squared layer delay equals the sum over `j : ℤ` of the
squared binomial-law difference, since the support of the summand is exactly the
(injective) range of `orientedLayerPoint (n + h)`, on which `orientedLayerDelay_at_point`
identifies the summand. -/
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

/-- The squared layer delay is summable over `Site 2`, since it vanishes outside the
finite set `S` formed as the union of the box `boxFinset 0 (n + h)` and the shifted image
of `boxFinset 0 n`. -/
theorem summable_orientedLayerDelay_sq (n h : ℕ) (D : ℤ) :
    Summable fun z : Site 2 => orientedLayerDelay h D n z ^ 2 := by
  classical
  let S := boxFinset (0 : Site 2) (n + h) ∪
    (boxFinset (0 : Site 2) n).image (fun z => z + orientedLayerPoint h D)
  refine summable_of_ne_finset_zero (s := S) fun z hz => ?_
  have hp : z ∉ boxFinset (0 : Site 2) (n + h) := fun hp => hz (mem_union_left _ hp)
  have hq : z - orientedLayerPoint h D ∉ boxFinset (0 : Site 2) n := by
    intro hq
    exact hz (mem_union_right _
      (mem_image.mpr ⟨z - orientedLayerPoint h D, hq, sub_add_cancel _ _⟩))
  rw [orientedLayerDelay, orientedLayer_eq_zero_of_notMem hp, orientedLayer_eq_zero_of_notMem hq]
  norm_num

/-- If `f` has pairwise-vanishing products off the diagonal on a finite index set `S`,
then `(∑ i ∈ S, f i) ^ 2 = ∑ i ∈ S, f i ^ 2`, by expanding the square and discarding the
cross terms. -/
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

/-- The difference of two truncated Green functions at shifted arguments splits as a
Green function of length `h` plus a sum of layer delays over `n < N`, by reindexing the
sum `range (h + N)` into its first `h` and remaining `N` terms. -/
theorem orientedGreen_delay_split (N h : ℕ) (D : ℤ) (z : Site 2) :
    orientedGreen 2 (N + h) z - orientedGreen 2 N (z - orientedLayerPoint h D) =
      orientedGreen 2 h z + ∑ n ∈ range N, orientedLayerDelay h D n z := by
  simp only [orientedGreen, orientedLayerDelay, sum_sub_distrib]
  rw [show N + h = h + N by omega, sum_range_add]
  have he : (∑ x ∈ range N, orientedLayer 2 (h + x) z) =
      ∑ x ∈ range N, orientedLayer 2 (x + h) z := by
    apply sum_congr rfl
    intro x _
    rw [Nat.add_comm h x]
  rw [he]
  ring

/-- Squaring the splitting identity `orientedGreen_delay_split` and dropping the cross
term, which vanishes since `orientedGreen 2 h z` multiplies each delay to `0`, together
with the pairwise orthogonality of the delays across different `n`
(`sum_sq_of_pairwise_mul_eq_zero`), gives the sum-of-squares decomposition. -/
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

/-- Summing the pointwise identity `orientedGreen_delay_sq` over all sites evaluates each
piece: the Green-function term becomes `∑ l ∈ range h, conv l 0` (`tsum_orientedGreen_two_sq`),
and each delay term becomes the `tsum` from `tsum_orientedLayerDelay_sq`. -/
theorem tsum_orientedGreen_delay_sq (N h : ℕ) (D : ℤ) :
    (∑' z : Site 2,
        (orientedGreen 2 (N + h) z - orientedGreen 2 N (z - orientedLayerPoint h D)) ^ 2) =
      (∑ l ∈ range h, conv l 0) +
        ∑ n ∈ range N, ∑' j : ℤ, (binomLaw (n + h) j - binomLaw n (j - D)) ^ 2 := by
  have hg : Summable fun z : Site 2 => orientedGreen 2 h z ^ 2 :=
    (summable_sum (s := range h) (fun l _ => summable_orientedLayer_sq l)).congr
      (fun z => (orientedGreen_sq h z).symm)
  have hd := summable_sum (s := range N) (fun n _ => summable_orientedLayerDelay_sq n h D)
  rw [tsum_congr (orientedGreen_delay_sq N h D), hg.tsum_add hd,
    tsum_orientedGreen_two_sq,
    Summable.tsum_finsetSum (fun n _ => summable_orientedLayerDelay_sq n h D)]
  simp only [tsum_orientedLayerDelay_sq]

/-- The coefficient bound for two times of the directed potential. -/
theorem orientedGreen_delay_bound (N h : ℕ) (D : ℤ) :
    (∑' z : Site 2,
        (orientedGreen 2 (N + h) z - orientedGreen 2 N (z - orientedLayerPoint h D)) ^ 2) ≤
      4 * (Real.sqrt h + |(D : ℝ) - (h : ℝ) / 2|) := by
  rw [tsum_orientedGreen_delay_sq]
  have h1 := sum_conv_zero_upper h
  have h2 := sum_binom_delay_difference_le N h D
  have h3 := sum_binom_abs_shift_le h D
  linarith

end Parking
