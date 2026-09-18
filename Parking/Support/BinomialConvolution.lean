/- Finite binomial convolution and the convex square estimate for delayed layers. -/
import Parking.Support.OrientedBinomial

noncomputable section
namespace Parking
open LatticeProb Finset

theorem tsum_binomLaw (l : ℕ) : ∑' j : ℤ, binomLaw l j = 1 := by
  have hs : Function.support (orientedLayer 2 l) ⊆ Set.range (orientedLayerPoint l) := by
    intro x hx
    exact ⟨-x 0, orientedLayerPoint_eq (orientedLayer_height hx)⟩
  have he := (orientedLayerPoint_injective l).tsum_eq hs
  simp only [orientedLayer_at_layerPoint] at he
  exact he.trans (tsum_orientedLayer (by norm_num) l)

theorem binomLaw_zero_outside {l : ℕ} {j : ℤ} (hj : j ∉ Icc (0 : ℤ) (l : ℤ)) :
    binomLaw l j = 0 := by
  rw [mem_Icc, not_and_or, not_le, not_le] at hj
  exact hj.elim (binomLaw_of_neg l) (binomLaw_of_gt l)

theorem sum_binomLaw (l : ℕ) : ∑ j ∈ Icc (0 : ℤ) (l : ℤ), binomLaw l j = 1 := by
  have he : (∑' j : ℤ, binomLaw l j) = ∑ j ∈ Icc (0 : ℤ) (l : ℤ), binomLaw l j :=
    tsum_eq_sum (fun j hj => binomLaw_zero_outside hj)
  exact he.symm.trans (tsum_binomLaw l)

theorem binomLaw_convolution (n h : ℕ) (j : ℤ) :
    binomLaw (n + h) j = ∑ k ∈ Icc (0 : ℤ) (h : ℤ), binomLaw h k * binomLaw n (j - k) := by
  induction n generalizing j with
  | zero =>
    simp only [zero_add, binomLaw_zero]
    have he : ∀ k : ℤ, j - k = 0 ↔ k = j := fun k => by omega
    simp only [he, mul_ite, mul_one, mul_zero, sum_ite_eq']
    by_cases hj : j ∈ Icc (0 : ℤ) (h : ℤ)
    · simp [hj]
    · simp [hj, binomLaw_zero_outside hj]
  | succ n ih =>
    rw [show n + 1 + h = (n + h) + 1 by omega, binomLaw_succ, ih, ih]
    have he : ∀ k : ℤ, binomLaw h k * binomLaw (n + 1) (j - k) =
        (binomLaw h k * binomLaw n (j - 1 - k) + binomLaw h k * binomLaw n (j - k)) / 2 := by
      intro k
      rw [binomLaw_succ, show j - k - 1 = j - 1 - k by ring]
      ring
    rw [sum_congr rfl (fun k _ => he k), ← sum_div, sum_add_distrib]

theorem square_weighted_sum_le {ι : Type*} (S : Finset ι) (w a : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hs : ∑ i ∈ S, w i = 1) :
    (∑ i ∈ S, w i * a i) ^ 2 ≤ ∑ i ∈ S, w i * a i ^ 2 := by
  have h := sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (r := fun i => w i * a i) hw
    (fun i hi => mul_nonneg (hw i hi) (sq_nonneg (a i)))
    (fun i _ => by nlinarith only [sq_nonneg (w i * a i)])
  simpa only [hs, one_mul] using h

theorem binomLaw_convolution_difference_sq (n h : ℕ) (j D : ℤ) :
    (binomLaw (n + h) j - binomLaw n (j - D)) ^ 2 ≤
      ∑ k ∈ Icc (0 : ℤ) (h : ℤ), binomLaw h k * (binomLaw n (j - k) - binomLaw n (j - D)) ^ 2 := by
  have he : binomLaw (n + h) j - binomLaw n (j - D) =
      ∑ k ∈ Icc (0 : ℤ) (h : ℤ), binomLaw h k * (binomLaw n (j - k) - binomLaw n (j - D)) := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, sum_binomLaw, one_mul,
      binomLaw_convolution]
  rw [he]
  exact square_weighted_sum_le _ _ _ (fun k _ => binomLaw_nonneg h k) (sum_binomLaw h)

end Parking
