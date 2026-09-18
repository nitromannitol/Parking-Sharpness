/- The directed layer collision probability from an ordinary return probability. -/
import Parking.Support.OrientedOperators
import Parking.Support.Shift

noncomputable section
namespace Parking
open LatticeProb Finset
variable {d : ℕ}

theorem signedAverage_false_pow (n : ℕ) (f : Site d → ℝ) :
    (signedAverage d false ^ n) f = orientedLayerAverage f n := by
  induction n with
  | zero =>
    funext x
    exact (orientedLayerAverage_zero f x).symm
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    funext x
    rw [signedAverage_false, orientedLayerAverage_succ]

theorem signedAverage_mixed_delta (k l : ℕ) :
    (signedAverage d true ^ k * signedAverage d false ^ l)
      (fun x : Site d => if x = 0 then 1 else 0) 0 =
        ∑' x : Site d, orientedLayer d l x * orientedLayer d k x := by
  rw [((signedAverage_commute (d := d) true false).pow_pow k l).eq,
    Module.End.mul_apply, signedAverage_true_pow_delta, signedAverage_false_pow]
  simp only [orientedLayerAverage, zero_add]

theorem central_binomial_coefficient (n : ℕ) :
    (1 / 2 : ℝ) ^ (2 * n) * (Nat.choose (2 * n) n : ℝ) = conv n 0 := by
  rw [pow_mul, conv_zero_eq, Nat.centralBinom]
  norm_num only [show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num]
  rw [div_pow, one_pow]
  ring

/-- A return of the signed walk forces equal numbers of positive and negative
steps. The surviving middle term is the directed layer collision probability. -/
theorem orientedLayer_collision_identity (n : ℕ) :
    srwHeat d (2 * n) 0 = conv n 0 * ∑' x : Site d, orientedLayer d n x ^ 2 := by
  classical
  have h := congrArg (fun A : Module.End ℝ (Site d → ℝ) =>
    A (fun x : Site d => if x = 0 then 1 else 0) 0)
    (simpleAverage_pow_binomial (d := d) (2 * n))
  rw [simpleAverage_pow_delta] at h
  simp only [← Nat.cast_smul_eq_nsmul ℝ, LinearMap.smul_apply, LinearMap.sum_apply,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul, signedAverage_mixed_delta] at h
  have hs : (∑ m ∈ antidiagonal (2 * n), (Nat.choose (2 * n) m.1 : ℝ) *
      (∑' x : Site d, orientedLayer d m.2 x * orientedLayer d m.1 x)) =
        (Nat.choose (2 * n) n : ℝ) * ∑' x : Site d, orientedLayer d n x ^ 2 := by
    rw [sum_eq_single (n, n)]
    · simp only [pow_two]
    · intro m hm hmn
      have hsum := mem_antidiagonal.mp hm
      have hne : m.2 ≠ m.1 := by
        intro he
        apply hmn
        apply Prod.ext <;> dsimp only <;> omega
      simp only [orientedLayer_mul_eq_zero hne, tsum_zero, mul_zero]
    · intro hm
      exact False.elim (hm (mem_antidiagonal.mpr (by omega)))
  rw [hs, ← mul_assoc, central_binomial_coefficient] at h
  exact h

end Parking
