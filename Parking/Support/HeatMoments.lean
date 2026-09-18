/-
The mass and the second moment of the one-dimensional kernel, and the
Chebyshev bound on its tail that Step 3 of `lem:gamma-sum` needs.

In dimension one `Γ_m(y)` is a square of the gradient of `g_m`, and the
gradient is exactly twice the tail `P_0(X_m>y)` of the kernel
(`LatticeProb.srwGreen_one_sub`).  What the sum of the lemma therefore needs
is a bound on that tail which is monotone in the horizon, so that the supremum
over `m ≤ n` costs nothing.  The kernel has finite support, so its mass and its
second moment are computed by one induction each against the nearest-neighbour
recursion, and Chebyshev's inequality turns the second moment `m` into the tail
bound `m/(y+1)^2`.
-/
import Parking.Support.GreenBridge

noncomputable section

namespace Parking

open LatticeProb Finset

/-- The one-dimensional kernel, read as a function on the integers. -/
def heat1 (m : ℕ) (a : ℤ) : ℝ := LatticeProb.srwHeat 1 m ![a]

theorem heat1_nonneg (m : ℕ) (a : ℤ) : 0 ≤ heat1 m a := srwHeat_nonneg _ _

theorem heat1_succ (m : ℕ) (a : ℤ) :
    heat1 (m + 1) a = (heat1 m (a - 1) + heat1 m (a + 1)) / 2 :=
  srwHeat_one_succ m a

theorem heat1_neg (m : ℕ) (a : ℤ) : heat1 m (-a) = heat1 m a := by
  have h : (-(![a] : Site 1)) = ![-a] := by
    funext i
    fin_cases i
    simp
  unfold heat1
  rw [← heat_eq_srwHeat, ← heat_eq_srwHeat, ← h, heat_neg]

/-- The kernel vanishes outside the interval of radius `m`. -/
theorem heat1_eq_zero_of_notMem {m : ℕ} {a : ℤ} (ha : a ∉ Finset.Icc (-(m : ℤ)) (m : ℤ)) :
    heat1 m a = 0 := by
  rw [Finset.mem_Icc, not_and_or] at ha
  by_cases h : (m : ℤ) < a
  · exact srwHeat_one_eq_zero_of_gt h
  · have hneg : (m : ℤ) < -a := by
      rcases ha with h1 | h1 <;> omega
    rw [← heat1_neg]
    exact srwHeat_one_eq_zero_of_gt hneg

/-- Every weighting of the kernel is summable, because the kernel has finite
support. -/
theorem summable_heat1_weight (m : ℕ) (g : ℤ → ℝ) :
    Summable fun a : ℤ => g a * heat1 m a := by
  refine summable_of_ne_finset_zero (s := Finset.Icc (-(m : ℤ)) (m : ℤ)) ?_
  intro a ha
  rw [heat1_eq_zero_of_notMem ha, mul_zero]

theorem summable_heat1 (m : ℕ) : Summable (heat1 m) := by
  simpa using summable_heat1_weight m (fun _ => (1 : ℝ))

theorem heat1_zero_zero : heat1 0 0 = 1 := by
  unfold heat1
  rw [srwHeat_zero, if_pos]
  funext i
  fin_cases i
  simp

theorem heat1_zero_of_ne {a : ℤ} (ha : a ≠ 0) : heat1 0 a = 0 := by
  refine heat1_eq_zero_of_notMem ?_
  simp only [Finset.mem_Icc, Nat.cast_zero, neg_zero]
  omega

/-- Shifting the index does not change a sum over the integers. -/
theorem tsum_int_shift (g : ℤ → ℝ) (c : ℤ) : ∑' a : ℤ, g (a + c) = ∑' a : ℤ, g a :=
  (Equiv.addRight c).tsum_eq g

/-- The kernel is a probability distribution. -/
theorem tsum_heat1 (m : ℕ) : ∑' a : ℤ, heat1 m a = 1 := by
  induction m with
  | zero =>
      rw [tsum_eq_single 0 fun a ha => heat1_zero_of_ne ha, heat1_zero_zero]
  | succ m ih =>
      have hsplit : ∀ a : ℤ, heat1 (m + 1) a
          = (1 / 2 : ℝ) * heat1 m (a + (-1)) + (1 / 2 : ℝ) * heat1 m (a + 1) := by
        intro a
        rw [heat1_succ]
        have : a + (-1 : ℤ) = a - 1 := by ring
        rw [this]
        ring
      have h1 : Summable fun a : ℤ => (1 / 2 : ℝ) * heat1 m (a + (-1)) := by
        refine summable_of_ne_finset_zero (s := Finset.Icc (-(m : ℤ) - 1) ((m : ℤ) + 1)) ?_
        intro a ha
        rw [Finset.mem_Icc] at ha
        rw [heat1_eq_zero_of_notMem (by rw [Finset.mem_Icc]; omega), mul_zero]
      have h2 : Summable fun a : ℤ => (1 / 2 : ℝ) * heat1 m (a + 1) := by
        refine summable_of_ne_finset_zero (s := Finset.Icc (-(m : ℤ) - 1) ((m : ℤ) + 1)) ?_
        intro a ha
        rw [Finset.mem_Icc] at ha
        rw [heat1_eq_zero_of_notMem (by rw [Finset.mem_Icc]; omega), mul_zero]
      rw [tsum_congr hsplit, h1.tsum_add h2,
        tsum_int_shift (fun a : ℤ => (1 / 2 : ℝ) * heat1 m a) (-1),
        tsum_int_shift (fun a : ℤ => (1 / 2 : ℝ) * heat1 m a) 1,
        tsum_mul_left, ih]
      norm_num

/-- The second moment of the kernel is the number of steps. -/
theorem tsum_sq_heat1 (m : ℕ) : ∑' a : ℤ, ((a : ℝ) ^ 2 * heat1 m a) = (m : ℝ) := by
  induction m with
  | zero =>
      rw [tsum_eq_single 0 fun a ha => by rw [heat1_zero_of_ne ha, mul_zero]]
      simp
  | succ m ih =>
      have hsplit : ∀ a : ℤ, (a : ℝ) ^ 2 * heat1 (m + 1) a
          = ((((a + (-1) : ℤ) : ℝ) + 1) ^ 2 / 2) * heat1 m (a + (-1))
            + ((((a + 1 : ℤ) : ℝ) - 1) ^ 2 / 2) * heat1 m (a + 1) := by
        intro a
        rw [heat1_succ]
        have hc : a + (-1 : ℤ) = a - 1 := by ring
        rw [hc]
        push_cast
        ring
      have hsupp : ∀ (g : ℤ → ℝ) (c : ℤ),
          Summable fun a : ℤ => g a * heat1 m (a + c) := by
        intro g c
        refine summable_of_ne_finset_zero
          (s := Finset.Icc (-(m : ℤ) - |c|) ((m : ℤ) + |c|)) ?_
        intro a ha
        rw [Finset.mem_Icc] at ha
        rw [heat1_eq_zero_of_notMem (by rw [Finset.mem_Icc]; rcases abs_cases c with ⟨h, _⟩ | ⟨h, _⟩ <;> omega), mul_zero]
      have h1 := hsupp (fun a : ℤ => (((a + (-1) : ℤ) : ℝ) + 1) ^ 2 / 2) (-1)
      have h2 := hsupp (fun a : ℤ => (((a + 1 : ℤ) : ℝ) - 1) ^ 2 / 2) 1
      rw [tsum_congr hsplit, h1.tsum_add h2,
        tsum_int_shift (fun a : ℤ => (((a : ℤ) : ℝ) + 1) ^ 2 / 2 * heat1 m a) (-1),
        tsum_int_shift (fun a : ℤ => (((a : ℤ) : ℝ) - 1) ^ 2 / 2 * heat1 m a) 1]
      have hA : Summable fun a : ℤ => (((a : ℤ) : ℝ) + 1) ^ 2 / 2 * heat1 m a :=
        summable_heat1_weight m _
      have hB : Summable fun a : ℤ => (((a : ℤ) : ℝ) - 1) ^ 2 / 2 * heat1 m a :=
        summable_heat1_weight m _
      rw [← hA.tsum_add hB]
      have hcomb : ∀ a : ℤ, ((a : ℝ) + 1) ^ 2 / 2 * heat1 m a + ((a : ℝ) - 1) ^ 2 / 2 * heat1 m a
          = (a : ℝ) ^ 2 * heat1 m a + heat1 m a := by
        intro a
        ring
      rw [tsum_congr hcomb]
      have hC : Summable fun a : ℤ => (a : ℝ) ^ 2 * heat1 m a := summable_heat1_weight m _
      rw [hC.tsum_add (summable_heat1 m), ih, tsum_heat1]
      push_cast
      ring

/-! ### The tail of the kernel -/

/-- The tail sum, read as a sum over the integers it ranges over. -/
theorem srwTail_eq_sum_image (m : ℕ) (y : ℤ) :
    srwTail m y = ∑ a ∈ (Finset.range (m + 1)).image (fun k : ℕ => y + 1 + (k : ℤ)),
      heat1 m a := by
  rw [srwTail, Finset.sum_image]
  · rfl
  · intro k _ l _ h
    simp only [add_right_inj] at h
    exact_mod_cast h

theorem srwTail_le_one (m : ℕ) (y : ℤ) : srwTail m y ≤ 1 := by
  rw [srwTail_eq_sum_image]
  refine le_trans ((summable_heat1 m).sum_le_tsum _ (fun a _ => heat1_nonneg m a)) ?_
  rw [tsum_heat1]

/-- **Chebyshev's inequality for the kernel.**  The tail past `y` is at most
the second moment divided by `(y+1)^2`. -/
theorem srwTail_le_sq (m : ℕ) {y : ℤ} (hy : 0 ≤ y) :
    srwTail m y ≤ (m : ℝ) / ((y : ℝ) + 1) ^ 2 := by
  have hpos : (0 : ℝ) < ((y : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
    positivity
  rw [srwTail_eq_sum_image, le_div_iff₀ hpos]
  have hstep : ∀ a ∈ (Finset.range (m + 1)).image (fun k : ℕ => y + 1 + (k : ℤ)),
      heat1 m a * ((y : ℝ) + 1) ^ 2 ≤ (a : ℝ) ^ 2 * heat1 m a := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨k, _, rfl⟩ := ha
    have hy' : (0 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
    have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have hcast : ((y + 1 + (k : ℤ) : ℤ) : ℝ) = (y : ℝ) + 1 + (k : ℝ) := by push_cast; ring
    rw [hcast]
    have hsq : ((y : ℝ) + 1) ^ 2 ≤ ((y : ℝ) + 1 + (k : ℝ)) ^ 2 := by nlinarith
    have := heat1_nonneg m (y + 1 + (k : ℤ))
    nlinarith
  rw [Finset.sum_mul]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  refine le_trans ((summable_heat1_weight m fun a : ℤ => (a : ℝ) ^ 2).sum_le_tsum _
    (fun a _ => ?_)) ?_
  · exact mul_nonneg (by positivity) (heat1_nonneg m a)
  · rw [tsum_sq_heat1]

end Parking

end
