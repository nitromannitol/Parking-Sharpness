/-
The a priori bounds on the divisible sandpile odometer `u_n` of a realization,
in the same shape as the bounds on `U_n` and on the error `w_n`: measurability,
nonnegativity, and the pathwise bound by the configuration over a box, which
gives every moment of `u_n(x)` under the law.

The pathwise bound is the exact analogue of `Parking.U_le_confBox`: `u_{k+1}`
adds `η(x)⁺` to an average of values of `u_k` at the neighbours of `x`, and the
box of radius `k` around a neighbour of `x` sits inside the box of radius
`k + 1` around `x`.
-/
import Parking.Support.ConfMoments
import Parking.Support.WBound
import Parking.Support.KernelBridge

noncomputable section

namespace Parking

open MeasureTheory LatticeProb Finset

variable {d : ℕ}

/-! ### The walk operator against a bound at the neighbours -/

theorem walkOp_const (hd : 1 ≤ d) (B : ℝ) (x : Site d) :
    walkOp (fun _ : Site d => B) x = B := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [walkOp, nbrSum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- The walk average is at most a bound that holds at the `2d` neighbours. -/
theorem walkOp_le_of_nbr (hd : 1 ≤ d) {f : Site d → ℝ} {B : ℝ} {x : Site d}
    (h : ∀ y ∈ nbrFinset x, f y ≤ B) : walkOp f x ≤ B := by
  have hd0 : (0 : ℝ) < 2 * (d : ℝ) := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    linarith
  have hsum : nbrSum f x ≤ 2 * (d : ℝ) * B := by
    rw [nbrSum]
    have hterm : ∀ i : Fin d, f (x + unit i) + f (x - unit i) ≤ B + B := fun i =>
      add_le_add (h _ (mem_nbrFinset_add x i)) (h _ (mem_nbrFinset_sub x i))
    calc ∑ i : Fin d, (f (x + unit i) + f (x - unit i))
        ≤ ∑ _i : Fin d, (B + B) := Finset.sum_le_sum fun i _ => hterm i
      _ = 2 * (d : ℝ) * B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  rw [walkOp, div_le_iff₀ hd0]
  linarith

/-! ### The sandpile odometer of a realization -/

theorem uOf_nonneg (ω : Data d) (n : ℕ) (x : Site d) : 0 ≤ uOf ω n x := by
  cases n with
  | zero => exact le_refl 0
  | succ k => exact le_max_left _ _

/-- **The sandpile odometer against the configuration.**  `u_k(x)` is at most
`k` times the configuration summed over the box of radius `k` about `x`. -/
theorem uOf_le_confBox (hd : 1 ≤ d) (ω : Data d) (k : ℕ) (x : Site d) :
    uOf ω k x ≤ (k : ℝ) * confBox ω x k := by
  induction k generalizing x with
  | zero =>
      have : uOf ω 0 x = 0 := rfl
      rw [this]
      simp
  | succ k ih =>
      have hstep : uOf ω (k + 1) x
          = max 0 ((ω.1 x : ℝ) + walkOp (uOf ω k) x) := rfl
      have hbox : ∀ y ∈ nbrFinset x, uOf ω k y ≤ (k : ℝ) * confBox ω x (k + 1) := by
        intro y hy
        refine (ih y).trans ?_
        have hsub : confBox ω y k ≤ confBox ω x (1 + k) :=
          confBox_le_of_mem ω (nbrFinset_subset_box x hy) k
        have hcomm : confBox ω x (1 + k) = confBox ω x (k + 1) := by
          rw [Nat.add_comm]
        exact mul_le_mul_of_nonneg_left (by rw [← hcomm]; exact hsub) (Nat.cast_nonneg k)
      have hwalk : walkOp (uOf ω k) x ≤ (k : ℝ) * confBox ω x (k + 1) :=
        walkOp_le_of_nbr hd hbox
      have heta : (ω.1 x : ℝ) ≤ confBox ω x (k + 1) := by
        have h0 : (ω.1 x : ℝ) ≤ (((ω.1 x).toNat : ℕ) : ℝ) := by
          rw [toNat_cast_eq_max]; exact le_max_left _ _
        refine h0.trans ?_
        have hmem : x ∈ boxFinset x (k + 1) := mem_boxFinset_iff.mpr (fun i => by simp; positivity)
        have : ((ω.1 x).toNat : ℝ)
            ≤ ((∑ z ∈ boxFinset x (k + 1), (ω.1 z).toNat : ℕ) : ℝ) := by
          exact_mod_cast Finset.single_le_sum
            (f := fun z => (ω.1 z).toNat) (fun z _ => Nat.zero_le _) hmem
        exact this
      have hconf : (0 : ℝ) ≤ confBox ω x (k + 1) := confBox_nonneg _ _ _
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      rw [hstep]
      refine max_le ?_ ?_
      · have : (0 : ℝ) ≤ ((k : ℝ) + 1) * confBox ω x (k + 1) := by positivity
        simpa using this
      · have : (ω.1 x : ℝ) + walkOp (uOf ω k) x
            ≤ confBox ω x (k + 1) + (k : ℝ) * confBox ω x (k + 1) :=
          add_le_add heta hwalk
        refine this.trans ?_
        have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        ring_nf
        nlinarith [hconf]

/-! ### Measurability and the moments -/

theorem measurable_uOf (k : ℕ) (x : Site d) :
    Measurable fun ω : Data d => uOf ω k x := by
  induction k generalizing x with
  | zero => exact measurable_const
  | succ k ih =>
      have hwalk : Measurable fun ω : Data d => walkOp (uOf ω k) x := by
        have heq : (fun ω : Data d => walkOp (uOf ω k) x)
            = fun ω : Data d =>
              (∑ i : Fin d, (uOf ω k (x + unit i) + uOf ω k (x - unit i))) / (2 * (d : ℝ)) :=
          rfl
        rw [heq]
        exact (Finset.measurable_sum _ fun i _ =>
          (ih (x + unit i)).add (ih (x - unit i))).div_const _
      have heta : Measurable fun ω : Data d => ((ω.1 x : ℤ) : ℝ) :=
        (measurable_from_countable' fun m : ℤ => (m : ℝ)).comp
          ((measurable_pi_apply x).comp measurable_fst)
      have hfun : (fun ω : Data d => uOf ω (k + 1) x)
          = fun ω : Data d => max 0 ((ω.1 x : ℝ) + walkOp (uOf ω k) x) := rfl
      rw [hfun]
      exact measurable_const.max (heta.add hwalk)

theorem measurable_u_eval (n : ℕ) (x : Site d) :
    Measurable fun η : Site d → ℝ => u η n x := by
  induction n generalizing x with
  | zero => exact measurable_const
  | succ k ih =>
      have hwalk : Measurable fun η : Site d → ℝ => walkOp (u η k) x := by
        have heq : (fun η : Site d → ℝ => walkOp (u η k) x)
            = fun η : Site d → ℝ =>
              (∑ i : Fin d, (u η k (x + unit i) + u η k (x - unit i))) / (2 * (d : ℝ)) := rfl
        rw [heq]
        exact (Finset.measurable_sum _ fun i _ =>
          (ih (x + unit i)).add (ih (x - unit i))).div_const _
      have hfun : (fun η : Site d → ℝ => u η (k + 1) x)
          = fun η : Site d → ℝ => max 0 (η x + walkOp (u η k) x) := rfl
      rw [hfun]
      exact measurable_const.max ((measurable_pi_apply x).add hwalk)

theorem integrable_uOf_rpow (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν)
    {r : ℝ} (hr : 1 ≤ r) (n : ℕ) (x : Site d) :
    Integrable (fun ω : Data d => |uOf ω n x| ^ r) (law d ν) := by
  have hr0 : (0 : ℝ) ≤ r := le_trans zero_le_one hr
  have hdom : Integrable (fun ω : Data d => (n : ℝ) ^ r * confBox ω x n ^ r) (law d ν) :=
    (integrable_confBox_rpow hd ν hθ hexp hr x n).const_mul _
  refine Integrable.mono' hdom
    (((measurable_uOf n x).abs.pow_const r).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  have h0 : 0 ≤ uOf ω n x := uOf_nonneg ω n x
  have hle : uOf ω n x ≤ (n : ℝ) * confBox ω x n := uOf_le_confBox hd ω n x
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) r),
    abs_of_nonneg h0]
  rw [← Real.mul_rpow (Nat.cast_nonneg n) (confBox_nonneg ω x n)]
  exact Real.rpow_le_rpow h0 hle hr0

end Parking

end
