/- Linear potential and the divisible recursion for the directed kernel. -/
import Parking.Support.OrientedLayer

noncomputable section
namespace Parking
open LatticeProb Finset
variable {d : ℕ}

theorem orientedOp_mono {f g : Site d → ℝ} (h : ∀ x, f x ≤ g x) (x : Site d) :
    orientedOp f x ≤ orientedOp g x :=
  div_le_div_of_nonneg_right (sum_le_sum fun _ _ => h _) (Nat.cast_nonneg _)

theorem orientedOp_const (hd : 1 ≤ d) (c : ℝ) (x : Site d) :
    orientedOp (fun _ => c) x = c := by
  simp only [orientedOp, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ c (ne_of_gt (show (0 : ℝ) < d by exact_mod_cast hd))

theorem orientedOp_add (f g : Site d → ℝ) (x : Site d) :
    orientedOp (f + g) x = orientedOp f x + orientedOp g x := by
  simp [orientedOp, sum_add_distrib, add_div]

theorem orientedOp_sub (f g : Site d → ℝ) (x : Site d) :
    orientedOp (f - g) x = orientedOp f x - orientedOp g x := by
  simp [orientedOp, sum_sub_distrib, sub_div]

theorem orientedOp_sum {ι : Type*} (S : Finset ι) (f : ι → Site d → ℝ) (x : Site d) :
    orientedOp (fun y => ∑ i ∈ S, f i y) x = ∑ i ∈ S, orientedOp (f i) x := by
  simp only [orientedOp, ← sum_div]
  rw [sum_comm]

/-- The scenery averaged against a directed layer. -/
def orientedLayerAverage (η : Site d → ℝ) (n : ℕ) (x : Site d) : ℝ :=
  ∑' z : Site d, orientedLayer d n z * η (x + z)

/-- The truncated linear potential. -/
def orientedPotential (η : Site d → ℝ) (n : ℕ) (x : Site d) : ℝ :=
  ∑ l ∈ range n, orientedLayerAverage η l x

theorem summable_orientedLayerAverage (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    Summable fun z => orientedLayer d n z * η (x + z) := by
  exact (summable_orientedLayer_weight n (fun z => η (x + z))).congr fun z => mul_comm _ _

theorem orientedLayerAverage_zero (η : Site d → ℝ) (x : Site d) :
    orientedLayerAverage η 0 x = η x := by
  simp only [orientedLayerAverage, orientedLayer]
  simp

theorem orientedLayerAverage_succ (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    orientedLayerAverage η (n + 1) x = orientedOp (orientedLayerAverage η n) x := by
  have he : ∀ (i : Fin d) (z : Site d),
      orientedLayer d n (z + unit i) * η (x + z) =
        (fun w => orientedLayer d n w * η (x - unit i + w)) (z + unit i) := by
    intro i z
    congr 2
    abel
  have hs : ∀ i : Fin d, Summable fun z => orientedLayer d n (z + unit i) * η (x + z) := by
    intro i
    have h := ((Equiv.addRight (unit i)).summable_iff
      (f := fun w : Site d => orientedLayer d n w * η (x - unit i + w))).mpr
      (summable_orientedLayerAverage η n (x - unit i))
    exact h.congr fun z => (he i z).symm
  have ht : ∀ i : Fin d, (∑' z, orientedLayer d n (z + unit i) * η (x + z)) =
      orientedLayerAverage η n (x - unit i) := by
    intro i
    rw [tsum_congr (he i)]
    exact (Equiv.addRight (unit i)).tsum_eq
      (fun w : Site d => orientedLayer d n w * η (x - unit i + w))
  have hsplit : ∀ z : Site d, orientedLayer d (n + 1) z * η (x + z) =
      (∑ i : Fin d, orientedLayer d n (z + unit i) * η (x + z)) / d := by
    intro z
    rw [orientedLayer_succ, ← sum_mul]
    ring
  rw [orientedLayerAverage, tsum_congr hsplit, tsum_div_const,
    Summable.tsum_finsetSum (fun i _ => hs i)]
  simp only [ht, orientedOp]

theorem orientedPotential_zero (η : Site d → ℝ) (x : Site d) : orientedPotential η 0 x = 0 := by
  simp [orientedPotential]

theorem orientedPotential_succ (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    orientedPotential η (n + 1) x = η x + orientedOp (orientedPotential η n) x := by
  rw [orientedPotential, sum_range_succ']
  change (∑ l ∈ range n, orientedLayerAverage η (l + 1) x) + orientedLayerAverage η 0 x = _
  simp only [orientedLayerAverage_succ, orientedLayerAverage_zero]
  rw [← orientedOp_sum]
  exact add_comm _ _

theorem orientedPotential_eq_green (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    orientedPotential η n x = ∑' z : Site d, orientedGreen d n z * η (x + z) := by
  simp only [orientedGreen, sum_mul]
  rw [Summable.tsum_finsetSum (fun l _ => summable_orientedLayerAverage η l x)]
  rfl

theorem uOriented_nonneg (η : Site d → ℝ) (n : ℕ) (x : Site d) : 0 ≤ uOriented η n x := by
  cases n with
  | zero => rfl
  | succ n => exact le_max_left _ _

theorem uOriented_mono_time (η : Site d → ℝ) (x : Site d) : Monotone fun n => uOriented η n x := by
  apply monotone_nat_of_le_succ
  intro n
  induction n generalizing x with
  | zero => exact uOriented_nonneg η 1 x
  | succ n ih =>
    change max 0 (η x + orientedOp (uOriented η n) x) ≤
      max 0 (η x + orientedOp (uOriented η (n + 1)) x)
    exact max_le_max le_rfl (add_le_add le_rfl (orientedOp_mono ih x))

theorem orientedPotential_le_u (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    orientedPotential η n x ≤ uOriented η n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [orientedPotential_succ]
    exact (add_le_add le_rfl (orientedOp_mono ih x)).trans (le_max_right _ _)

theorem max_orientedPotential_le_u (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    max 0 (orientedPotential η n x) ≤ uOriented η n x :=
  max_le (uOriented_nonneg η n x) (orientedPotential_le_u η n x)

theorem uOriented_sub_potential_succ (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    uOriented η (n + 1) x - orientedPotential η (n + 1) x =
      max (-orientedPotential η (n + 1) x)
        (orientedOp (uOriented η n - orientedPotential η n) x) := by
  simp only [uOriented]
  rw [← max_sub_sub_right, zero_sub, orientedOp_sub, orientedPotential_succ]
  congr 1
  ring

end Parking
