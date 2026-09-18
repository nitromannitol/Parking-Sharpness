/- The discrete walk operator has the continuum Laplacian as its second-order limit. -/
import Parking.Generic.SymmetricTaylor
import Parking.Support.Continuum

noncomputable section

namespace Parking

open LatticeProb
open Parking.Generic.SymmetricTaylor

theorem exists_walkOp_taylor_bound {d : ℕ} (hd : 1 ≤ d)
    {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∀ y : Site d,
      |walkOp (fun z => φ (fun i => (z i : ℝ) / R)) y - φ (fun i => (y i : ℝ) / R)
        - contOp d φ (fun i => (y i : ℝ) / R) / R ^ 2| ≤ C / R ^ 3 := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_uniform_coordinate_taylor_bound hφ.1 hφ.2
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  refine ⟨C / 2, by positivity, fun R hR y => ?_⟩
  let x : Fin d → ℝ := fun j => (y j : ℝ) / R
  have hplus : ∀ i : Fin d, (fun j => ((y + unit i) j : ℝ) / R) =
      Function.update x i (x i + 1 / R) := by
    intro i
    funext j
    by_cases hji : j = i
    · subst j
      simp [x, unit, add_div]
    · simp [x, unit, hji]
  have hminus : ∀ i : Fin d, (fun j => ((y - unit i) j : ℝ) / R) =
      Function.update x i (x i - 1 / R) := by
    intro i
    funext j
    by_cases hji : j = i
    · subst j
      simp [x, unit, sub_div]
    · simp [x, unit, hji]
  let D : Fin d → ℝ := fun i => deriv (deriv (fun t => φ (Function.update x i t))) (x i)
  let e : Fin d → ℝ := fun i =>
    φ (Function.update x i (x i + 1 / R)) + φ (Function.update x i (x i - 1 / R))
      - 2 * φ x - (1 / R) ^ 2 * D i
  have he : ∀ i, |e i| ≤ C / R ^ 3 := by
    intro i
    have hi := hbound i x (1 / R)
    simpa [e, D, abs_of_pos hR, div_pow, div_eq_mul_inv] using hi
  have heq : walkOp (fun z => φ (fun i => (z i : ℝ) / R)) y - φ x
      - contOp d φ x / R ^ 2 = (∑ i, e i) / (2 * d) := by
    unfold walkOp nbrSum contOp lap
    simp_rw [hplus, hminus]
    simp only [e, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    dsimp [D]
    rw [← Finset.mul_sum]
    field_simp
    simp only [mul_comm, mul_assoc]
  change |walkOp (fun z => φ (fun i => (z i : ℝ) / R)) y - φ x - contOp d φ x / R ^ 2|
      ≤ C / 2 / R ^ 3
  rw [heq, abs_div, abs_of_pos (mul_pos (by norm_num) hdpos)]
  have hsum : |∑ i, e i| ≤ (d : ℝ) * (C / R ^ 3) := by
    calc |∑ i, e i| ≤ ∑ i, |e i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, C / R ^ 3 := Finset.sum_le_sum fun i _ => he i
      _ = (d : ℝ) * (C / R ^ 3) := by simp
  calc |∑ i, e i| / (2 * d) ≤ ((d : ℝ) * (C / R ^ 3)) / (2 * d) :=
      div_le_div_of_nonneg_right hsum (by positivity)
    _ = C / 2 / R ^ 3 := by field_simp

end Parking
