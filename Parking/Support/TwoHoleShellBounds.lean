import Parking.Support.OrthantCube
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
namespace Parking
open Filter Topology
variable {d : ℕ}

/-- The fixed inner cutoff makes the exponent of the two-hole bound small. -/
theorem exists_twoHole_inner_cutoff (hd : 5 ≤ d) (C : ℝ) :
    ∃ L : ℕ, C * (1 + (L : ℝ)) ^ (4 - (d : ℝ)) ≤ 1 / 4 := by
  have he : 0 < (d : ℝ) - 4 := by
    have hd' : (5 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have ht : Tendsto (fun L : ℕ => (1 : ℝ) + L) atTop atTop := tendsto_atTop_add_const_left atTop 1 tendsto_natCast_atTop_atTop
  have hp : Tendsto (fun L : ℕ => C * (1 + (L : ℝ)) ^ (-((d : ℝ) - 4))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using ((tendsto_rpow_neg_atTop he).comp ht).const_mul C
  have hq : ∀ᶠ L : ℕ in atTop, C * (1 + (L : ℝ)) ^ (4 - (d : ℝ)) ≤ 1 / 4 := by
    have h := hp.eventually (eventually_le_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
    simpa only [neg_sub, mul_zero] using h
  exact hq.exists

theorem twoHole_coefficient_antitone (hd : 5 ≤ d) {L n : ℕ} (hLn : L ≤ n) :
    (1 + (n : ℝ)) ^ (4 - (d : ℝ)) ≤ (1 + (L : ℝ)) ^ (4 - (d : ℝ)) := by
  apply Real.rpow_le_rpow_of_nonpos (by positivity)
  · exact_mod_cast Nat.add_le_add_left hLn 1
  · have hd' : (5 : ℝ) ≤ d := by exact_mod_cast hd
    linarith

/-- The intermediate-distance bound has exponent seven quarters in the hole density. -/
theorem twoHole_middle_bound {C h q : ℝ} (hC : 0 ≤ C) (hh : 0 < h) (hh1 : h ≤ 1)
    (hq : C * q ≤ 1 / 4) :
    C * h ^ 2 * Real.exp (C * Real.log (1 / h) * q) ≤ C * h ^ (7 / 4 : ℝ) := by
  have hL : 0 ≤ Real.log (1 / h) := Real.log_nonneg (by apply (le_div_iff₀ hh).mpr; simpa using hh1)
  have hexp : C * Real.log (1 / h) * q ≤ Real.log (1 / h) / 4 := by
    have hm := mul_le_mul_of_nonneg_right hq hL
    nlinarith
  have hi : h ^ 2 * Real.exp (Real.log (1 / h) / 4) = h ^ (7 / 4 : ℝ) := by
    rw [Real.rpow_def_of_pos hh]
    have hp : h ^ 2 = Real.exp (2 * Real.log h) := by
      simpa only [Nat.cast_ofNat, Real.exp_log hh] using (Real.exp_nat_mul (Real.log h) 2).symm
    rw [hp, ← Real.exp_add, Real.log_div (by norm_num) hh.ne', Real.log_one]
    congr 1
    ring
  calc C * h ^ 2 * Real.exp (C * Real.log (1 / h) * q)
    ≤ C * h ^ 2 * Real.exp (Real.log (1 / h) / 4) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (mul_nonneg hC (sq_nonneg h))
    _ = C * h ^ (7 / 4 : ℝ) := by rw [mul_assoc, hi]

end Parking
