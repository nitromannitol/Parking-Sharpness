import Parking.External.BinomialLocalCLT
import LatticeProb.Walk.BinomialLocalCLT

/-!
# The one-dimensional local CLT, proved

The one-dimensional local central limit theorem for the simple `±1` random
walk, discharged from the shared library's `LatticeProb.BinomialLCLT`
development (`LatticeProb/Walk/BinomialLocalCLT.lean`).

The library's `exists_binomPMF_localCLT` gives the `C/m` Gaussian
approximation for `binomPMF m j`, the walk's position pmf, restricted to
`|j| ≤ m` (outside that range the naive formula for `binomPMF` reads as a
junk value, per that file's own docstring).  Parking's `binomLaw` indexes
the *same* fair binomial pmf by the number of successes rather than the
position (`LatticeProb/Walk/BinomLaw.lean`); the two agree exactly on
`binomLaw m ((j+m)/2) = binomPMF m j` in the range `|j| ≤ m`, where the
index `(j+m)/2` is a nonnegative integer at most `m` and both formulas read
off the same binomial coefficient.  Outside that range `binomLaw` is
honestly zero (`binomLaw_of_neg`, `binomLaw_of_gt`), so the remaining case
is an elementary Gaussian tail estimate: `|j| > m` forces the exponent
`-(j/√m)²/2` below `-m/2`, and `m · exp(-m/2) ≤ 2` follows from
`Real.add_one_le_exp` at the point `m/2`, giving a uniform `C_tail/m` bound
there.
-/

open LatticeProb.BinomialLCLT

/-- The elementary Gaussian tail bound used outside the range `|j| ≤ m`, where
`binomLaw` (and hence the left-hand side of the local CLT) vanishes. -/
private theorem binomialLocalCLT_tail_bound (m : ℕ) (hm : 1 ≤ m) (j : ℤ)
    (hjlt : (m : ℤ) < |j|) :
    2 * (Real.exp (-((j : ℝ) / Real.sqrt (m : ℝ)) ^ 2 / 2) / Real.sqrt (2 * Real.pi))
      ≤ (4 / Real.sqrt (2 * Real.pi)) / (m : ℝ) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hjR : (m : ℝ) < |(j : ℝ)| := by exact_mod_cast hjlt
  have hj2 : (m : ℝ) ^ 2 < (j : ℝ) ^ 2 := by
    have h := (sq_lt_sq₀ hm0.le (abs_nonneg (j : ℝ))).mpr hjR
    rwa [sq_abs] at h
  have hxsq : (m : ℝ) < ((j : ℝ) / Real.sqrt (m : ℝ)) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hm0.le, lt_div_iff₀ hm0]
    nlinarith [hj2]
  have hexp_le : Real.exp (-((j : ℝ) / Real.sqrt (m : ℝ)) ^ 2 / 2)
      ≤ Real.exp (-(m : ℝ) / 2) :=
    (Real.exp_lt_exp.mpr (by linarith [hxsq])).le
  have hmexp : (m : ℝ) * Real.exp (-(m : ℝ) / 2) ≤ 2 := by
    have h1 : (m : ℝ) / 2 + 1 ≤ Real.exp ((m : ℝ) / 2) := Real.add_one_le_exp ((m : ℝ) / 2)
    have h3 : (m : ℝ) < 2 * Real.exp ((m : ℝ) / 2) := by linarith
    have h4 : (m : ℝ) * Real.exp (-(m : ℝ) / 2)
        ≤ (2 * Real.exp ((m : ℝ) / 2)) * Real.exp (-(m : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right h3.le (Real.exp_pos _).le
    have h5 : Real.exp ((m : ℝ) / 2) * Real.exp (-(m : ℝ) / 2) = 1 := by
      rw [← Real.exp_add, show (m : ℝ) / 2 + -(m : ℝ) / 2 = 0 by ring, Real.exp_zero]
    calc (m : ℝ) * Real.exp (-(m : ℝ) / 2)
        ≤ (2 * Real.exp ((m : ℝ) / 2)) * Real.exp (-(m : ℝ) / 2) := h4
      _ = 2 * (Real.exp ((m : ℝ) / 2) * Real.exp (-(m : ℝ) / 2)) := by ring
      _ = 2 := by rw [h5]; ring
  have hexp_le2 : Real.exp (-(m : ℝ) / 2) ≤ 2 / (m : ℝ) := by
    rw [le_div_iff₀ hm0]; linarith [hmexp]
  have hsqrtpos : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have step1 : Real.exp (-((j : ℝ) / Real.sqrt (m : ℝ)) ^ 2 / 2) / Real.sqrt (2 * Real.pi)
      ≤ Real.exp (-(m : ℝ) / 2) / Real.sqrt (2 * Real.pi) :=
    (div_le_div_iff_of_pos_right hsqrtpos).mpr hexp_le
  have step2 : Real.exp (-(m : ℝ) / 2) / Real.sqrt (2 * Real.pi)
      ≤ (2 / (m : ℝ)) / Real.sqrt (2 * Real.pi) :=
    (div_le_div_iff_of_pos_right hsqrtpos).mpr hexp_le2
  calc 2 * (Real.exp (-((j : ℝ) / Real.sqrt (m : ℝ)) ^ 2 / 2) / Real.sqrt (2 * Real.pi))
      ≤ 2 * (Real.exp (-(m : ℝ) / 2) / Real.sqrt (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left step1 (by norm_num)
    _ ≤ 2 * ((2 / (m : ℝ)) / Real.sqrt (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left step2 (by norm_num)
    _ = (4 / Real.sqrt (2 * Real.pi)) / (m : ℝ) := by ring

/-- `Parking.External.BinomialLocalCLT` in full: inside `|j| ≤ m` from the library's
`exists_binomPMF_localCLT` via the `binomLaw`/`binomPMF` index identification, and outside it
from `binomialLocalCLT_tail_bound`, with the combined constant `C0 + 4/√(2π)`. -/
private theorem binomialLocalCLT_proof : Parking.External.BinomialLocalCLT := by
  obtain ⟨C0, hC0pos, hC0⟩ := exists_binomPMF_localCLT
  have hCtailpos : (0 : ℝ) < 4 / Real.sqrt (2 * Real.pi) := by positivity
  refine ⟨C0 + 4 / Real.sqrt (2 * Real.pi), by linarith, ?_⟩
  intro m hm j hpar
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  by_cases hjle : |j| ≤ (m : ℤ)
  · have hparZ : j ≡ (m : ℤ) [ZMOD 2] := by
      unfold Int.ModEq
      omega
    have hjbound := abs_le.mp hjle
    have hnonneg : 0 ≤ ((m : ℤ) + j) / 2 := by omega
    have hidx : (j + (m : ℤ)) / 2 = ((m : ℤ) + j) / 2 := by rw [add_comm]
    have hbinomEq : Parking.binomLaw m ((j + (m : ℤ)) / 2) = binomPMF m j := by
      rw [hidx]
      unfold Parking.binomLaw binomPMF
      rw [if_pos hnonneg]
    have hgdEq : 2 * (Real.exp (-((j : ℝ) / Real.sqrt (m : ℝ)) ^ 2 / 2) / Real.sqrt (2 * Real.pi))
        = 2 * gaussianDensity ((j : ℝ) / Real.sqrt (m : ℝ)) := by
      unfold gaussianDensity
      ring
    rw [hbinomEq, hgdEq]
    have hkey := hC0 m hm j hparZ hjle
    have hle : C0 / (m : ℝ) ≤ (C0 + 4 / Real.sqrt (2 * Real.pi)) / (m : ℝ) :=
      (div_le_div_iff_of_pos_right hm0).mpr (by linarith [hCtailpos])
    linarith [hkey, hle]
  · rw [not_le] at hjle
    have hidx0 : Parking.binomLaw m ((j + (m : ℤ)) / 2) = 0 := by
      by_cases hj0 : 0 ≤ j
      · have habsj : |j| = j := abs_of_nonneg hj0
        rw [habsj] at hjle
        exact LatticeProb.Walk.binomLaw_of_gt m (by omega)
      · have hj0' : j < 0 := not_le.mp hj0
        have habsj : |j| = -j := abs_of_neg hj0'
        rw [habsj] at hjle
        exact LatticeProb.Walk.binomLaw_of_neg m (by omega)
    rw [hidx0]
    have htail := binomialLocalCLT_tail_bound m hm j hjle
    have hpos : (0 : ℝ)
        ≤ 2 * (Real.exp (-((j : ℝ) / Real.sqrt (m : ℝ)) ^ 2 / 2) / Real.sqrt (2 * Real.pi)) := by
      positivity
    rw [mul_zero, zero_sub, abs_neg, abs_of_nonneg hpos]
    have hle2 : (4 / Real.sqrt (2 * Real.pi)) / (m : ℝ)
        ≤ (C0 + 4 / Real.sqrt (2 * Real.pi)) / (m : ℝ) :=
      (div_le_div_iff_of_pos_right hm0).mpr (by linarith [hC0pos])
    linarith [htail, hle2]

-- FROZEN-STATEMENT-BEGIN
theorem Parking.External.binomialLocalCLT : Parking.External.BinomialLocalCLT
-- FROZEN-STATEMENT-END
:= by
  exact binomialLocalCLT_proof
