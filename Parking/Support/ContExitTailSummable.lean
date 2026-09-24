/-
**Summability of the exit-tail series.** This module derives the `hexitsummable` hypothesis of
`Parking.ae_tendsto_contCutoffValue_sub_contStoppingValue`
(`Parking/Support/ContStoppingCutoffTail.lean`) from the library's own Brownian exit-tail
estimate.

- `measureReal_contExitEvent_le`: extracts, as its own standalone fact, the pure Brownian
  exit-tail bound `PB'.real (contExitEvent B' A s) ≤ C·exp(-cA²/(s+1))` contained in
  `Parking.abs_spatialContValue_sub_contCutoffValue_le_exp`'s proof
  (`Parking/Support/ContSpatialCutoff.lean`), so it can be reused for a purely numerical
  summability argument instead of a comparison of stopping values.
- `summable_mul_measureReal_contExitEvent_of_poly`: given `M n` bounded by a POLYNOMIAL in `n`
  (the shape `M n = O(√(log n) + n^β)` produced by the Kolmogorov-Chentsov moment bound,
  read through a natural-number upper bound on its growth rate), `Summable (fun n => M n ·
  PB'.real (contExitEvent B' ((n:ℝ)+1) s))`, exactly the shape `hexitsummable` needs: since
  `(n+1)² ≥ n+1`, the Gaussian exit tail at radius `n+1` is already dominated by a SINGLE
  exponential `exp(-r(n+1))` for `r := c/(s+1)`, and a polynomial times a single exponential is
  summable (`Real.summable_pow_mul_exp_neg_nat_mul`, shifted by one index).
-/
import Parking.Support.ContSpatialCutoff

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Parking

variable {d : ℕ}

/-- **The pure Brownian exit-tail bound for `contExitEvent`**, extracted from the proof of
`Parking.abs_spatialContValue_sub_contCutoffValue_le_exp` so it can be reused on its own. -/
theorem measureReal_contExitEvent_le {ΩB' : Type*} [MeasurableSpace ΩB']
    (B' : ℝ≥0 → ΩB' → EuclideanSpace ℝ (Fin d)) (PB' : Measure ΩB') [IsProbabilityMeasure PB']
    (hB' : LatticeProb.IsBrownianSpace d 0 B' PB') (s : ℝ) (hs : 0 ≤ s) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ A : ℝ, 0 < A →
      PB'.real (contExitEvent B' A s) ≤ C * Real.exp (-(c * A ^ 2 / (s + 1))) := by
  obtain ⟨C, c, hC, hc, hbound⟩ := LatticeProb.brownian_exit_tail_closed d
  refine ⟨C, c, hC, hc, ?_⟩
  intro A hA
  have hexit := hbound 0 ΩB' PB' inferInstance B' hB' A hA (s + 1) (by linarith)
  have hsub : contExitEvent B' A s ⊆ {ω | ∃ t : ℝ≥0, (t : ℝ) < s + 1 ∧ A ≤ ‖B' t ω - 0‖} := by
    rintro β ⟨t, ht, hA'⟩
    exact ⟨t, by linarith, by simpa using hA'⟩
  calc PB'.real (contExitEvent B' A s)
      ≤ PB'.real {ω | ∃ t : ℝ≥0, (t : ℝ) < s + 1 ∧ A ≤ ‖B' t ω - 0‖} := measureReal_mono hsub
    _ ≤ C * Real.exp (-(c * A ^ 2 / (s + 1))) := by
        rw [measureReal_def]
        have := ENNReal.toReal_mono (by finiteness) hexit
        rwa [ENNReal.toReal_ofReal (by positivity)] at this

/-- **`hexitsummable` from a polynomial bound on `M`.** `(n+1)² ≥ n+1` lets the quadratic
Gaussian exit rate be dominated by a single linear exponential, to which
`Real.summable_pow_mul_exp_neg_nat_mul` applies directly. -/
theorem summable_mul_measureReal_contExitEvent_of_poly {ΩB' : Type*} [MeasurableSpace ΩB']
    (B' : ℝ≥0 → ΩB' → EuclideanSpace ℝ (Fin d)) (PB' : Measure ΩB') [IsProbabilityMeasure PB']
    (hB' : LatticeProb.IsBrownianSpace d 0 B' PB') (s : ℝ) (hs : 0 ≤ s)
    (M : ℕ → ℝ) (Cpoly : ℝ) (β : ℕ) (hCpoly : 0 ≤ Cpoly)
    (hM0 : ∀ n, 0 ≤ M n) (hMpoly : ∀ n, M n ≤ Cpoly * ((n : ℝ) + 1) ^ β) :
    Summable (fun n : ℕ => M n * PB'.real (contExitEvent B' ((n : ℝ) + 1) s)) := by
  obtain ⟨C, c, hC, hc, hbound⟩ := measureReal_contExitEvent_le B' PB' hB' s hs
  set r := c / (s + 1) with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hcomparepow : ∀ n : ℕ, M n * PB'.real (contExitEvent B' ((n : ℝ) + 1) s)
      ≤ Cpoly * C * ((n : ℝ) + 1) ^ β * Real.exp (-(r * ((n : ℝ) + 1))) := by
    intro n
    have hApos : (0:ℝ) < (n:ℝ) + 1 := by positivity
    have hb := hbound ((n:ℝ)+1) hApos
    have hstep1 : -(c * ((n:ℝ)+1) ^ 2 / (s+1)) ≤ -(r * ((n:ℝ)+1)) := by
      have hle : r * ((n:ℝ)+1) ≤ c * ((n:ℝ)+1) ^ 2 / (s+1) := by
        rw [hr, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
        nlinarith [sq_nonneg ((n:ℝ))]
      linarith
    have hexp_mono : Real.exp (-(c * ((n:ℝ)+1) ^ 2 / (s+1))) ≤ Real.exp (-(r * ((n:ℝ)+1))) :=
      Real.exp_le_exp.mpr hstep1
    calc M n * PB'.real (contExitEvent B' ((n:ℝ)+1) s)
        ≤ (Cpoly * ((n:ℝ)+1) ^ β) * (C * Real.exp (-(c * ((n:ℝ)+1) ^ 2 / (s+1)))) :=
          mul_le_mul (hMpoly n) hb (by positivity) (by positivity)
      _ ≤ (Cpoly * ((n:ℝ)+1) ^ β) * (C * Real.exp (-(r * ((n:ℝ)+1)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp_mono hC.le) (by positivity)
      _ = Cpoly * C * ((n:ℝ)+1) ^ β * Real.exp (-(r * ((n:ℝ)+1))) := by ring
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (hM0 n) measureReal_nonneg) hcomparepow
  have hshift : Summable (fun n : ℕ => ((n:ℝ)+1) ^ β * Real.exp (-(r * ((n:ℝ)+1)))) := by
    have h := Real.summable_pow_mul_exp_neg_nat_mul β hr0
    have heq : (fun n:ℕ => ((n:ℝ)+1)^β * Real.exp (-(r*((n:ℝ)+1))))
        = (fun n:ℕ => ((n+1 : ℕ):ℝ)^β * Real.exp (-r * ((n+1:ℕ):ℝ))) := by
      funext n; push_cast; ring_nf
    rw [heq]
    exact (summable_nat_add_iff (f := fun m:ℕ => (m:ℝ)^β * Real.exp (-r*(m:ℝ))) 1).mpr h
  simpa [mul_assoc] using hshift.mul_left (Cpoly * C)

end Parking
