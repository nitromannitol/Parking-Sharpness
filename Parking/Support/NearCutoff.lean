/-
The cutoff `eq:near-cutoff` in the scale `env` (`parking.tex:2918-2929`).

"Let `L = log(e/δ)`.  Take `N = ⌈C δ^{-4}L^3⌉` in dimension one,
`⌈C δ^{-2}L^3⌉` in dimension two and `⌈C δ^{-2}L^2⌉` from dimension three on."

The cutoff of `Parking/Support/NearTail.lean` is the first integer past the threshold
of `prop:resolvent` at the exponent `a₀δ²`.  That threshold carries `(a₀δ²)^{-2}` or
`(a₀δ²)^{-1}` and a power of `log(e/(a₀δ²))`, and `log(e/(a₀δ²)) = 2L - 1 - log a₀` is
at most a constant multiple of `L`, so the threshold is at most a constant multiple of
`δ^{-4}L^3`, `δ^{-2}L^3` and `δ^{-2}L^2` in the three cases, exactly the rates of
`eq:near-cutoff`.
-/
import Parking.Support.NearEnv
import Parking.Support.NearTail

noncomputable section
namespace Parking
variable {d : ℕ}

/-- The scale of the cutoff `eq:near-cutoff`. -/
def cutoffEnv (d : ℕ) (δ : ℝ) : ℝ :=
  if d = 1 then env 4 3 δ else if d = 2 then env 2 3 δ else env 2 2 δ

theorem one_le_cutoffEnv (d : ℕ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ cutoffEnv d δ := by
  rw [cutoffEnv]
  split_ifs
  · exact one_le_env hδ0 hδ1 (by norm_num)
  · exact one_le_env hδ0 hδ1 (by norm_num)
  · exact one_le_env hδ0 hδ1 (by norm_num)

theorem inv_scaled {a₀ δ : ℝ} (hδ0 : 0 < δ) :
    (a₀ * δ ^ 2)⁻¹ = a₀⁻¹ * δ ^ (-(2 : ℝ)) := by
  rw [mul_inv, Real.rpow_neg hδ0.le, ← Real.rpow_natCast δ 2]
  norm_num

theorem rpow_scaled {a₀ δ : ℝ} (ha₀ : 0 < a₀) (hδ0 : 0 < δ) :
    (a₀ * δ ^ 2) ^ (-(2 : ℝ)) = a₀ ^ (-(2 : ℝ)) * δ ^ (-(4 : ℝ)) := by
  rw [Real.mul_rpow ha₀.le (sq_nonneg δ), ← Real.rpow_natCast δ 2, ← Real.rpow_mul hδ0.le]
  norm_num

/-- The threshold of `prop:resolvent` at the exponent `a₀ δ²` is at most a constant times
the cutoff scale of `eq:near-cutoff`. -/
theorem exists_resolventThreshold_le (d : ℕ) {CR a₀ : ℝ} (hCR : 0 < CR) (ha₀ : 0 < a₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → a₀ * δ ^ 2 ≤ 1 →
      Parking.resolventThreshold d CR (a₀ * δ ^ 2) ≤ C * cutoffEnv d δ := by
  obtain ⟨CL, hCL, hCLle⟩ := exists_log_scaled_le ha₀
  have key : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → a₀ * δ ^ 2 ≤ 1 →
      Real.log (Real.exp 1 / (a₀ * δ ^ 2)) ^ 3
          ≤ CL ^ 3 * Real.log (Real.exp 1 / δ) ^ 3 ∧
      Real.log (Real.exp 1 / (a₀ * δ ^ 2)) ^ 2
          ≤ CL ^ 2 * Real.log (Real.exp 1 / δ) ^ 2 := by
    intro δ hδ0 hδ1 ha1
    have ha0' : 0 < a₀ * δ ^ 2 := by positivity
    have hΛ1 : 1 ≤ Real.log (Real.exp 1 / (a₀ * δ ^ 2)) := one_le_bigL ha0' ha1
    have hΛle := hCLle δ hδ0 hδ1
    refine ⟨?_, ?_⟩
    · calc Real.log (Real.exp 1 / (a₀ * δ ^ 2)) ^ 3
          ≤ (CL * Real.log (Real.exp 1 / δ)) ^ 3 :=
            pow_le_pow_left₀ (by linarith) hΛle 3
        _ = CL ^ 3 * Real.log (Real.exp 1 / δ) ^ 3 := by ring
    · calc Real.log (Real.exp 1 / (a₀ * δ ^ 2)) ^ 2
          ≤ (CL * Real.log (Real.exp 1 / δ)) ^ 2 :=
            pow_le_pow_left₀ (by linarith) hΛle 2
        _ = CL ^ 2 * Real.log (Real.exp 1 / δ) ^ 2 := by ring
  by_cases h1 : d = 1
  · refine ⟨CR * a₀ ^ (-(2 : ℝ)) * CL ^ 3, by positivity, fun δ hδ0 hδ1 ha1 => ?_⟩
    rw [Parking.resolventThreshold, cutoffEnv, if_pos h1, if_pos h1, rpow_scaled ha₀ hδ0, env]
    have hpos : (0 : ℝ) ≤ CR * a₀ ^ (-(2 : ℝ)) * δ ^ (-(4 : ℝ)) := by positivity
    calc CR * (a₀ ^ (-(2 : ℝ)) * δ ^ (-(4 : ℝ))
            * Real.log (Real.exp 1 / (a₀ * δ ^ 2)) ^ 3)
        = (CR * a₀ ^ (-(2 : ℝ)) * δ ^ (-(4 : ℝ)))
            * Real.log (Real.exp 1 / (a₀ * δ ^ 2)) ^ 3 := by ring
      _ ≤ (CR * a₀ ^ (-(2 : ℝ)) * δ ^ (-(4 : ℝ)))
            * (CL ^ 3 * Real.log (Real.exp 1 / δ) ^ 3) :=
          mul_le_mul_of_nonneg_left (key δ hδ0 hδ1 ha1).1 hpos
      _ = CR * a₀ ^ (-(2 : ℝ)) * CL ^ 3
            * (δ ^ (-(4 : ℝ)) * Real.log (Real.exp 1 / δ) ^ 3) := by ring
  by_cases h2 : d = 2
  · refine ⟨CR * a₀⁻¹ * CL ^ 3, by positivity, fun δ hδ0 hδ1 ha1 => ?_⟩
    rw [Parking.resolventThreshold, cutoffEnv, if_neg h1, if_neg h1, if_pos h2, if_pos h2,
      inv_scaled hδ0, env]
    have hpos : (0 : ℝ) ≤ CR * a₀⁻¹ * δ ^ (-(2 : ℝ)) := by positivity
    calc CR * (a₀⁻¹ * δ ^ (-(2 : ℝ)) * Real.log (Real.exp 1 / (a₀ * δ ^ 2)) ^ 3)
        = (CR * a₀⁻¹ * δ ^ (-(2 : ℝ)))
            * Real.log (Real.exp 1 / (a₀ * δ ^ 2)) ^ 3 := by ring
      _ ≤ (CR * a₀⁻¹ * δ ^ (-(2 : ℝ))) * (CL ^ 3 * Real.log (Real.exp 1 / δ) ^ 3) :=
          mul_le_mul_of_nonneg_left (key δ hδ0 hδ1 ha1).1 hpos
      _ = CR * a₀⁻¹ * CL ^ 3 * (δ ^ (-(2 : ℝ)) * Real.log (Real.exp 1 / δ) ^ 3) := by ring
  · refine ⟨CR * a₀⁻¹ * CL ^ 2, by positivity, fun δ hδ0 hδ1 ha1 => ?_⟩
    rw [Parking.resolventThreshold, cutoffEnv, if_neg h1, if_neg h1, if_neg h2, if_neg h2,
      inv_scaled hδ0, env]
    have hpos : (0 : ℝ) ≤ CR * a₀⁻¹ * δ ^ (-(2 : ℝ)) := by positivity
    calc CR * (a₀⁻¹ * δ ^ (-(2 : ℝ)) * Real.log (Real.exp 1 / (a₀ * δ ^ 2)) ^ 2)
        = (CR * a₀⁻¹ * δ ^ (-(2 : ℝ)))
            * Real.log (Real.exp 1 / (a₀ * δ ^ 2)) ^ 2 := by ring
      _ ≤ (CR * a₀⁻¹ * δ ^ (-(2 : ℝ))) * (CL ^ 2 * Real.log (Real.exp 1 / δ) ^ 2) :=
          mul_le_mul_of_nonneg_left (key δ hδ0 hδ1 ha1).2 hpos
      _ = CR * a₀⁻¹ * CL ^ 2 * (δ ^ (-(2 : ℝ)) * Real.log (Real.exp 1 / δ) ^ 2) := by ring

theorem resolventThreshold_nonneg (d : ℕ) {CR a : ℝ} (hCR : 0 ≤ CR) (ha : 0 < a)
    (ha1 : a ≤ 1) : 0 ≤ Parking.resolventThreshold d CR a := by
  have hΛ : 1 ≤ Real.log (Real.exp 1 / a) := one_le_bigL ha ha1
  have hΛ0 : (0 : ℝ) ≤ Real.log (Real.exp 1 / a) := by linarith
  have hr : (0 : ℝ) < a ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos ha _
  have hi : (0 : ℝ) < a⁻¹ := inv_pos.mpr ha
  rw [Parking.resolventThreshold]
  split_ifs
  · exact mul_nonneg hCR (mul_nonneg hr.le (pow_nonneg hΛ0 3))
  · exact mul_nonneg hCR (mul_nonneg hi.le (pow_nonneg hΛ0 3))
  · exact mul_nonneg hCR (mul_nonneg hi.le (pow_nonneg hΛ0 2))

/-- **The cutoff `eq:near-cutoff` in the scale `env`.** -/
theorem exists_nearCutoff_le (d : ℕ) {CR a₀ : ℝ} (hCR : 0 < CR) (ha₀ : 0 < a₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → a₀ * δ ^ 2 ≤ 1 →
      ((nearCutoff d CR a₀ δ : ℕ) : ℝ) ≤ C * cutoffEnv d δ := by
  obtain ⟨C, hC, hCle⟩ := exists_resolventThreshold_le d hCR ha₀
  refine ⟨C + 2, by linarith, fun δ hδ0 hδ1 ha1 => ?_⟩
  have ha0' : 0 < a₀ * δ ^ 2 := by positivity
  have hT0 : 0 ≤ Parking.resolventThreshold d CR (a₀ * δ ^ 2) :=
    resolventThreshold_nonneg d hCR.le ha0' ha1
  have h1 := nearCutoff_le d CR a₀ δ hT0
  have h2 := hCle δ hδ0 hδ1 ha1
  have h3 : (1 : ℝ) ≤ cutoffEnv d δ := one_le_cutoffEnv d hδ0 hδ1
  linarith

end Parking
end
