/-
The end of Step 3 of `lem:critical-density` (`parking.tex:1329-1338`): the
choice of `ε`.

The paper's coupling produces, for every `t` and every `0 ≤ ε ≤ γ`, the
quadratic bound

    4 S_t ≥ ε - t ε² ,

and then reads the survivor bound off it: "For `t ≥ 1/(2γ)`, take `ε = 1/(2t)`.
Then `ε - t ε² = 1/(4t)`, so `S_t ≥ 1/(16t)`."  The constraint `ε ≤ γ` is
exactly `t ≥ 1/(2γ)`, which is why the threshold is where it is.

Chaining that with `critical_density_of_survivor_bound` reduces
`lem:critical-density` to the quadratic bound alone.
-/
import Parking.Support.CriticalReduction

noncomputable section

namespace Parking

open MeasureTheory Filter Topology LatticeProb

variable {d : ℕ}

/-- **The optimisation `ε = 1/(2t)`.**  A quadratic lower bound valid for every
`ε` in `[0, γ]` gives `1/(16t)` as soon as `1/(2γ) ≤ t`. -/
theorem quad_opt {γ s t : ℝ} (hγ : 0 < γ) (ht : 1 / (2 * γ) ≤ t)
    (h : ∀ ε : ℝ, 0 ≤ ε → ε ≤ γ → ε - t * ε ^ 2 ≤ 4 * s) :
    1 / (16 * t) ≤ s := by
  have ht0 : 0 < t := by linarith [show (0:ℝ) < 1 / (2 * γ) by positivity]
  have hgt : 1 / (2 * t) ≤ γ := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * t)]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * γ)] at ht
    nlinarith
  have hkey := h (1 / (2 * t)) (by positivity) hgt
  have hval : 1 / (2 * t) - t * (1 / (2 * t)) ^ 2 = 1 / (4 * t) := by
    field_simp
    ring
  rw [hval] at hkey
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 16 * t)]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * t)] at hkey
  linarith

/-- **`lem:critical-density` from the quadratic bound of the coupling.**  What
Steps 1 and 2 of the paper have to deliver is the family of inequalities
`4 S_t ≥ ε - t ε²`, one for each `ε` in `[0, γ]`; everything after that is this
file and `CriticalReduction.lean`. -/
theorem critical_density_of_quadratic (hd : 1 ≤ d) (ν : Measure ℤ)
    (hprob : IsProbabilityMeasure ν) (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    {γ : ℝ} (hγ : 0 < γ)
    (hquad : ∀ t : ℕ, ∀ ε : ℝ, 0 ≤ ε → ε ≤ γ →
      ε - (t : ℝ) * ε ^ 2 ≤ 4 * S (law d ν) t) :
    (∀ᶠ t : ℕ in atTop, (1 / 16 : ℝ) ≤ (t : ℝ) * S (law d ν) t) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        (1 / 16 : ℝ) * Real.log n - C ≤ meanU (law d ν) n := by
  set T : ℕ := max 1 ⌈1 / (2 * γ)⌉₊ with hTdef
  have hT : 1 ≤ T := le_max_left _ _
  have hthr : ∀ t : ℕ, T ≤ t → 1 / (2 * γ) ≤ (t : ℝ) := by
    intro t ht
    have h1 : ⌈1 / (2 * γ)⌉₊ ≤ t := le_trans (le_max_right _ _) ht
    have h2 : (1 : ℝ) / (2 * γ) ≤ (⌈1 / (2 * γ)⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : ((⌈1 / (2 * γ)⌉₊ : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast h1
    linarith
  have hS : ∀ t : ℕ, T ≤ t → (1 : ℝ) / (16 * (t : ℝ)) ≤ S (law d ν) t := fun t ht =>
    quad_opt hγ (hthr t ht) (hquad t)
  obtain ⟨h1, h2⟩ := critical_density_of_survivor_bound hd ν hprob hint hT hS
  exact ⟨Filter.eventually_atTop.2 ⟨T, h1⟩, h2⟩

end Parking

end
