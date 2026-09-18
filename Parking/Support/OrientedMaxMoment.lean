/- The directed walk maximum has the one-quarter moment growth. -/
import Parking.Support.FinitePathMoment
import Parking.Support.OrientedPathMax

noncomputable section
namespace Parking
open LatticeProb MeasureTheory Finset

theorem exists_orientedMax_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (r : ℝ) (hr : 4 < r) (hmom : Integrable (fun z : ℝ => |z| ^ r) μ)
    (hmean : ∫ z : ℝ, z ∂μ = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      Integrable (fun ω : (ℕ → Fin 2 × Bool) × (Site 2 → ℝ) =>
        |orientedMax (orientedPotential ω.2) n 0 ω.1| ^ r) ((walkLaw 2).prod (iidLaw 2 μ)) ∧
      rNorm ((walkLaw 2).prod (iidLaw 2 μ)) r
        (fun ω => orientedMax (orientedPotential ω.2) n 0 ω.1) ≤
          C * (n : ℝ) ^ ((1 : ℝ) / 4) := by
  have hr0 : 0 < r := by linarith
  obtain ⟨A, hA, hinc⟩ := exists_oriented_potential_increment μ r hr hmom hmean
  have ha : 1 / r < (1 : ℝ) / 4 := by
    apply (div_lt_iff₀ hr0).mpr
    linarith
  obtain ⟨K, hK, hmax⟩ := exists_finitePathMax_moment ((walkLaw 2).prod (iidLaw 2 μ))
    (by linarith : 1 ≤ r) ((1 : ℝ) / 4) ha
  refine ⟨K * A, mul_pos hK hA, fun n hn => ?_⟩
  let F : ℕ → ((ℕ → Fin 2 × Bool) × (Site 2 → ℝ)) → ℝ :=
    fun j => orientedPotentialAlong n (n - j)
  have hm : ∀ j, Measurable (F j) := fun j => measurable_orientedPotentialAlong n (n - j)
  have hz (ω : (ℕ → Fin 2 × Bool) × (Site 2 → ℝ)) : F 0 ω = 0 := by
    simp only [F, orientedPotentialAlong, Nat.sub_zero, Nat.sub_self, orientedPotential_zero]
  have hFi : ∀ j k : ℕ, j ≤ k → k ≤ n →
      Integrable (fun ω => |F k ω - F j ω| ^ r) ((walkLaw 2).prod (iidLaw 2 μ)) ∧
      rNorm ((walkLaw 2).prod (iidLaw 2 μ)) r (fun ω => F k ω - F j ω) ≤
        A * ((k - j : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := by
    intro j k hjk hkn
    obtain ⟨hi, hb⟩ := hinc n (n - k) (n - j) (by omega) (by omega)
    have he : n - j - (n - k) = k - j := by omega
    rw [he] at hb
    exact ⟨hi, hb⟩
  obtain ⟨hi, hb⟩ := hmax n hn F hm hz A hA.le hFi
  have he (ω : (ℕ → Fin 2 × Bool) × (Site 2 → ℝ)) :
      finitePathMax (fun j => F j ω) n = orientedMax (orientedPotential ω.2) n 0 ω.1 := by
    apply le_antisymm
    · apply finitePathMax_le
      intro j hj
      exact (orientedMax_le_iff (orientedPotential ω.2) n 0 ω.1 _).mp le_rfl (n - j) (by omega)
    · apply (orientedMax_le_iff (orientedPotential ω.2) n 0 ω.1 _).mpr
      intro j hj
      have hb := abs_le_finitePathMax (fun j => F j ω) n (n - j) (by omega)
      simpa only [F, show n - (n - j) = j by omega, orientedPotentialAlong] using hb
  simpa only [he] using And.intro hi hb

end Parking
