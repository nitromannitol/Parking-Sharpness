/- A logarithmic mean bound for the directed potential maximum. -/
import Parking.Support.OrientedPotentialExponential
import Parking.Support.OrientedPathMax
import Parking.Support.FiniteExponentialMax
import Parking.Support.ExponentialMean

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

theorem exists_orientedMax_log_mean (hd : 3 ≤ d)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (id : ℝ → ℝ) μ) (hm : ∫ z : ℝ, z ∂μ = 0)
    {θ : ℝ} (hθ : 0 < θ) (he : Integrable (fun z : ℝ => Real.exp (θ * |z|)) μ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      Integrable (fun ω : (ℕ → Fin d × Bool) × (Site d → ℝ) =>
        orientedMax (orientedPotential ω.2) n 0 ω.1) ((walkLaw d).prod (iidLaw d μ)) ∧
      (∫ ω : (ℕ → Fin d × Bool) × (Site d → ℝ),
        orientedMax (orientedPotential ω.2) n 0 ω.1 ∂((walkLaw d).prod (iidLaw d μ))) ≤
          C * Real.log ((n : ℝ) + 1) := by
  haveI := stepLaw_isProbability (d := d) (by omega)
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  haveI : IsProbabilityMeasure (iidLaw d μ) := by unfold iidLaw; infer_instance
  obtain ⟨τ, A, hτ, hA, hb⟩ := exists_orientedPotential_exponential hd μ hi hm hθ he
  refine ⟨(A + 2) / τ, by positivity, fun n hn => ?_⟩
  let Q := (walkLaw d).prod (iidLaw d μ)
  let F : ℕ → ((ℕ → Fin d × Bool) × (Site d → ℝ)) → ℝ := orientedPotentialAlong n
  let M : ((ℕ → Fin d × Bool) × (Site d → ℝ)) → ℝ :=
    fun ω => orientedMax (orientedPotential ω.2) n 0 ω.1
  have hM (ω : (ℕ → Fin d × Bool) × (Site d → ℝ)) :
      finitePathMax (fun j => F j ω) n = M ω :=
    (orientedMax_eq_sup (orientedPotential ω.2) n 0 ω.1).symm
  have hcoord (j : ℕ) :
      Integrable (fun ω => Real.exp (τ * |F j ω|)) Q ∧
      (∫ ω, Real.exp (τ * |F j ω|) ∂Q) ≤ 2 * Real.exp (A * Real.log ((n : ℝ) + 1)) := by
    have hsec (p : ℕ → Fin d × Bool) := hb n hn (n - j) (Nat.sub_le _ _) (orientedPath 0 p j)
    have h := integral_prod_le_of_sections (walkLaw d) (iidLaw d μ)
      (fun ω => Real.exp (τ * |F j ω|))
      (((measurable_orientedPotentialAlong n j).abs.const_mul τ).exp)
      (fun ω => (Real.exp_pos _).le) (fun p => (hsec p).1)
      (fun _ => 2 * Real.exp (A * Real.log ((n : ℝ) + 1))) (integrable_const _) (fun p => (hsec p).2)
    simpa only [integral_const, probReal_univ, one_smul] using h
  obtain ⟨hEi, hEb⟩ := finitePathMax_exponential Q F
    (fun j => measurable_orientedPotentialAlong n j) n τ
    (2 * Real.exp (A * Real.log ((n : ℝ) + 1)))
    (fun j _ => (hcoord j).1) (fun j _ => (hcoord j).2)
  simp only [hM] at hEi hEb
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlog : Real.log 2 ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by norm_num) (by linarith)
  have hExp : ((n : ℝ) + 1) * (2 * Real.exp (A * Real.log ((n : ℝ) + 1))) ≤
      Real.exp ((A + 2) * Real.log ((n : ℝ) + 1)) := by
    calc ((n : ℝ) + 1) * (2 * Real.exp (A * Real.log ((n : ℝ) + 1))) =
        Real.exp (Real.log ((n : ℝ) + 1) + Real.log 2 + A * Real.log ((n : ℝ) + 1)) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_log hn0, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  obtain ⟨hMi, hMb⟩ := mean_le_of_exp_integral_le Q M (measurable_orientedPotentialMax n)
    (fun ω => orientedMax_nonneg _ _ _ _) hτ hEi (hEb.trans hExp)
  refine ⟨hMi, ?_⟩
  calc (∫ ω, M ω ∂Q) ≤ ((A + 2) * Real.log ((n : ℝ) + 1)) / τ :=
      (le_div_iff₀ hτ).mpr (by simpa only [mul_comm] using hMb)
    _ = _ := by ring

end Parking
