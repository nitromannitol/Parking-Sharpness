/- The activity asymptotic of the directed walk, and `thm:oriented-walk` reduced to the
scaling constant alone.

The last paragraph of Step 3 (`parking.tex:3324-3331`) derives `S⃗_t ∼ (μ/4)t^{-3/4}` from
`E U⃗_n(0) ∼ μ n^{1/4}` and the monotonicity of `S⃗`.  With the mass transport identity for
the directed law and the monotone density step, that derivation is carried out here, and
the activity asymptotic ceases to be an input of the theorem: what is left of
`thm:oriented-walk` is the constant `μ` of `prop:oriented-scaling` and nothing else.
-/
import Parking.Support.OrientedWalkReduced
import Parking.Support.OrientedTransport
import Parking.Support.MonotoneDensity

noncomputable section
namespace Parking
open MeasureTheory Filter Topology

/-- **The activity asymptotic of the directed walk from the asymptotic of the mean.** -/
theorem tendsto_S_oriented (ν : Measure ℤ) (hν : CriticalLaw ν) (μ : ℝ) (hμ : 0 < μ)
    (hmean : Tendsto (fun n : ℕ => meanU (orientedLaw 2 ν) n / (n : ℝ) ^ ((1:ℝ)/4))
      atTop (𝓝 μ)) :
    Tendsto (fun t : ℕ => S (orientedLaw 2 ν) t / (μ / 4 * (t : ℝ) ^ (-(3:ℝ)/4)))
      atTop (𝓝 1) := by
  have hact := tendsto_activity_of_mean (S (orientedLaw 2 ν))
    (S_antitone_oriented (by norm_num) ν hν) (meanU (orientedLaw 2 ν))
    (meanU_eq_sum_S_oriented (by norm_num) ν hν) μ hmean
  have hne : (μ / 4) ≠ 0 := ne_of_gt (by linarith)
  have hdiv := hact.div_const (μ / 4)
  rw [div_self hne] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  have ht0 : (0:ℝ) < t := by exact_mod_cast ht
  have hpos : (0:ℝ) < (t : ℝ) ^ ((3:ℝ)/4) := Real.rpow_pos_of_pos ht0 _
  have h1 : (t : ℝ) ^ (-(3:ℝ)/4) = ((t : ℝ) ^ ((3:ℝ)/4))⁻¹ := by
    rw [← Real.rpow_neg ht0.le]
    norm_num
  rw [h1]
  field_simp

/-- **`thm:oriented-walk` from the scaling constant of the divisible mean alone.** -/
theorem oriented_walk_of_mean (hBern : Parking.External.Bernstein)
    (hConc : Parking.External.UConcentration)
    (d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (μ : ℝ) (hμ : 0 < μ)
    (hμlim : Tendsto (fun n : ℕ => meanuOriented (orientedLaw 2 ν) n /
      ((n : ℝ) ^ ((1 : ℝ) / 4))) atTop (𝓝 μ)) :
    (d = 2 → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ meanU (orientedLaw d ν) n ∧
        meanU (orientedLaw d ν) n ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4)) ∧
    (3 ≤ d → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * Real.log n ≤ meanU (orientedLaw d ν) n ∧
        meanU (orientedLaw d ν) n ≤ C * Real.log n) ∧
    (d = 2 →
      Tendsto (fun n : ℕ => meanU (orientedLaw d ν) n /
        meanuOriented (orientedLaw d ν) n) atTop (𝓝 1) ∧
      ∃ μ' : ℝ, 0 < μ' ∧
        Tendsto (fun n : ℕ => meanU (orientedLaw d ν) n /
          (μ' * (n : ℝ) ^ ((1 : ℝ) / 4))) atTop (𝓝 1) ∧
        Tendsto (fun t : ℕ => S (orientedLaw d ν) t /
          (μ' / 4 * (t : ℝ) ^ (-(3 : ℝ) / 4))) atTop (𝓝 1)) := by
  haveI := hν.prob
  obtain ⟨Cc, hCc, herr⟩ := exists_oriented_herr hBern hConc ν hν
  obtain ⟨c₂, hc₂, hlo⟩ :=
    exists_meanuOriented_two_lower ν hν.nonconst hν.integrable_abs hν.mean
  have hratio := tendsto_meanU_div_meanuOriented ν hν c₂ Cc hc₂ (fun n _ => hlo n) herr
  have hmean : Tendsto (fun n : ℕ => meanU (orientedLaw 2 ν) n / (n : ℝ) ^ ((1:ℝ)/4))
      atTop (𝓝 μ) := by
    have hprod := hratio.mul hμlim
    rw [one_mul] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0:ℝ) < (n : ℝ) ^ ((1:ℝ)/4) :=
      Real.rpow_pos_of_pos (by exact_mod_cast hn) _
    have hden : meanuOriented (orientedLaw 2 ν) n ≠ 0 := by
      have hpos : 0 < c₂ * (n : ℝ) ^ ((1 : ℝ) / 4) := by positivity
      exact ne_of_gt (lt_of_lt_of_le hpos (hlo n))
    field_simp
  exact oriented_walk_of_scaling hBern hConc d hd ν hν μ hμ hμlim
    (tendsto_S_oriented ν hν μ hμ hmean)

end Parking
end
