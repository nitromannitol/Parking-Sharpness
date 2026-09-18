/- Moments of the coefficient bound along a directed time interval. -/
import Parking.Support.OrientedCountMoment

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset

theorem le_rpow_of_rpow_two_div_le {I B p : ℝ} (hI : 0 ≤ I) (hp : 0 < p)
    (h : I ^ (2 / p) ≤ B) : I ≤ B ^ (p / 2) := by
  have hb := Real.rpow_le_rpow (Real.rpow_nonneg hI _) h (by positivity : (0 : ℝ) ≤ p / 2)
  rw [← Real.rpow_mul hI, show (2 / p) * (p / 2) = (1 : ℝ) by field_simp,
    Real.rpow_one] at hb
  exact hb

theorem orientedFirstCount_congr {ω τ : ℕ → Fin 2 × Bool} (j h : ℕ)
    (he : ∀ i, i < j + h → ω i = τ i) : orientedFirstCount ω j h = orientedFirstCount τ j h := by
  apply sum_congr rfl
  intro i hi
  rw [he i (mem_Ico.mp hi).2]

theorem measurable_orientedFirstCount (j h : ℕ) :
    Measurable fun ω : ℕ → Fin 2 × Bool => orientedFirstCount ω j h := by
  unfold orientedFirstCount
  apply Finset.measurable_sum
  intro i _
  exact (measurable_from_countable' (fun b : Fin 2 × Bool => if b.1 = 0 then (1 : ℕ) else 0)).comp
    (measurable_pi_apply i)

/-- The random coefficient bound has the required moments, uniformly in the
location and length of the time interval. -/
theorem exists_orientedCount_load_moment (q : ℝ) (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ j h : ℕ,
      Integrable (fun ω : ℕ → Fin 2 × Bool =>
        (Real.sqrt h + |(orientedFirstCount ω j h : ℝ) - (h : ℝ) / 2|) ^ q) (walkLaw 2) ∧
      (∫ ω : ℕ → Fin 2 × Bool,
        (Real.sqrt h + |(orientedFirstCount ω j h : ℝ) - (h : ℝ) / 2|) ^ q ∂(walkLaw 2)) ≤
          C * (h : ℝ) ^ (q / 2) := by
  have hq0 : 0 < q := by linarith
  haveI := stepLaw_isProbability (d := 2) (by norm_num)
  haveI : IsProbabilityMeasure (walkLaw 2) := by unfold walkLaw; infer_instance
  obtain ⟨C, hC, hb⟩ := exists_orientedCount_moment q hq
  refine ⟨2 ^ q * (1 + C ^ (q / 2)), by positivity, fun j h => ?_⟩
  have hi : Integrable (fun ω : ℕ → Fin 2 × Bool =>
      (Real.sqrt h + |(orientedFirstCount ω j h : ℝ) - (h : ℝ) / 2|) ^ q) (walkLaw 2) := by
    apply integrable_of_finite_dependence (by norm_num) (j + h)
    intro ω τ he
    rw [orientedFirstCount_congr j h he]
  obtain ⟨hdi, hdb⟩ := hb j h
  have hdB := le_rpow_of_rpow_two_div_le
    (integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) q) hq0 hdb
  rw [Real.mul_rpow hC.le (Nat.cast_nonneg h)] at hdB
  have hdom := integral_mono hi (((integrable_const (Real.sqrt (h : ℝ) ^ q)).add hdi).const_mul (2 ^ q))
    (fun ω => rpow_add_le_two (by linarith) (Real.sqrt_nonneg (h : ℝ)) (abs_nonneg _))
  simp only [Pi.add_apply, integral_const_mul, integral_add (integrable_const _) hdi, integral_const,
    probReal_univ, smul_eq_mul, one_mul] at hdom
  have he : Real.sqrt (h : ℝ) ^ q = (h : ℝ) ^ (q / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg h)]
    congr 1
    ring
  rw [he] at hdom
  refine ⟨hi, hdom.trans ?_⟩
  have hm := mul_le_mul_of_nonneg_left hdB (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) q)
  nlinarith

end Parking
