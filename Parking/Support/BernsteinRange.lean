/- Bernstein's bounded-increment inequality indexed from zero. -/
import Parking.External.Bernstein
import Parking.Support.BlockSum

noncomputable section
namespace Parking
open MeasureTheory Finset

theorem exists_bernstein_range_bound (hBern : External.Bernstein) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (_ : IsProbabilityMeasure μ) (k : ℕ) (F : ℕ → MeasurableSpace Ω)
      (ξ v : ℕ → Ω → ℝ) (r a : ℝ),
      Monotone F → (∀ i, F i ≤ ‹MeasurableSpace Ω›) →
      (∀ i, Measurable[F (i + 1)] (ξ i)) → (∀ i, Integrable (ξ i) μ) →
      (∀ i, i < k → μ[ξ i | F i] =ᵐ[μ] 0) →
      (∀ i, i < k → μ[fun ω => ξ i ω ^ 2 | F i] =ᵐ[μ] v i) →
      2 ≤ r → 0 < a → (∀ i, i < k → ∀ ω, |ξ i ω| ≤ a) →
      (∫ ω, |∑ i ∈ range k, ξ i ω| ^ r ∂μ) ^ (1 / r) ≤
        C * (Real.sqrt r * (∫ ω, (∑ i ∈ range k, v i ω) ^ (r / 2) ∂μ) ^ (1 / r) + r * a) := by
  obtain ⟨C, hC, hb⟩ := hBern
  refine ⟨C, hC, fun Ω _ μ _ k F ξ v r a hmono hle hm hi hc hv hr ha hbd => ?_⟩
  let ζ : ℕ → Ω → ℝ := fun i => if i = 0 then fun _ => 0 else ξ (i - 1)
  have hz (i : ℕ) : ζ (i + 1) = ξ i := by simp [ζ]
  have hzm (i : ℕ) : Measurable[F i] (ζ i) := by
    cases i with
    | zero => exact measurable_const
    | succ i => rw [hz]; exact hm i
  have hzi (i : ℕ) : Integrable (ζ i) μ := by
    cases i with
    | zero => exact integrable_zero _ _ _
    | succ i => rw [hz]; exact hi i
  have hzc (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ k) : μ[ζ i | F (i - 1)] =ᵐ[μ] 0 := by
    cases i with
    | zero => omega
    | succ i => simp only [hz, Nat.add_sub_cancel]; exact hc i (by omega)
  have hzb (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ k) (ω : Ω) : |ζ i ω| ≤ a := by
    cases i with
    | zero => omega
    | succ i => rw [hz]; exact hbd i (by omega) ω
  have h := (hb Ω inferInstance μ inferInstance k F ζ r a hmono hle hzm hzi hzc hr ha).1 hzb
  have hs (ω : Ω) : (∑ i ∈ Icc 1 k, ζ i ω) = ∑ i ∈ range k, ξ i ω := by
    rw [sum_Icc_one_eq_range_succ]
    simp only [hz]
  simp only [hs] at h
  have hvall : ∀ᵐ ω ∂μ, ∀ i, i < k → (μ[fun z => ξ i z ^ 2 | F i]) ω = v i ω :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun hik => hv i hik
  have he : (fun ω => (∑ i ∈ Icc 1 k, (μ[fun z => ζ i z ^ 2 | F (i - 1)]) ω) ^ (r / 2)) =ᵐ[μ]
      fun ω => (∑ i ∈ range k, v i ω) ^ (r / 2) := by
    filter_upwards [hvall] with ω hω
    congr 1
    rw [sum_Icc_one_eq_range_succ]
    simp only [hz, Nat.add_sub_cancel]
    exact sum_congr rfl fun i hik => hω i (mem_range.mp hik)
  rwa [integral_congr_ae he] at h

end Parking
