import Parking.Support.LinearExponential
import Parking.Support.LinearMoment

/-!
# Exponential moments on finite coordinate sets of an infinite product

Lifts the finite-product exponential-moment bound of `Parking.Support.LinearExponential` to
the infinite product `Measure.infinitePi`, for a linear combination supported on a finite
coordinate set `S`, and then combines the bound with its mirror image to bound the exponential
moment of the absolute value of the combination.
-/

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset

/-- Lifts `linear_exponential_pi`'s bound on a finite product to the infinite product
`Measure.infinitePi`, for a linear combination supported on the finite set `S`, by reindexing
through the coordinate-reading map `read : (ι → ℝ) → Fin S.card → ℝ` and the measure-preserving
`hread`. -/
theorem linear_exponential_infinitePi {ι : Type*} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {τ D : ℝ} (hτ : 0 ≤ τ)
    (hb : ∀ t : ℝ, |t| ≤ τ →
      Integrable (fun z : ℝ => Real.exp (t * z)) μ ∧
      (∫ z : ℝ, Real.exp (t * z) ∂μ) ≤ Real.exp (D * t ^ 2))
    (S : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ S, |a i| ≤ 1) :
    Integrable (fun ξ : ι → ℝ => Real.exp (τ * ∑ i ∈ S, a i * ξ i))
        (Measure.infinitePi fun _ : ι => μ) ∧
      (∫ ξ : ι → ℝ, Real.exp (τ * ∑ i ∈ S, a i * ξ i)
        ∂(Measure.infinitePi fun _ : ι => μ)) ≤ Real.exp (D * τ ^ 2 * ∑ i ∈ S, a i ^ 2) := by
  classical
  let e := S.equivFin.symm
  let v : Fin S.card → ι := fun i => (e i).val
  have hv : Function.Injective v := fun i j h => e.injective (Subtype.ext h)
  let read : (ι → ℝ) → Fin S.card → ℝ := fun ξ i => ξ (v i)
  have hread : MeasurePreserving read (Measure.infinitePi fun _ : ι => μ)
      (Measure.pi fun _ : Fin S.card => μ) :=
    ⟨measurable_pi_lambda _ (fun i => measurable_pi_apply (v i)), infinitePi_map_comp μ v hv⟩
  have he : ∀ f : ι → ℝ, (∑ i : Fin S.card, f (v i)) = ∑ j ∈ S, f j := by
    intro f
    exact (e.sum_comp (fun j : S => f j.val)).trans (Finset.sum_coe_sort S f)
  obtain ⟨hI, hB⟩ := linear_exponential_pi μ hτ hb S.card (fun i => a (v i))
    (fun i => ha (v i) (e i).property)
  let F : (Fin S.card → ℝ) → ℝ := fun ξ => Real.exp (τ * ∑ i, a (v i) * ξ i)
  have hF : Measurable F := by dsimp only [F]; fun_prop
  have hcomp (ξ : ι → ℝ) : F (read ξ) = Real.exp (τ * ∑ j ∈ S, a j * ξ j) := by
    dsimp only [F, read]
    rw [he (fun j => a j * ξ j)]
  have hi := integrable_comp_mp hread F hF.aestronglyMeasurable hI
  have heq := integral_comp_mp hread F hF.aestronglyMeasurable
  change (∫ ξ, F ξ ∂(Measure.pi fun _ : Fin S.card => μ)) ≤
    Real.exp (D * τ ^ 2 * ∑ i : Fin S.card, a (v i) ^ 2) at hB
  rw [heq, he (fun i => a i ^ 2)] at hB
  simpa only [hcomp] using And.intro hi hB

/-- `exp(τ * |x|) ≤ exp(τ * x) + exp(τ * (-x))`, by splitting on the sign of `x` and dropping
the other, positive, exponential term. -/
theorem exp_abs_le_exp_add (τ x : ℝ) :
    Real.exp (τ * |x|) ≤ Real.exp (τ * x) + Real.exp (τ * (-x)) := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    linarith [Real.exp_pos (τ * (-x))]
  · rw [abs_of_neg (lt_of_not_ge hx)]
    linarith [Real.exp_pos (τ * x)]

/-- From a one-site exponential tail bound (`exists_oneSite_exponential_bound`), produces a
rate `τ > 0` and constant `B > 0` such that every finitely-supported, `|a i| ≤ 1`-bounded
linear combination has `exp(τ * |∑ a i * ξ i|)` integrable with mean at most
`2 * exp(B * ∑ a i ^ 2)`, by applying `linear_exponential_infinitePi` to `a` and to `-a` and
combining the two bounds via `exp_abs_le_exp_add`. -/
theorem exists_linear_abs_exponential {ι : Type*} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (id : ℝ → ℝ) μ) (hm : ∫ z : ℝ, z ∂μ = 0)
    {θ : ℝ} (hθ : 0 < θ) (he : Integrable (fun z : ℝ => Real.exp (θ * |z|)) μ) :
    ∃ τ B : ℝ, 0 < τ ∧ 0 < B ∧ ∀ (S : Finset ι) (a : ι → ℝ),
      (∀ i ∈ S, |a i| ≤ 1) →
      Integrable (fun ξ : ι → ℝ => Real.exp (τ * |∑ i ∈ S, a i * ξ i|))
          (Measure.infinitePi fun _ : ι => μ) ∧
        (∫ ξ : ι → ℝ, Real.exp (τ * |∑ i ∈ S, a i * ξ i|)
          ∂(Measure.infinitePi fun _ : ι => μ)) ≤ 2 * Real.exp (B * ∑ i ∈ S, a i ^ 2) := by
  classical
  obtain ⟨τ, D, hτ, hD, hb⟩ := exists_oneSite_exponential_bound μ hi hm hθ he
  refine ⟨τ, D * τ ^ 2, hτ, by positivity, fun S a ha => ?_⟩
  obtain ⟨hIp, hBp⟩ := linear_exponential_infinitePi μ hτ.le hb S a ha
  obtain ⟨hIn, hBn⟩ := linear_exponential_infinitePi μ hτ.le hb S (fun i => -a i)
    (fun i hi => by simpa only [abs_neg] using ha i hi)
  simp only [neg_mul, sum_neg_distrib, neg_sq] at hIn hBn
  have hIa : Integrable (fun ξ : ι → ℝ => Real.exp (τ * |∑ i ∈ S, a i * ξ i|))
      (Measure.infinitePi fun _ : ι => μ) := by
    refine (hIp.add hIn).mono'
      ((show Measurable (fun ξ : ι → ℝ => Real.exp (τ * |∑ i ∈ S, a i * ξ i|)) by
        fun_prop).aestronglyMeasurable) (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact exp_abs_le_exp_add τ _
  have hraw := integral_mono hIa (hIp.add hIn)
    (fun ξ : ι → ℝ => exp_abs_le_exp_add τ (∑ i ∈ S, a i * ξ i))
  simp only [Pi.add_apply, integral_add hIp hIn] at hraw
  exact ⟨hIa, by nlinarith⟩

end Parking
