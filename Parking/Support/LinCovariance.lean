/-
**The covariance of a finite linear combination of i.i.d. mean-zero coordinates.**

The orthogonality computation that turns the finite-sum representation of `V` in
`Parking.Support.LinPotentialSum` into a covariance: for `ξ : ι → ℝ` distributed as
`Measure.pi (fun _ => ν)` (a FINITE i.i.d. family with common law `ν`, mean zero, finite
second moment),

    E[(Σᵢ aᵢ ξᵢ)(Σⱼ bⱼ ξⱼ)] = (Σᵢ aᵢ bᵢ) · E[ξ₀²].

The proof uses three tools, all from Mathlib:
`MeasureTheory.measurePreserving_eval` (the marginal of `Measure.pi` at one coordinate is the
corresponding factor), `ProbabilityTheory.iIndepFun_iff_hasLaw_pi_pi` (the coordinate
projections of a finite `Measure.pi` are independent — taken at the trivial `HasLaw id`),
and `ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral` (independence gives the
expectation of a product is the product of expectations).  Combined with
`Parking.linPotential_eq_sum_of_boxFinset_subset`, this gives
`Cov(V_n(x), V_m(y)) = Var(η(0)) · Σ_{z ∈ S} g_n(x-z) g_m(y-z)` for any finite `S` containing
both boxes, over the COMMON index set `S`.  That combination, and the further reduction of
the finite sum to BP's closed form `Σ_{a<n}Σ_{b<m} P^{a+b}(x-y)` (via
`LatticeProb.tsum_srwGreen_mul_shift`), are carried out in `Parking.Support.LinCovarianceGlue`.
This module supplies only the finite orthogonality identity; it is stated for a general
finite i.i.d. family and mentions no object specific to the parking model.
-/
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section

open MeasureTheory ProbabilityTheory Finset

namespace Parking

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Each coordinate projection of a finite i.i.d. product has law `ν`.** -/
theorem hasLaw_eval_pi (ν : Measure ℝ) [IsProbabilityMeasure ν] (i : ι) :
    HasLaw (fun ξ : ι → ℝ => ξ i) ν (Measure.pi fun _ : ι => ν) :=
  ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval (μ := fun _ : ι => ν) i).map_eq⟩

omit [DecidableEq ι] in
/-- **The coordinate projections of a finite i.i.d. product are independent.** -/
theorem iIndepFun_eval_pi (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    iIndepFun (fun i : ι => fun ξ : ι → ℝ => ξ i) (Measure.pi fun _ : ι => ν) := by
  rw [iIndepFun_iff_hasLaw_pi_pi (fun i => hasLaw_eval_pi (ι := ι) ν i)]
  exact ⟨aemeasurable_id, Measure.map_id⟩

omit [DecidableEq ι] in
/-- **The pushforward of a finite i.i.d. product along one coordinate transports an
integral to the one-site law.** -/
theorem integral_eval_pi (ν : Measure ℝ) [IsProbabilityMeasure ν] (i : ι) (g : ℝ → ℝ)
    (hg : AEStronglyMeasurable g ν) :
    ∫ ξ : ι → ℝ, g (ξ i) ∂(Measure.pi fun _ : ι => ν) = ∫ x, g x ∂ν := by
  have hmp := measurePreserving_eval (μ := fun _ : ι => ν) i
  have hf : AEMeasurable (fun ξ : ι → ℝ => ξ i) (Measure.pi fun _ : ι => ν) :=
    (measurable_pi_apply i).aemeasurable
  have hg' : AEStronglyMeasurable g ((Measure.pi fun _ : ι => ν).map (fun ξ : ι → ℝ => ξ i)) := by
    rw [hmp.map_eq]; exact hg
  have hkey := integral_map hf hg'
  rw [hmp.map_eq] at hkey
  exact hkey.symm

omit [DecidableEq ι] in
/-- **The pushforward also transports integrability.** -/
theorem integrable_eval_pi (ν : Measure ℝ) [IsProbabilityMeasure ν] (i : ι) (g : ℝ → ℝ)
    (hg : Integrable g ν) :
    Integrable (fun ξ : ι → ℝ => g (ξ i)) (Measure.pi fun _ : ι => ν) := by
  have hmp := measurePreserving_eval (μ := fun _ : ι => ν) i
  have hg' : Integrable g ((Measure.pi fun _ : ι => ν).map (fun ξ : ι → ℝ => ξ i)) := by
    rw [hmp.map_eq]; exact hg
  exact (integrable_map_measure hg'.1 (measurable_pi_apply i).aemeasurable).mp hg'

/-- **The orthogonality identity.**  `E[(Σᵢ aᵢξᵢ)(Σⱼ bⱼξⱼ)] = (Σᵢ aᵢbᵢ)·E[ξ₀²]`, for a
finite i.i.d. family with mean zero and finite second moment. -/
theorem integral_sum_mul_sum_pi (a b : ι → ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ x, x ∂ν = 0) (hint : Integrable (fun x : ℝ => x) ν)
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν) :
    ∫ ξ : ι → ℝ, (∑ i, a i * ξ i) * (∑ j, b j * ξ j) ∂(Measure.pi fun _ : ι => ν)
      = (∑ i, a i * b i) * ∫ x, x ^ 2 ∂ν := by
  have hindep := iIndepFun_eval_pi (ι := ι) ν
  have hIntEval : ∀ i : ι, Integrable (fun ξ : ι → ℝ => ξ i) (Measure.pi fun _ : ι => ν) :=
    fun i => integrable_eval_pi ν i id hint
  have hcross : ∀ i j : ι, i ≠ j →
      ∫ ξ : ι → ℝ, ξ i * ξ j ∂(Measure.pi fun _ : ι => ν) = 0 := by
    intro i j hij
    have hI := hindep.indepFun hij
    have hkey := hI.integral_mul_eq_mul_integral (hIntEval i).aestronglyMeasurable
      (hIntEval j).aestronglyMeasurable
    simp only [Pi.mul_apply] at hkey
    have hEi : ∫ ξ : ι → ℝ, ξ i ∂(Measure.pi fun _ : ι => ν) = 0 := by
      have hz := integral_eval_pi (ι := ι) ν i id hint.1
      simpa using hz.trans hmean
    rw [hkey, hEi]
    ring
  have hdiag : ∀ i : ι,
      ∫ ξ : ι → ℝ, ξ i * ξ i ∂(Measure.pi fun _ : ι => ν) = ∫ x, x ^ 2 ∂ν := by
    intro i
    have heq : (fun ξ : ι → ℝ => ξ i * ξ i) = (fun ξ : ι → ℝ => (fun x => x ^ 2) (ξ i)) := by
      funext ξ; ring
    rw [heq, integral_eval_pi (ι := ι) ν i (fun x => x ^ 2) hsq.1]
  have hstep : (fun ξ : ι → ℝ => (∑ i, a i * ξ i) * (∑ j, b j * ξ j))
      = fun ξ => ∑ i, ∑ j, (a i * b j) * (ξ i * ξ j) := by
    funext ξ
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hstep]
  have hIntDiag : ∀ i : ι,
      Integrable (fun ξ : ι → ℝ => ξ i * ξ i) (Measure.pi fun _ : ι => ν) := by
    intro i
    have heq : (fun ξ : ι → ℝ => ξ i * ξ i) = (fun ξ : ι → ℝ => (fun x => x ^ 2) (ξ i)) := by
      funext ξ; ring
    rw [heq]
    exact integrable_eval_pi ν i (fun x => x ^ 2) hsq
  have hIntOff : ∀ i j : ι, i ≠ j →
      Integrable (fun ξ : ι → ℝ => ξ i * ξ j) (Measure.pi fun _ : ι => ν) :=
    fun i j hij => (hindep.indepFun hij).integrable_mul (hIntEval i) (hIntEval j)
  have hIntCross : ∀ i j : ι,
      Integrable (fun ξ : ι → ℝ => (a i * b j) * (ξ i * ξ j)) (Measure.pi fun _ : ι => ν) := by
    intro i j
    by_cases hij : i = j
    · subst hij; exact (hIntDiag i).const_mul _
    · exact (hIntOff i j hij).const_mul _
  have hsum1 : ∀ i : ι,
      ∫ ξ : ι → ℝ, (∑ j, (a i * b j) * (ξ i * ξ j)) ∂(Measure.pi fun _ : ι => ν)
        = ∑ j, ∫ ξ : ι → ℝ, (a i * b j) * (ξ i * ξ j) ∂(Measure.pi fun _ : ι => ν) :=
    fun i => integral_finsetSum Finset.univ (fun j _ => hIntCross i j)
  have hsum2 :
      ∫ ξ : ι → ℝ, (∑ i, ∑ j, (a i * b j) * (ξ i * ξ j)) ∂(Measure.pi fun _ : ι => ν)
        = ∑ i, ∫ ξ : ι → ℝ, (∑ j, (a i * b j) * (ξ i * ξ j)) ∂(Measure.pi fun _ : ι => ν) :=
    integral_finsetSum Finset.univ (fun i _ =>
      (integrable_finsetSum Finset.univ (fun j _ => hIntCross i j)))
  rw [hsum2]
  have hinner : ∀ i : ι,
      ∫ ξ : ι → ℝ, (∑ j, (a i * b j) * (ξ i * ξ j)) ∂(Measure.pi fun _ : ι => ν)
        = a i * b i * ∫ x, x ^ 2 ∂ν := by
    intro i
    rw [hsum1 i]
    have hterm : ∀ j : ι,
        ∫ ξ : ι → ℝ, (a i * b j) * (ξ i * ξ j) ∂(Measure.pi fun _ : ι => ν)
          = (a i * b j) * ∫ ξ : ι → ℝ, ξ i * ξ j ∂(Measure.pi fun _ : ι => ν) :=
      fun j => integral_const_mul _ _
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    rw [Finset.sum_eq_single i
      (fun j _ hji => by rw [hcross i j (Ne.symm hji)]; ring)
      (fun hcontra => absurd (Finset.mem_univ i) hcontra)]
    rw [hdiag i]
  rw [Finset.sum_congr rfl fun i _ => hinner i, ← Finset.sum_mul]

end Parking

end
