/-
Cramer-Wold: convergence in law of a finite-dimensional random vector from convergence of the
scalar characteristic function of every fixed linear combination of its coordinates.  Needed
for the finite-dimensional convergence clause of `prop:spatial-scaling`: the extended
continuous mapping theorem's hypothesis `X_n → X` in law in `C(K)` factors, by tightness plus
this theorem, through the scalar characteristic-function convergence of every finite linear
combination of point evaluations of the rescaled field.

This is a general fact about finite-dimensional vectors indexed by `Fin m`, independent of the
parking model and of the spatial dimension `d`: its statement mentions no object of this paper's
model, and `m` is an arbitrary number of evaluation points.  It reduces `TendstoInDistribution`
of a `Fin m → ℝ`-valued family to the scalar characteristic-function convergence hypothesis, via
Mathlib's Levy continuity theorem (`MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_charFun`)
on the auxiliary Euclidean space `EuclideanSpace ℝ (Fin m)`, transported to the plain product
type `Fin m → ℝ` by the continuous mapping theorem
(`MeasureTheory.TendstoInDistribution.continuous_comp`) along the continuous linear equivalence
`EuclideanSpace.equiv`.
-/
import Mathlib

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

noncomputable section
namespace Parking.Generic.CramerWold

/-- **Cramer-Wold.** If the scalar characteristic function of every fixed linear combination
`∑ₖ t k · X i · k` converges (at argument `1`) to that of the corresponding combination of a
limit vector `Z`, then `X` converges to `Z` in distribution as `Fin m → ℝ`-valued random
vectors. -/
theorem tendstoInDistribution_of_tendsto_charFun_linearCombination
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)] {Ω' : Type*} [MeasurableSpace Ω']
    {P : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)]
    {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {m : ℕ} {X : (i : ℕ) → Ω i → Fin m → ℝ} {Z : Ω' → Fin m → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hZm : Measurable Z)
    (hcomb : ∀ t : Fin m → ℝ,
      Tendsto (fun i => charFun ((P i).map (fun ω => ∑ k, t k * X i ω k)) 1) atTop
        (𝓝 (charFun (Q.map (fun ω => ∑ k, t k * Z ω k)) 1))) :
    TendstoInDistribution X atTop Z P Q := by
  set e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] Fin m → ℝ := EuclideanSpace.equiv (Fin m) ℝ with hedef
  set Xe : (i : ℕ) → Ω i → EuclideanSpace ℝ (Fin m) := fun i ω => e.symm (X i ω) with hXedef
  set Ze : Ω' → EuclideanSpace ℝ (Fin m) := fun ω => e.symm (Z ω) with hZedef
  have hXem : ∀ i, Measurable (Xe i) := fun i => e.symm.continuous.measurable.comp (hXm i)
  have hZem : Measurable Ze := e.symm.continuous.measurable.comp hZm
  have hinner : ∀ (v : Fin m → ℝ) (s : EuclideanSpace ℝ (Fin m)),
      (inner ℝ (e.symm v) s : ℝ) = ∑ k, (e s) k * v k := by
    intro v s
    have hs : s = e.symm (e s) := (e.symm_apply_apply s).symm
    calc (inner ℝ (e.symm v) s : ℝ) = (inner ℝ (e.symm v) (e.symm (e s)) : ℝ) := by rw [← hs]
      _ = ∑ k, (e s) k * v k := rfl
  have hone : ∀ x : ℝ, (inner ℝ x (1 : ℝ) : ℝ) = x := by
    intro x; rw [RCLike.inner_apply]; simp
  have hsumXm : ∀ (i : ℕ) (s : EuclideanSpace ℝ (Fin m)),
      Measurable (fun ω => ∑ k, (e s) k * X i ω k) :=
    fun i s => Finset.measurable_sum Finset.univ
      fun k _ => measurable_const.mul ((measurable_pi_apply k).comp (hXm i))
  have hsumZm : ∀ s : EuclideanSpace ℝ (Fin m), Measurable (fun ω => ∑ k, (e s) k * Z ω k) :=
    fun s => Finset.measurable_sum Finset.univ
      fun k _ => measurable_const.mul ((measurable_pi_apply k).comp hZm)
  have hcharEq : ∀ (i : ℕ) (s : EuclideanSpace ℝ (Fin m)),
      charFun ((P i).map (Xe i)) s = charFun ((P i).map (fun ω => ∑ k, (e s) k * X i ω k)) 1 := by
    intro i s
    rw [charFun_apply, charFun_apply]
    have hL : (∫ x : EuclideanSpace ℝ (Fin m), Complex.exp (((inner ℝ x s : ℝ) : ℂ) *
          Complex.I) ∂(P i).map (Xe i))
        = ∫ ω, Complex.exp (((inner ℝ (Xe i ω) s : ℝ) : ℂ) * Complex.I) ∂(P i) :=
      integral_map (hXem i).aemeasurable (by fun_prop)
    have hR : (∫ x : ℝ, Complex.exp (((inner ℝ x (1 : ℝ) : ℝ) : ℂ) * Complex.I)
          ∂(P i).map (fun ω => ∑ k, (e s) k * X i ω k))
        = ∫ ω, Complex.exp (((inner ℝ (∑ k, (e s) k * X i ω k : ℝ) (1 : ℝ) : ℝ) : ℂ) * Complex.I)
          ∂(P i) :=
      integral_map (hsumXm i s).aemeasurable (by fun_prop)
    rw [hL, hR]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have h1 : (inner ℝ (Xe i ω) s : ℝ) = ∑ k, (e s) k * X i ω k := by
      rw [hXedef]; exact hinner (X i ω) s
    have h2 : (inner ℝ (∑ k, (e s) k * X i ω k : ℝ) (1 : ℝ) : ℝ) = ∑ k, (e s) k * X i ω k :=
      hone _
    show Complex.exp (((inner ℝ (Xe i ω) s : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((inner ℝ (∑ k, (e s) k * X i ω k : ℝ) (1 : ℝ) : ℝ) : ℂ) * Complex.I)
    rw [h1, h2]
  have hcharZEq : ∀ s : EuclideanSpace ℝ (Fin m),
      charFun (Q.map Ze) s = charFun (Q.map (fun ω => ∑ k, (e s) k * Z ω k)) 1 := by
    intro s
    rw [charFun_apply, charFun_apply]
    have hL : (∫ x : EuclideanSpace ℝ (Fin m), Complex.exp (((inner ℝ x s : ℝ) : ℂ) *
          Complex.I) ∂Q.map Ze)
        = ∫ ω, Complex.exp (((inner ℝ (Ze ω) s : ℝ) : ℂ) * Complex.I) ∂Q :=
      integral_map hZem.aemeasurable (by fun_prop)
    have hR : (∫ x : ℝ, Complex.exp (((inner ℝ x (1 : ℝ) : ℝ) : ℂ) * Complex.I)
          ∂Q.map (fun ω => ∑ k, (e s) k * Z ω k))
        = ∫ ω, Complex.exp (((inner ℝ (∑ k, (e s) k * Z ω k : ℝ) (1 : ℝ) : ℝ) : ℂ) * Complex.I)
          ∂Q :=
      integral_map (hsumZm s).aemeasurable (by fun_prop)
    rw [hL, hR]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have h1 : (inner ℝ (Ze ω) s : ℝ) = ∑ k, (e s) k * Z ω k := by
      rw [hZedef]; exact hinner (Z ω) s
    have h2 : (inner ℝ (∑ k, (e s) k * Z ω k : ℝ) (1 : ℝ) : ℝ) = ∑ k, (e s) k * Z ω k := hone _
    show Complex.exp (((inner ℝ (Ze ω) s : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((inner ℝ (∑ k, (e s) k * Z ω k : ℝ) (1 : ℝ) : ℝ) : ℂ) * Complex.I)
    rw [h1, h2]
  have hchar : ∀ s : EuclideanSpace ℝ (Fin m),
      Tendsto (fun i => charFun ((P i).map (Xe i)) s) atTop (𝓝 (charFun (Q.map Ze) s)) := by
    intro s
    refine Tendsto.congr' (Filter.Eventually.of_forall fun i => (hcharEq i s).symm) ?_
    rw [hcharZEq s]
    exact hcomb (e s)
  have hTID : TendstoInDistribution Xe atTop Ze P Q :=
    ⟨fun i => (hXem i).aemeasurable, hZem.aemeasurable,
      ProbabilityMeasure.tendsto_of_tendsto_charFun hchar⟩
  have hcont : Continuous (e : EuclideanSpace ℝ (Fin m) → Fin m → ℝ) := e.continuous
  have hcomp := hTID.continuous_comp hcont
  refine hcomp.congr ?_ ?_
  · intro i
    refine Filter.Eventually.of_forall fun ω => ?_
    show e (e.symm (X i ω)) = X i ω
    exact e.apply_symm_apply (X i ω)
  · refine Filter.Eventually.of_forall fun ω => ?_
    show e (e.symm (Z ω)) = Z ω
    exact e.apply_symm_apply (Z ω)

end Parking.Generic.CramerWold
end
