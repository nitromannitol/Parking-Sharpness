/-
`hWalk`: the finite-dimensional convergence in law of the rescaled oriented walk to a quarter-
Brownian motion (`parking.tex:3175-3196`), the second of the three ingredients
`Parking.tendsto_integral_orientedCutoffValue` consumes.

The route is Cramer-Wold (`Parking.tendstoInDistribution_of_tendsto_charFun_linearCombination`,
`TightCramerWold.lean`): it reduces `TendstoInDistribution` of the rescaled walk vectors to
scalar characteristic-function convergence of every fixed linear combination
`∑ₖ tₖ · (rescaled walk at time tsₖ)`.  The discrete side of that scalar statement is read off
`Parking.tendsto_charFun_walkFddLaw` (`TightWalk.lean`) through the general identity
`Parking.charFun_map_linearCombination_eq` (the scalar characteristic function of a linear
combination is the vector characteristic function at the same point, via the inner product on
`EuclideanSpace`); the continuum side is `Parking.charFun_quarterBrownian_linearCombination`
(`TightQuarterBrownian.lean`).  The two limits agree termwise (`Real.coe_toNNReal`,
`NNReal.coe_min`), so Cramer-Wold gives `TendstoInDistribution`, and Portmanteau
(`ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`) unwinds it into the bounded-
continuous-function-tested form `hWalk` is stated in.
-/
import Parking.Support.TightWalk
import Parking.Support.TightQuarterBrownian
import Parking.Support.TightCramerWold
import Mathlib.MeasureTheory.Measure.Portmanteau

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

noncomputable section

namespace Parking

/-- **The scalar characteristic function of a linear combination is the vector characteristic
function at the same point.** General, independent of the parking model. -/
theorem charFun_map_linearCombination_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {m : ℕ} (X : Ω → Fin m → ℝ) (hXm : Measurable X) (t : Fin m → ℝ) :
    charFun (μ.map (fun ω => ∑ k, t k * X ω k)) (1 : ℝ)
      = charFun (μ.map (fun ω => (WithLp.toLp 2 (X ω) : EuclideanSpace ℝ (Fin m))))
          (WithLp.toLp 2 t : EuclideanSpace ℝ (Fin m)) := by
  have hf1 : Measurable (fun ω => ∑ k, t k * X ω k) :=
    Finset.measurable_sum Finset.univ fun k _ => measurable_const.mul ((measurable_pi_apply k).comp hXm)
  have hf2 : Measurable (fun ω => (WithLp.toLp 2 (X ω) : EuclideanSpace ℝ (Fin m))) :=
    (PiLp.continuous_toLp 2 _).measurable.comp hXm
  rw [charFun_apply, charFun_apply,
    integral_map hf1.aemeasurable (by fun_prop),
    integral_map hf2.aemeasurable (by fun_prop)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have h1 : (⟪(∑ k, t k * X ω k : ℝ), (1 : ℝ)⟫ : ℝ) = ∑ k, t k * X ω k := by
    rw [RCLike.inner_apply]; simp
  have h2 : (⟪(WithLp.toLp 2 (X ω) : EuclideanSpace ℝ (Fin m)),
      (WithLp.toLp 2 t : EuclideanSpace ℝ (Fin m))⟫ : ℝ) = ∑ k, t k * X ω k := by
    rw [PiLp.inner_apply]
    have hterm : ∀ k : Fin m,
        (⟪(WithLp.toLp 2 (X ω) : EuclideanSpace ℝ (Fin m)) k,
          (WithLp.toLp 2 t : EuclideanSpace ℝ (Fin m)) k⟫ : ℝ) = t k * X ω k := by
      intro k
      show (⟪X ω k, t k⟫ : ℝ) = t k * X ω k
      rw [RCLike.inner_apply]
      simp only [starRingEnd_apply, star_trivial, mul_comm]
    simp_rw [hterm]
  simp only [h1, h2]

/-- The rescaled oriented walk vector as a plain `Fin m → ℝ`-valued function of the driving
data, measurable, exactly the function `Parking.walkFddVec` wraps into `EuclideanSpace`. -/
theorem measurable_walkFddVecPlain (m n : ℕ) (ts : Fin m → ℝ) :
    Measurable (fun (p : ℕ → Fin 2 × Bool) (i : Fin m) =>
      orientedScaledSite n (orientedPath (0 : Site 2) p ⌊(n : ℝ) * ts i⌋₊)) :=
  measurable_pi_lambda _ fun i =>
    measurable_of_finite_dependence (d := 2) (by norm_num) _ _
      (fun p q hpq => by rw [orientedPath_congr (0 : Site 2) _ (fun j hj => hpq j hj)])

/-- **The finite-dimensional characteristic function of the rescaled oriented walk converges to
that of the quarter-Brownian motion**, at every linear combination. -/
theorem tendsto_charFun_linearCombination_of_quarterBrownian {ΩB : Type} [MeasurableSpace ΩB]
    (PB : Measure ΩB) (B : ℝ≥0 → ΩB → ℝ) (hB : IsQuarterBrownian B PB) {T : ℝ} (m : ℕ)
    (ts : Fin m → ℝ) (hts : ∀ i, ts i ∈ Set.Icc (0 : ℝ) T) (t : Fin m → ℝ) :
    Tendsto (fun n : ℕ => charFun ((walkLaw 2).map (fun p => ∑ k, t k *
        orientedScaledSite n (orientedPath (0 : Site 2) p ⌊(n : ℝ) * ts k⌋₊))) (1 : ℝ)) atTop
      (𝓝 (charFun (PB.map (fun β => ∑ k, t k * B (Real.toNNReal (ts k)) β)) (1 : ℝ))) := by
  have hbridge : ∀ n : ℕ, charFun ((walkLaw 2).map (fun p => ∑ k, t k *
        orientedScaledSite n (orientedPath (0 : Site 2) p ⌊(n : ℝ) * ts k⌋₊))) (1 : ℝ)
      = charFun ((walkFddLaw m n ts : ProbabilityMeasure (EuclideanSpace ℝ (Fin m))) :
          Measure (EuclideanSpace ℝ (Fin m))) (WithLp.toLp 2 t : EuclideanSpace ℝ (Fin m)) := by
    intro n
    exact charFun_map_linearCombination_eq (walkLaw 2) (m := m)
      (fun p i => orientedScaledSite n (orientedPath (0 : Site 2) p ⌊(n : ℝ) * ts i⌋₊))
      (measurable_walkFddVecPlain m n ts) t
  have hQ : (∑ i : Fin m, ∑ l : Fin m, t i * t l * min (ts i) (ts l))
      = ∑ i : Fin m, ∑ l : Fin m, t i * t l * (min (Real.toNNReal (ts i))
          (Real.toNNReal (ts l)) : ℝ) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    rw [Real.coe_toNNReal (ts i) (hts i).1, Real.coe_toNNReal (ts l) (hts l).1]
  have hlim : Tendsto (fun n : ℕ => charFun ((walkFddLaw m n ts : ProbabilityMeasure
      (EuclideanSpace ℝ (Fin m))) : Measure (EuclideanSpace ℝ (Fin m)))
      (WithLp.toLp 2 t : EuclideanSpace ℝ (Fin m))) atTop
      (𝓝 (Complex.exp (-(↑(∑ i : Fin m, ∑ l : Fin m,
        t i * t l * min (ts i) (ts l)) : ℂ) / 8))) :=
    tendsto_charFun_walkFddLaw m ts hts (WithLp.toLp 2 t : EuclideanSpace ℝ (Fin m))
  have hrhs : charFun (PB.map (fun β => ∑ k, t k * B (Real.toNNReal (ts k)) β)) (1 : ℝ)
      = Complex.exp (-(↑(∑ i : Fin m, ∑ l : Fin m,
        t i * t l * min (ts i) (ts l)) : ℂ) / 8) := by
    rw [charFun_quarterBrownian_linearCombination hB, hQ]
  rw [hrhs]
  exact (hlim.congr' (Filter.Eventually.of_forall fun n => (hbridge n).symm))

/-- **`hWalk`: the finite-dimensional convergence in law of the rescaled oriented walk to a
concrete quarter-Brownian motion.** The exact shape
`Parking.tendsto_integral_orientedCutoffValue` consumes as its `hWalk` hypothesis. -/
theorem hWalk_of_quarterBrownian {ΩB : Type} [MeasurableSpace ΩB] (PB : Measure ΩB)
    [IsProbabilityMeasure PB] (B : ℝ≥0 → ΩB → ℝ) (hBmeas : ∀ t, Measurable (B t))
    (hB : IsQuarterBrownian B PB) {T : ℝ} (m : ℕ) (ts : Fin m → ℝ)
    (hts : ∀ i, ts i ∈ Set.Icc (0 : ℝ) T) (F : BoundedContinuousFunction (Fin m → ℝ) ℝ) :
    Tendsto (fun n : ℕ => ∫ p, F (fun i => orientedScaledSite n
        (orientedPath (0 : Site 2) p ⌊(n : ℝ) * ts i⌋₊)) ∂(walkLaw 2)) atTop
      (𝓝 (∫ β, F (fun i => B (Real.toNNReal (ts i)) β) ∂PB)) := by
  haveI : IsProbabilityMeasure (walkLaw 2) := by
    haveI := stepLaw_isProbability (d := 2) (by norm_num)
    unfold walkLaw; infer_instance
  have hXm : ∀ n : ℕ, Measurable (fun p : ℕ → Fin 2 × Bool => fun i : Fin m =>
      orientedScaledSite n (orientedPath (0 : Site 2) p ⌊(n : ℝ) * ts i⌋₊)) :=
    fun n => measurable_walkFddVecPlain m n ts
  have hZm : Measurable (fun β : ΩB => fun i : Fin m => B (Real.toNNReal (ts i)) β) :=
    measurable_pi_lambda _ fun i => (hBmeas (Real.toNNReal (ts i)))
  have hcomb : ∀ t : Fin m → ℝ, Tendsto (fun n : ℕ => charFun (((fun _ : ℕ => walkLaw 2) n).map
      (fun p => ∑ k, t k * (fun i : Fin m => orientedScaledSite n
        (orientedPath (0 : Site 2) p ⌊(n : ℝ) * ts i⌋₊)) k)) (1 : ℝ)) atTop
      (𝓝 (charFun (PB.map (fun β => ∑ k, t k *
        (fun i : Fin m => B (Real.toNNReal (ts i)) β) k)) (1 : ℝ))) := fun t =>
    tendsto_charFun_linearCombination_of_quarterBrownian PB B hB m ts hts t
  have hTID := tendstoInDistribution_of_tendsto_charFun_linearCombination
    (P := fun _ : ℕ => walkLaw 2) (Q := PB) hXm hZm hcomb
  have hport : Tendsto (fun n : ℕ => ∫ x, F x ∂((walkLaw 2).map (fun p : ℕ → Fin 2 × Bool =>
        fun i : Fin m => orientedScaledSite n
          (orientedPath (0 : Site 2) p ⌊(n : ℝ) * ts i⌋₊)))) atTop
      (𝓝 (∫ x, F x ∂(PB.map (fun β => fun i : Fin m => B (Real.toNNReal (ts i)) β)))) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hTID.tendsto F
  have heqL : (fun n : ℕ => ∫ x, F x ∂((walkLaw 2).map (fun p : ℕ → Fin 2 × Bool =>
        fun i : Fin m => orientedScaledSite n
          (orientedPath (0 : Site 2) p ⌊(n : ℝ) * ts i⌋₊))))
      = fun n => ∫ p, F (fun i => orientedScaledSite n
          (orientedPath (0 : Site 2) p ⌊(n : ℝ) * ts i⌋₊)) ∂(walkLaw 2) := by
    funext n
    exact integral_map (hXm n).aemeasurable F.continuous.aestronglyMeasurable
  have heqR : (∫ x, F x ∂(PB.map (fun β => fun i : Fin m => B (Real.toNNReal (ts i)) β)))
      = ∫ β, F (fun i => B (Real.toNNReal (ts i)) β) ∂PB :=
    integral_map hZm.aemeasurable F.continuous.aestronglyMeasurable
  rw [heqL, heqR] at hport
  exact hport

end Parking

end
