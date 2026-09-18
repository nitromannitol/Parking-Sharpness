/- `prop:oriented-scaling` from the convergence in distribution at a single time.

The frozen statement (`parking.tex:3151-3159`) asserts the convergence in distribution of
`n^{-1/4} u_{⌊nT⌋}(0)` for EVERY `T > 0`, together with the parabolic self-similarity
`U(T) =_d T^{1/4} U(1)` of the limit.  The paper reads the self-similarity off the
continuum object of its Step 1 and states it separately in Step 2.  It is cheaper, and it
proves the same statement, to read it off the prefactors instead: writing
`m_n = ⌊nT⌋` and `a_n = (m_n/n)^{1/4}`,

  `n^{-1/4} u_{m_n}(0) = a_n · (m_n^{-1/4} u_{m_n}(0))`,

and `a_n → T^{1/4}` because `m_n/(nT) → 1`.  So the convergence at time `T` is the
convergence at time one along the subsequence `m_n`, rescaled by a deterministic sequence
of constants; Slutsky's theorem transports it.  Taking the law of the limit at time one as
the underlying probability space and `T^{1/4} ·` as the limit at time `T` then makes the
self-similarity clause an identity of pushforwards under the same map.

The whole proposition therefore rests on ONE analytic statement: that the laws of
`n^{-1/4} u_n(0)` converge weakly on the line.  Everything else is soft.
-/
import Parking.Support.OrientedScalingReduced
import Parking.Support.ScalParabolicScaling
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

noncomputable section
namespace Parking
open MeasureTheory Filter Topology LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Weak convergence of the laws of real random variables, written through bounded
continuous test functions, is convergence in distribution to the identity on the limit
law. -/
theorem tendstoInDistribution_id_of_integral_bcf
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ n, AEMeasurable (X n) P) (L : Measure ℝ) [IsProbabilityMeasure L]
    (h : ∀ F : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n => ∫ ω, F (X n ω) ∂P) atTop (𝓝 (∫ x, F x ∂L))) :
    TendstoInDistribution X atTop (id : ℝ → ℝ) (fun _ => P) L where
  forall_aemeasurable := hX
  aemeasurable_limit := aemeasurable_id
  tendsto := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    simpa [integral_map (hX _) f.continuous.aestronglyMeasurable, Measure.map_id] using h f

/-- Convergence in distribution, read back as convergence of the integrals of bounded
continuous test functions. -/
theorem tendsto_integral_bcf_of_tendstoInDistribution {Ω' : Type*} [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (X : ℕ → Ω → ℝ) (Z : Ω' → ℝ)
    (h : TendstoInDistribution X atTop Z (fun _ => P) Q) (F : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun n => ∫ ω, F (X n ω) ∂P) atTop (𝓝 (∫ ω, F (Z ω) ∂Q)) := by
  have h2 := h.tendsto
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at h2
  have h3 := h2 F
  simpa [integral_map (h.forall_aemeasurable _) F.continuous.aestronglyMeasurable,
    integral_map h.aemeasurable_limit F.continuous.aestronglyMeasurable] using h3

/-- A sequence of constants converging in the line converges in measure. -/
theorem tendstoInMeasure_const_of_tendsto (P : Measure Ω) [IsFiniteMeasure P]
    {a : ℕ → ℝ} {c : ℝ} (ha : Tendsto a atTop (𝓝 c)) :
    TendstoInMeasure P (fun n (_ : Ω) => a n) atTop (fun _ => c) := by
  refine tendstoInMeasure_of_ne_top fun ε hε _ => ?_
  have hev : ∀ᶠ n in atTop, edist (a n) c < ε := EMetric.tendsto_nhds.mp ha ε hε
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [hev] with n hn
  have hempty : {x : Ω | ε ≤ edist (a n) c} = ∅ := by
    ext x; simp [not_le.mpr hn]
  simp [hempty]

/-- **Weak convergence against a deterministic prefactor.**  If the laws of `X n` converge
weakly to `L` and `a n → c`, then the laws of `a n · X n` converge weakly to the law of
`c · id` under `L`.  This is Slutsky's theorem for a sequence of constants. -/
theorem tendsto_integral_bcf_mul_of_weak
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ n, AEMeasurable (X n) P) (L : Measure ℝ) [IsProbabilityMeasure L]
    (h : ∀ F : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n => ∫ ω, F (X n ω) ∂P) atTop (𝓝 (∫ x, F x ∂L)))
    {a : ℕ → ℝ} {c : ℝ} (ha : Tendsto a atTop (𝓝 c)) (F : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun n => ∫ ω, F (a n * X n ω) ∂P) atTop (𝓝 (∫ x, F (c * x) ∂L)) := by
  have hd := tendstoInDistribution_id_of_integral_bcf P X hX L h
  have hs := hd.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : ℝ × ℝ => p.2 * p.1) (by fun_prop)
      (tendstoInMeasure_const_of_tendsto P ha) (fun _ => aemeasurable_const)
  exact tendsto_integral_bcf_of_tendstoInDistribution P L _ _ hs F

/-- The prefactor identity behind the parabolic rescaling: at a positive integer horizon
the prefactor at time `n` is the prefactor at the horizon `m` times `(m/n)^{1/4}`. -/
theorem rpow_quarter_ratio_mul (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (u : ℝ) :
    ((m : ℝ) / (n : ℝ)) ^ ((1 : ℝ) / 4) * ((m : ℝ) ^ (-(1 : ℝ) / 4) * u)
      = (n : ℝ) ^ (-(1 : ℝ) / 4) * u := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Real.div_rpow hm0.le hn0.le]
  have h1 : (-(1 : ℝ) / 4) = -((1 : ℝ) / 4) := by ring
  rw [h1, Real.rpow_neg hm0.le, Real.rpow_neg hn0.le]
  have hmp : (0 : ℝ) < (m : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hm0 _
  have hnp : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hn0 _
  field_simp

/-- The rescaled horizon tends to infinity. -/
theorem tendsto_floor_horizon_atTop (T : ℝ) (hT : 0 < T) :
    Tendsto (fun n : ℕ => ⌊(n : ℝ) * T⌋₊) atTop atTop := by
  have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) * T) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const hT tendsto_natCast_atTop_atTop
  exact tendsto_nat_floor_atTop.comp h1

/-- The ratio of the prefactor at time `n` to the prefactor at the rescaled horizon tends
to `T^{1/4}`. -/
theorem tendsto_quarter_ratio (T : ℝ) (hT : 0 < T) :
    Tendsto (fun n : ℕ => ((⌊(n : ℝ) * T⌋₊ : ℝ) / (n : ℝ)) ^ ((1 : ℝ) / 4))
      atTop (𝓝 (T ^ ((1 : ℝ) / 4))) := by
  have hne : T ≠ 0 := ne_of_gt hT
  have h0 := tendsto_floor_mul_div T hT
  have hdiv : Tendsto (fun n : ℕ => ((⌊(n : ℝ) * T⌋₊ : ℝ) / (n : ℝ))) atTop (𝓝 T) := by
    have h1 : Tendsto (fun n : ℕ => ((⌊(n : ℝ) * T⌋₊ : ℝ) / ((n : ℝ) * T)) * T) atTop (𝓝 T) := by
      simpa using h0.mul_const T
    refine h1.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  exact ((Real.continuousAt_rpow_const T ((1 : ℝ) / 4) (Or.inl hne)).tendsto).comp hdiv


/-- **The convergence at a rescaled horizon from the convergence at time one.** -/
theorem tendsto_weak_horizon (ν : Measure ℤ) (hν : CriticalLaw ν)
    (L : Measure ℝ) (hL : IsProbabilityMeasure L)
    (hone : ∀ F : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ => ∫ w, F ((n : ℝ) ^ (-(1 : ℝ) / 4) *
            uOriented (fun y => (w.1 y : ℝ)) n 0) ∂(orientedLaw 2 ν)) atTop
        (𝓝 (∫ x, F x ∂L)))
    (T : ℝ) (hT : 0 < T) (F : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun n : ℕ => ∫ w, F ((n : ℝ) ^ (-(1 : ℝ) / 4) *
        uOriented (fun y => (w.1 y : ℝ)) ⌊(n : ℝ) * T⌋₊ 0) ∂(orientedLaw 2 ν)) atTop
      (𝓝 (∫ x, F (T ^ ((1 : ℝ) / 4) * x) ∂L)) := by
  haveI := hν.prob
  haveI := hL
  haveI : IsProbabilityMeasure (orientedLaw 2 ν) := orientedLaw_isProbability (by norm_num) ν
  have hXm : ∀ m : ℕ, AEMeasurable
      (fun w : Data 2 => (m : ℝ) ^ (-(1 : ℝ) / 4) *
        uOriented (fun y => (w.1 y : ℝ)) m 0) (orientedLaw 2 ν) :=
    fun m => (measurable_const.mul
      ((measurable_uOriented m 0).comp measurable_confReal)).aemeasurable
  have hm := tendsto_floor_horizon_atTop T hT
  have hone' : ∀ G : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ => ∫ w, G ((((⌊(n : ℝ) * T⌋₊ : ℕ) : ℝ)) ^ (-(1 : ℝ) / 4) *
            uOriented (fun y => (w.1 y : ℝ)) ⌊(n : ℝ) * T⌋₊ 0) ∂(orientedLaw 2 ν))
        atTop (𝓝 (∫ x, G x ∂L)) := fun G => (hone G).comp hm
  have hsl := tendsto_integral_bcf_mul_of_weak (orientedLaw 2 ν)
    (fun n : ℕ => fun w : Data 2 => (((⌊(n : ℝ) * T⌋₊ : ℕ) : ℝ)) ^ (-(1 : ℝ) / 4) *
      uOriented (fun y => (w.1 y : ℝ)) ⌊(n : ℝ) * T⌋₊ 0)
    (fun n => hXm _) L hone' (tendsto_quarter_ratio T hT) F
  refine hsl.congr' ?_
  filter_upwards [eventually_ge_atTop 1, hm.eventually_ge_atTop 1] with n hn1 hn2
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  dsimp only
  rw [rpow_quarter_ratio_mul n ⌊(n : ℝ) * T⌋₊ hn1 hn2]

/-- **The self-similarity clause of `prop:oriented-scaling` is a consequence of its
convergence clause.**  Any family satisfying the convergence in distribution at every
positive time satisfies the parabolic self-similarity in law, so the frozen statement's third
clause adds nothing to its second. -/
theorem selfsimilar_of_weak (ν : Measure ℤ) (hν : CriticalLaw ν)
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) (hQ : IsProbabilityMeasure Q)
    (Uc : ℝ → Ω → ℝ) (hmeas : ∀ T : ℝ, 0 < T → Measurable (Uc T))
    (hlaw : ∀ T : ℝ, 0 < T → ∀ F : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ => ∫ w, F ((n : ℝ) ^ (-(1 : ℝ) / 4) *
            uOriented (fun y => (w.1 y : ℝ)) ⌊(n : ℝ) * T⌋₊ 0)
          ∂(orientedLaw 2 ν)) atTop (𝓝 (∫ ω, F (Uc T ω) ∂Q))) :
    ∀ T : ℝ, 0 < T → Q.map (Uc T) = Q.map fun ω => T ^ ((1 : ℝ) / 4) * Uc 1 ω := by
  haveI := hν.prob
  haveI := hQ
  intro T hT
  set L : Measure ℝ := Q.map (Uc 1) with hLdef
  haveI hL : IsProbabilityMeasure L := Measure.isProbabilityMeasure_map (hmeas 1 one_pos).aemeasurable
  have hint : ∀ F : BoundedContinuousFunction ℝ ℝ, ∫ x, F x ∂L = ∫ ω, F (Uc 1 ω) ∂Q := by
    intro F
    rw [hLdef, integral_map (hmeas 1 one_pos).aemeasurable F.continuous.aestronglyMeasurable]
  have hone : ∀ F : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ => ∫ w, F ((n : ℝ) ^ (-(1 : ℝ) / 4) *
            uOriented (fun y => (w.1 y : ℝ)) n 0) ∂(orientedLaw 2 ν)) atTop
        (𝓝 (∫ x, F x ∂L)) := by
    intro F
    rw [hint F]
    have h := hlaw 1 one_pos F
    simpa using h
  refine MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure ?_
  intro F
  have h1 := hlaw T hT F
  have h2 := tendsto_weak_horizon ν hν L hL hone T hT F
  have heq : ∫ ω, F (Uc T ω) ∂Q = ∫ x, F (T ^ ((1 : ℝ) / 4) * x) ∂L :=
    tendsto_nhds_unique h1 h2
  have hA : ∫ x, F x ∂(Q.map (Uc T)) = ∫ ω, F (Uc T ω) ∂Q :=
    integral_map (hmeas T hT).aemeasurable F.continuous.aestronglyMeasurable
  have hB : ∫ x, F x ∂(Q.map fun ω => T ^ ((1 : ℝ) / 4) * Uc 1 ω)
      = ∫ ω, F (T ^ ((1 : ℝ) / 4) * Uc 1 ω) ∂Q :=
    integral_map (measurable_const.mul (hmeas 1 one_pos)).aemeasurable
      F.continuous.aestronglyMeasurable
  have hC : ∫ x, F (T ^ ((1 : ℝ) / 4) * x) ∂L = ∫ ω, F (T ^ ((1 : ℝ) / 4) * Uc 1 ω) ∂Q := by
    rw [hLdef]
    exact integral_map (hmeas 1 one_pos).aemeasurable
      ((F.continuous.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
  rw [hA, hB, heq, hC]

theorem oriented_scaling_of_weak_one (ν : Measure ℤ) (hν : CriticalLaw ν)
    (L : Measure ℝ) (hL : IsProbabilityMeasure L)
    (hone : ∀ F : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ => ∫ w, F ((n : ℝ) ^ (-(1 : ℝ) / 4) *
            uOriented (fun y => (w.1 y : ℝ)) n 0) ∂(orientedLaw 2 ν)) atTop
        (𝓝 (∫ x, F x ∂L))) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
      (Uc : ℝ → Ω → ℝ) (μ : ℝ),
      (∀ T : ℝ, 0 < T → Measurable (Uc T)) ∧
      (∀ T : ℝ, 0 < T → ∀ F : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun n : ℕ => ∫ w, F ((n : ℝ) ^ (-(1 : ℝ) / 4) *
              uOriented (fun y => (w.1 y : ℝ)) ⌊(n : ℝ) * T⌋₊ 0)
            ∂(orientedLaw 2 ν)) atTop (𝓝 (∫ ω, F (Uc T ω) ∂Q))) ∧
      (∀ T : ℝ, 0 < T → Q.map (Uc T) = Q.map fun ω => T ^ ((1 : ℝ) / 4) * Uc 1 ω) ∧
      Integrable (Uc 1) Q ∧ μ = ∫ ω, Uc 1 ω ∂Q ∧ 0 < μ ∧
      Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 4) *
        meanuOriented (orientedLaw 2 ν) n) atTop (𝓝 μ) := by
  haveI := hν.prob
  haveI := hL
  haveI : IsProbabilityMeasure (orientedLaw 2 ν) := orientedLaw_isProbability (by norm_num) ν
  refine oriented_scaling_of_weak ν hν ℝ inferInstance L hL
    (fun T x => T ^ ((1 : ℝ) / 4) * x)
    (fun T _ => measurable_const.mul measurable_id) ?_ ?_
  · intro T hT F
    exact tendsto_weak_horizon ν hν L hL hone T hT F
  · intro T hT
    simp [Real.one_rpow]

end Parking
end
