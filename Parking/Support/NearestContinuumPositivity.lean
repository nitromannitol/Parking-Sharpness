/-
Positivity of the continuum odometer at `(1,0)`, as used in the proof of
`thm:nearest` at `parking.tex:1807-1833`. The critical lower-tail estimate
passes to the limit through the open-set inequality in Portmanteau. The
finite-dimensional convergence hypothesis below is exactly the clause of
`prop:spatial-scaling`; no local uniform convergence is used for this marginal
conclusion. Continuity then gives a positive ball in each limiting sample.
-/
import Parking.Support.NearestCriticalTail
import Mathlib.MeasureTheory.Measure.Portmanteau

noncomputable section
open MeasureTheory ProbabilityTheory LatticeProb Filter Topology Parking.CriticalScale

/-- Open-set Portmanteau excludes an atom at zero and all negative mass. -/
theorem Parking.ae_pos_of_weak_lower_tails (μ : ProbabilityMeasure ℝ)
    (μs : ℕ → ProbabilityMeasure ℝ) (hc : Tendsto μs atTop (𝓝 μ))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ n : ℕ in atTop, (μs n : Measure ℝ) (Set.Iic δ) ≤ ENNReal.ofReal ε) :
    ∀ᵐ x ∂(μ : Measure ℝ), 0 < x := by
  have hb (ε : ℝ) (hε : 0 < ε) : (μ : Measure ℝ) (Set.Iic 0) ≤ ENNReal.ofReal ε := by
    obtain ⟨δ, hδ, hn⟩ := hsmall ε hε
    calc
      (μ : Measure ℝ) (Set.Iic 0) ≤ (μ : Measure ℝ) (Set.Iio δ) :=
        measure_mono (fun _ hx => lt_of_le_of_lt hx hδ)
      _ ≤ liminf (fun n => (μs n : Measure ℝ) (Set.Iio δ)) atTop :=
        ProbabilityMeasure.le_liminf_measure_open_of_tendsto hc isOpen_Iio
      _ ≤ ENNReal.ofReal ε := liminf_le_of_frequently_le' (hn.mono
        (fun n h => (measure_mono Set.Iio_subset_Iic_self).trans h)).frequently
  have hz : (μ : Measure ℝ) (Set.Iic 0) ≤ 0 := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    simpa only [zero_add, ENNReal.ofReal_coe_nnreal] using hb (ε : ℝ) (by exact_mod_cast hε)
  change (μ : Measure ℝ) {x | ¬ 0 < x} = 0
  simpa only [Set.Iic_def, not_lt] using le_antisymm hz bot_le

theorem Parking.ae_pos_of_convergence_in_law_lower_tails
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (Xn : ℕ → Ω → ℝ) (X : Ω' → ℝ) (hXn : ∀ n, Measurable (Xn n)) (hX : Measurable X)
    (hc : ∀ F : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n => ∫ ω, F (Xn n ω) ∂P) atTop (𝓝 (∫ ω, F (X ω) ∂Q)))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ n : ℕ in atTop, P {ω | Xn n ω ≤ δ} ≤ ENNReal.ofReal ε) :
    ∀ᵐ ω ∂Q, 0 < X ω := by
  let μ : ProbabilityMeasure ℝ := ⟨Q.map X, Measure.isProbabilityMeasure_map hX.aemeasurable⟩
  let μs : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨P.map (Xn n), Measure.isProbabilityMeasure_map (hXn n).aemeasurable⟩
  have hweak : Tendsto μs atTop (𝓝 μ) := by
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro F
    change Tendsto (fun n => ∫ z, F z ∂(P.map (Xn n))) atTop
      (𝓝 (∫ z, F z ∂(Q.map X)))
    have hFn (n : ℕ) : (∫ z, F z ∂(P.map (Xn n))) = ∫ ω, F (Xn n ω) ∂P :=
      integral_map (hXn n).aemeasurable F.continuous.measurable.aestronglyMeasurable
    simp_rw [hFn, integral_map hX.aemeasurable F.continuous.measurable.aestronglyMeasurable]
    exact hc F
  have hs : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ n : ℕ in atTop, (μs n : Measure ℝ) (Set.Iic δ) ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := hsmall ε hε
    refine ⟨δ, hδ, h.mono fun n hn => ?_⟩
    change (P.map (Xn n)) (Set.Iic δ) ≤ ENNReal.ofReal ε
    rw [Measure.map_apply (hXn n) measurableSet_Iic]
    exact hn
  have ha := Parking.ae_pos_of_weak_lower_tails μ μs hweak hs
  change (Q.map X) {z | ¬ 0 < z} = 0 at ha
  have hm : MeasurableSet {z : ℝ | ¬ 0 < z} := by
    simpa only [not_lt, Set.Iic_def] using (measurableSet_Iic (a := (0 : ℝ)))
  rw [Measure.map_apply hX hm] at ha
  exact ha

/-- Project the spatial proposition's joint law onto `barDivisible R 1 0`. -/
theorem Parking.spatial_fdd_at_origin {d : ℕ} (ν : Measure ℤ)
    {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω)
    (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ)
    (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hFDD : ∀ (m k p : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ) (χ : Fin p → (Fin d → ℝ) → ℝ)
          (sp : Fin k → ℝ × (Fin d → ℝ)),
        (∀ i, Parking.IsTestFun (φ i)) → (∀ l, Parking.IsTestFun (χ l)) →
        (∀ j, 0 < (sp j).1) →
        ∀ F : BoundedContinuousFunction
            ((Fin m → ℝ) × (Fin k → ℝ) × (Fin k → ℝ) × (Fin p → ℝ)) ℝ,
          Tendsto (fun R : ℝ => ∫ w, F (fun i => Parking.scenePair w R (φ i),
                fun j => Parking.barDivisible w R (sp j).1 (sp j).2,
                fun j => Parking.barOdometer w R (sp j).1 (sp j).2,
                fun l => Parking.signedPair w R (χ l)) ∂(Parking.law d ν)) atTop
            (𝓝 (∫ ω, F (fun i => W (φ i) ω,
                fun j => Uc ω (sp j).1 (sp j).2,
                fun j => Uc ω (sp j).1 (sp j).2,
                fun l => W (χ l) ω
                  + ∫ x, Uc ω 1 x * Parking.contOp d (χ l) x) ∂Q))) :
    ∀ F : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun R : ℝ => ∫ w, F (Parking.barDivisible w R 1 0) ∂(Parking.law d ν))
        atTop (𝓝 (∫ ω, F (Uc ω 1 0) ∂Q)) := by
  intro F
  let G : BoundedContinuousFunction
      ((Fin 0 → ℝ) × (Fin 1 → ℝ) × (Fin 1 → ℝ) × (Fin 0 → ℝ)) ℝ :=
    F.compContinuous ⟨fun z => z.2.1 0, by fun_prop⟩
  have h := hFDD 0 1 0 (fun _ => 0) (fun _ => 0) (fun _ => (1, 0))
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun _ => by norm_num) G
  exact h

theorem Parking.ae_pos_of_critical_scale_lower_tail
    (hLower : Parking.External.CriticalScaleLowerTail)
    (hVar : Parking.External.VarianceScale) (hBerry : Parking.External.MultivariateBerryEsseen)
    {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ) (hν : Parking.CriticalLaw ν)
    {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ) (hm : Measurable (fun ω => Uc ω 1 0))
    (hconv : ∀ F : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun R : ℝ => ∫ w, F (Parking.barDivisible w R 1 0) ∂(Parking.law d ν)) atTop
        (𝓝 (∫ ω, F (Uc ω 1 0) ∂Q))) :
    ∀ᵐ ω ∂Q, 0 < Uc ω 1 0 := by
  haveI := hν.prob
  haveI := Parking.stackRankLaw_isProbability hd
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  haveI : IsProbabilityMeasure (Parking.law d ν) :=
    inferInstanceAs (IsProbabilityMeasure ((iidLaw d ν).prod (Parking.stackRankLaw d)))
  apply Parking.ae_pos_of_convergence_in_law_lower_tails (Parking.law d ν) Q
    (fun t ω => (t : ℝ) ^ (-((4 - (d : ℝ)) / 4)) * Parking.uOf ω t 0)
    (fun ω => Uc ω 1 0) (fun t => (Parking.measurable_uOf t 0).const_mul _) hm
  · intro F
    have h := (hconv F).comp (Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun t : ℕ => (t : ℝ)) atTop atTop))
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with t ht
    apply integral_congr_ae
    exact ae_of_all _ fun ω => congrArg F (barDivisible_sqrt ω t (by omega))
  · exact Parking.scaled_lower_tails_small hLower hVar hBerry hd hd3 ν hν

/-- The source lower tail and the exact spatial finite-dimensional clause imply positivity. -/
theorem Parking.ae_spatial_origin_pos
    (hLower : Parking.External.CriticalScaleLowerTail)
    (hVar : Parking.External.VarianceScale) (hBerry : Parking.External.MultivariateBerryEsseen)
    {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ) (hν : Parking.CriticalLaw ν)
    {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ)
    (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hm : ∀ s x, Measurable (fun ω => Uc ω s x))
    (hFDD : ∀ (m k p : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ) (χ : Fin p → (Fin d → ℝ) → ℝ)
          (sp : Fin k → ℝ × (Fin d → ℝ)),
        (∀ i, Parking.IsTestFun (φ i)) → (∀ l, Parking.IsTestFun (χ l)) →
        (∀ j, 0 < (sp j).1) →
        ∀ F : BoundedContinuousFunction
            ((Fin m → ℝ) × (Fin k → ℝ) × (Fin k → ℝ) × (Fin p → ℝ)) ℝ,
          Tendsto (fun R : ℝ => ∫ w, F (fun i => Parking.scenePair w R (φ i),
                fun j => Parking.barDivisible w R (sp j).1 (sp j).2,
                fun j => Parking.barOdometer w R (sp j).1 (sp j).2,
                fun l => Parking.signedPair w R (χ l)) ∂(Parking.law d ν)) atTop
            (𝓝 (∫ ω, F (fun i => W (φ i) ω,
                fun j => Uc ω (sp j).1 (sp j).2,
                fun j => Uc ω (sp j).1 (sp j).2,
                fun l => W (χ l) ω
                  + ∫ x, Uc ω 1 x * Parking.contOp d (χ l) x) ∂Q))) : ∀ᵐ ω ∂Q, 0 < Uc ω 1 0 := by
  exact Parking.ae_pos_of_critical_scale_lower_tail hLower hVar hBerry hd hd3 ν hν Q Uc
    (hm 1 0) (Parking.spatial_fdd_at_origin ν Q W Uc hFDD)

theorem Parking.exists_pos_l1_ball {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) (h0 : 0 < f 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : Fin d → ℝ, (∑ i, |x i|) ≤ r → 0 < f x := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (hf.continuousAt.eventually (eventually_gt_nhds h0))
  refine ⟨ε / 2, half_pos hε, fun x hx => hball ?_⟩
  have hn : ‖x‖ ≤ ε / 2 := (pi_norm_le_iff_of_nonneg (half_pos hε).le).mpr fun i => by
    rw [Real.norm_eq_abs]
    exact (Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)).trans hx
  rw [Metric.mem_ball, dist_zero_right]
  exact hn.trans_lt (by linarith)

theorem Parking.ae_exists_pos_l1_ball {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hcont : ∀ ω, Continuous (fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2))
    (hpos : ∀ᵐ ω ∂Q, 0 < Uc ω 1 0) :
    ∀ᵐ ω ∂Q, ∃ r : ℝ, 0 < r ∧ ∀ x : Fin d → ℝ,
      (∑ i, |x i|) ≤ r → 0 < Uc ω 1 x := by
  filter_upwards [hpos] with ω hω
  exact Parking.exists_pos_l1_ball ((hcont ω).comp (continuous_const.prodMk continuous_id)) hω

end
