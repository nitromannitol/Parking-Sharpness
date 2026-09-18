/-
The `(scenePair,barDivisible,barOdometer)` three-block joint finite-dimensional convergence:
`Parking.External.SpatialOdometerScaling`'s own `(scenePair,barDivisible)` joint clause,
combined with the vanishing-distance transfer to `barOdometer`
(`Parking.exists_spatial_vanishing_distance`) via Slutsky's theorem
(`Parking.Generic.Slutsky.tendsto_prodMk_of_tendsto_zero`).  This is the non-`signedPair` part
of the big joint clause of `Parking.Frozen.spatial_scaling` (`parking.tex:1679-1737`); the
`signedPair` block needs the separate middle-term Taylor/Riemann-sum identification of the
paper's Step 2, which is not part of this module.
-/
import Parking.External.SpatialOdometerScaling
import Parking.Support.SpatialVanishingDistance
import Parking.Support.NearestBallEvent
import Parking.Support.SpatWSceneryFdd
import Parking.Generic.Slutsky

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section
namespace Parking

variable {d : ℕ}

/-- **The three-block joint finite-dimensional convergence** `(scenePair,barDivisible,
barOdometer) ⟹ (W,Uc,Uc)`, jointly, from `Parking.External.SpatialOdometerScaling` and
`Parking.exists_spatial_vanishing_distance` alone (no `signedPair` block). -/
theorem tendsto_scenePair_barDivisible_barOdometer_joint_fdd
    (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : Parking.External.SandpileGrowth) (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration) (hGreenNorms : Parking.External.GreenNorms)
    (hOdometer : Parking.External.SpatialOdometerScaling)
    (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
      (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ) (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ),
      ∀ (m k : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ) (sp : Fin k → ℝ × (Fin d → ℝ)),
        (∀ i, Parking.IsTestFun (φ i)) → (∀ j, 0 < (sp j).1) →
        ∀ F : BoundedContinuousFunction ((Fin m → ℝ) × (Fin k → ℝ) × (Fin k → ℝ)) ℝ,
          Tendsto (fun R : ℝ => ∫ w, F (fun i => Parking.scenePair w R (φ i),
                fun j => Parking.barDivisible w R (sp j).1 (sp j).2,
                fun j => Parking.barOdometer w R (sp j).1 (sp j).2) ∂(Parking.law d ν)) atTop
            (𝓝 (∫ ω, F (fun i => W (φ i) ω,
                fun j => Uc ω (sp j).1 (sp j).2,
                fun j => Uc ω (sp j).1 (sp j).2) ∂Q)) := by
  obtain ⟨Ω, mΩ, Q, hQ, W, Z, Uc, hW, hWmeas, hZeq, hZcont, hUc0, hUccont, hUcmono, hUcmeas,
      hsuprep, hjointFDD, hequicont⟩ := hOdometer d hd hd3 ν hν
  refine ⟨Ω, mΩ, Q, hQ, W, Uc, ?_⟩
  intro m k φ sp hφ hsp F
  haveI := hν.prob
  haveI := Parking.law_isProb hd ν
  set Y : ℝ → Data d → Fin k → ℝ := fun R w j =>
    Parking.barOdometer w R (sp j).1 (sp j).2 - Parking.barDivisible w R (sp j).1 (sp j).2
    with hYdef
  have hYzero : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun R : ℝ => ((Parking.law d ν) {w | ε < ‖Y R w‖}).toReal) atTop (𝓝 0) := by
    apply Parking.Generic.Slutsky.tendsto_zero_pi_of_forall_tendsto_zero
    intro c ε hε
    have hstep := Parking.exists_spatial_vanishing_distance hd hd3 hGrowth hBernstein
      hConcentration hGreenNorms ν hν {sp c} isCompact_singleton
      (fun p hp => by rw [Set.mem_singleton_iff] at hp; rw [hp]; exact hsp c) ε hε
    have hsup_eq : ∀ R w, (⨆ p ∈ ({sp c} : Set (ℝ × (Fin d → ℝ))),
          |Parking.barOdometer w R p.1 p.2 - Parking.barDivisible w R p.1 p.2|)
        = |Parking.barOdometer w R (sp c).1 (sp c).2 - Parking.barDivisible w R (sp c).1 (sp c).2| := by
      intro R w
      apply le_antisymm
      · exact Real.iSup_le (fun p => Real.iSup_le (fun hp => by
          rw [Set.mem_singleton_iff] at hp; rw [hp]) (abs_nonneg _)) (abs_nonneg _)
      · exact Parking.le_biSup_of_bound ({sp c} : Set (ℝ × (Fin d → ℝ)))
          (fun p => |Parking.barOdometer w R p.1 p.2 - Parking.barDivisible w R p.1 p.2|)
          (abs_nonneg _)
          (fun p hp => by rw [Set.mem_singleton_iff] at hp; rw [hp]) (Set.mem_singleton _)
    simp only [hsup_eq] at hstep
    simpa [hYdef] using hstep
  have hXm : ∀ R : ℝ, AEMeasurable (fun w => (fun i => Parking.scenePair w R (φ i),
      fun j => Parking.barDivisible w R (sp j).1 (sp j).2)) (Parking.law d ν) :=
    fun R => (Measurable.prodMk
      (measurable_pi_lambda _ fun i => Parking.measurable_scenePair_any_R R)
      (measurable_pi_lambda _ fun j => Parking.measurable_barDivisible R (sp j).1 (sp j).2)
      : Measurable _).aemeasurable
  have hYm : ∀ R : ℝ, AEMeasurable (Y R) (Parking.law d ν) := fun R =>
    (measurable_pi_lambda _ fun j =>
      (Parking.measurable_barOdometer R (sp j).1 (sp j).2).sub
        (Parking.measurable_barDivisible R (sp j).1 (sp j).2)).aemeasurable
  have hZm : AEMeasurable (fun ω => (fun i => W (φ i) ω, fun j => Uc ω (sp j).1 (sp j).2)) Q :=
    (Measurable.prodMk
      (measurable_pi_lambda _ fun i => hWmeas (φ i) (hφ i))
      (measurable_pi_lambda _ fun j => hUcmeas (sp j).1 (sp j).2)
      : Measurable _).aemeasurable
  have hjoint := Parking.Generic.Slutsky.tendsto_prodMk_of_tendsto_zero
    hXm hYm hZm (hjointFDD m k φ sp hφ hsp) hYzero
  set g : ((Fin m → ℝ) × (Fin k → ℝ)) × (Fin k → ℝ) → (Fin m → ℝ) × (Fin k → ℝ) × (Fin k → ℝ) :=
    fun p => (p.1.1, p.1.2, fun j => p.1.2 j + p.2 j) with hgdef
  have hgcont : Continuous g := by
    refine Continuous.prodMk continuous_fst.fst (Continuous.prodMk continuous_fst.snd ?_)
    exact continuous_pi fun j =>
      ((continuous_apply j).comp continuous_fst.snd).add ((continuous_apply j).comp continuous_snd)
  have hres := hjoint (F.compContinuous ⟨g, hgcont⟩)
  have heqL : (fun R : ℝ => ∫ w, F.compContinuous (⟨g, hgcont⟩ : C(_, _))
      ((fun i => Parking.scenePair w R (φ i), fun j => Parking.barDivisible w R (sp j).1 (sp j).2),
        Y R w) ∂(Parking.law d ν))
      = fun R : ℝ => ∫ w, F (fun i => Parking.scenePair w R (φ i),
          fun j => Parking.barDivisible w R (sp j).1 (sp j).2,
          fun j => Parking.barOdometer w R (sp j).1 (sp j).2) ∂(Parking.law d ν) := by
    funext R
    congr 1
    funext w
    show F (g ((fun i => Parking.scenePair w R (φ i),
      fun j => Parking.barDivisible w R (sp j).1 (sp j).2), Y R w)) = _
    have hgeq : g ((fun i => Parking.scenePair w R (φ i),
        fun j => Parking.barDivisible w R (sp j).1 (sp j).2), Y R w)
      = (fun i => Parking.scenePair w R (φ i),
          fun j => Parking.barDivisible w R (sp j).1 (sp j).2,
          fun j => Parking.barOdometer w R (sp j).1 (sp j).2) := by
      simp only [hgdef]
      refine Prod.ext rfl (Prod.ext rfl ?_)
      funext j
      simp only [hYdef]
      ring
    rw [hgeq]
  have heqR : (∫ ω', F.compContinuous (⟨g, hgcont⟩ : C(_, _))
      ((fun i => W (φ i) ω', fun j => Uc ω' (sp j).1 (sp j).2), (0 : Fin k → ℝ)) ∂Q)
      = ∫ ω, F (fun i => W (φ i) ω, fun j => Uc ω (sp j).1 (sp j).2,
          fun j => Uc ω (sp j).1 (sp j).2) ∂Q := by
    congr 1
    funext ω
    show F (g ((fun i => W (φ i) ω, fun j => Uc ω (sp j).1 (sp j).2), (0 : Fin k → ℝ))) = _
    have hgeq : g ((fun i => W (φ i) ω, fun j => Uc ω (sp j).1 (sp j).2), (0 : Fin k → ℝ))
        = (fun i => W (φ i) ω, fun j => Uc ω (sp j).1 (sp j).2, fun j => Uc ω (sp j).1 (sp j).2) := by
      simp only [hgdef]
      refine Prod.ext rfl (Prod.ext rfl ?_)
      funext j
      simp
    rw [hgeq]
  rw [heqL, heqR] at hres
  exact hres

end Parking

end
