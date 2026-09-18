/- Joint convergence of scenery, field coordinates, and spatial pairings. -/
import Parking.Support.SpatWBlockPairingConvergence
import Parking.Support.SpatWPairingConvergence
import Parking.Support.SpatWSceneryFdd

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section
namespace Parking

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {W : ((Fin d → ℝ) → ℝ) → Ω → ℝ} {Uc : Ω → ℝ → (Fin d → ℝ) → ℝ}

/-- The spatial pairings retain the scenery and any prescribed space-time coordinates. -/
theorem tendstoInDistribution_scenePair_barDivisible_pairings
    (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure (law d ν)]
    (hUccont : ∀ ω, Continuous fun q : ℝ × (Fin d → ℝ) => Uc ω q.1 q.2)
    (hUcmeas : ∀ s x, Measurable fun ω => Uc ω s x)
    (hWmeas : ∀ φ, IsTestFun φ → Measurable (W φ))
    (hjointFDD : ∀ (m p' : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ) (sp : Fin p' → ℝ × (Fin d → ℝ)),
      (∀ i, IsTestFun (φ i)) → (∀ j, 0 < (sp j).1) →
      ∀ F : BoundedContinuousFunction ((Fin m → ℝ) × (Fin p' → ℝ)) ℝ,
        Tendsto (fun R : ℝ => ∫ w, F (fun i => scenePair w R (φ i),
              fun j => barDivisible w R (sp j).1 (sp j).2) ∂law d ν) atTop
          (𝓝 (∫ ω, F (fun i => W (φ i) ω, fun j => Uc ω (sp j).1 (sp j).2) ∂Q)))
    (hequicont : ∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → (∀ p ∈ K, 0 < p.1) → ∀ ε : ℝ, 0 < ε →
      ∀ ε' : ℝ, 0 < ε' → ∃ δ : ℝ, 0 < δ ∧ ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
        ((law d ν) {w | ε < ⨆ p ∈ K, ⨆ q ∈ K, ⨆ _ : dist p q ≤ δ,
            |barDivisible w R p.1 p.2 - barDivisible w R q.1 q.2|}).toReal ≤ ε')
    {m k p : ℕ} (φ : Fin m → (Fin d → ℝ) → ℝ) (hφ : ∀ i, IsTestFun (φ i))
    (sp : Fin k → ℝ × (Fin d → ℝ)) (hsp : ∀ j, 0 < (sp j).1)
    (g : Fin p → (Fin d → ℝ) → ℝ) (hg : ∀ j, Continuous (g j))
    (K : Set (Fin d → ℝ)) (hK : IsCompact K) (hKne : K.Nonempty)
    (hsupp : ∀ j, Function.support (g j) ⊆ K) :
    TendstoInDistribution
      (fun R w => ((fun i => scenePair w R (φ i), fun j => barDivisible w R (sp j).1 (sp j).2),
        fun j => ∫ x, barDivisible w R 1 x * g j x)) atTop
      (fun ω => ((fun i => W (φ i) ω, fun j => Uc ω (sp j).1 (sp j).2),
        fun j => ∫ x, Uc ω 1 x * g j x)) (fun _ : ℝ => law d ν) Q := by
  let V := fun R (w : Data d) =>
    (fun i => scenePair w R (φ i), fun j => barDivisible w R (sp j).1 (sp j).2)
  let Vlim := fun ω => (fun i => W (φ i) ω, fun j => Uc ω (sp j).1 (sp j).2)
  have hVm : ∀ R, Measurable (V R) := fun R =>
    (measurable_pi_lambda _ fun _ => measurable_scenePair_any_R R).prodMk
      (measurable_pi_lambda _ fun j => measurable_barDivisible R (sp j).1 (sp j).2)
  have hVlimm : Measurable Vlim :=
    (measurable_pi_lambda _ fun i => hWmeas (φ i) (hφ i)).prodMk
      (measurable_pi_lambda _ fun j => hUcmeas (sp j).1 (sp j).2)
  have hfdd : ∀ (n : ℕ) (x : Fin n → (Fin d → ℝ)), (∀ j, x j ∈ K) →
      TendstoInDistribution (fun R w => (V R w, fun j => barDivisible w R 1 (x j))) atTop
        (fun ω => (Vlim ω, fun j => Uc ω 1 (x j))) (fun _ : ℝ => law d ν) Q := by
    intro n x _
    apply Generic.Slutsky.tendstoInDistribution_of_tendsto_integral
      (fun R => ((hVm R).prodMk (measurable_pi_lambda _ fun j =>
        measurable_barDivisible R 1 (x j))).aemeasurable)
      ((hVlimm.prodMk (measurable_pi_lambda _ fun j => hUcmeas 1 (x j))).aemeasurable)
    intro F
    let points := Fin.append sp (fun j => ((1 : ℝ), x j))
    have hpoints : ∀ j, 0 < (points j).1 := by
      intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa [points] using hsp i
      · simp [points]
    let proj : (Fin m → ℝ) × (Fin (k + n) → ℝ) →
        ((Fin m → ℝ) × (Fin k → ℝ)) × (Fin n → ℝ) :=
      fun q => ((q.1, fun j => q.2 (Fin.castAdd n j)), fun j => q.2 (Fin.natAdd k j))
    have hproj : Continuous proj :=
      (continuous_fst.prodMk (continuous_pi fun j =>
        (continuous_apply (Fin.castAdd n j)).comp continuous_snd)).prodMk
      (continuous_pi fun j => (continuous_apply (Fin.natAdd k j)).comp continuous_snd)
    have h := hjointFDD m (k + n) φ points hφ hpoints (F.compContinuous ⟨proj, hproj⟩)
    simpa only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
      proj, points, Fin.append_left, Fin.append_right, V, Vlim] using h
  have hres := tendstoInDistribution_barDivisible_block_pairings hd ν hUccont hUcmeas
    hVm hVlimm 1 zero_lt_one K hK hKne hfdd
    (htight_barDivisible_fixedTime hd ν hequicont 1 zero_lt_one K hK) g hg
  have heq : ∀ (f : (Fin d → ℝ) → ℝ) j, (∫ x in K, f x * g j x) = ∫ x, f x * g j x := by
    intro f j
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : g j x = 0 := by by_contra hn; exact hx (hsupp j hn)
    simp [hz]
  simpa only [heq, V, Vlim] using hres

end Parking
end
