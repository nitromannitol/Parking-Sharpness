/- Joint space-time functionals with the scenery retained on the same limit space. -/
import Parking.Support.SpatialSpaceTimeMeasurable
import Parking.Support.SpatWSceneryFdd
import Parking.Support.NearestBallEvent
import Parking.Generic.FddNiceFunctional
import Parking.Generic.Slutsky

open MeasureTheory ProbabilityTheory Filter Topology
open Parking.Generic.BoundedFunctionalLift

noncomputable section
namespace Parking
variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {W : ((Fin d → ℝ) → ℝ) → Ω → ℝ} {Uc : Ω → ℝ → (Fin d → ℝ) → ℝ}

/-- Joint convergence for a bounded functional of the scenery and the entire space-time
field on a compact set. Its pathwise Lipschitz bound is needed only for measurable paths
bounded on that compact set. -/
theorem tendsto_integral_scenePair_spaceTime_functional
    (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure (law d ν)]
    (hUccont : ∀ ω, Continuous fun q : ℝ × (Fin d → ℝ) => Uc ω q.1 q.2)
    (hUcmeas : ∀ s x, Measurable fun ω => Uc ω s x)
    (hWmeas : ∀ φ, IsTestFun φ → Measurable (W φ))
    (hjointFDD : ∀ (m p' : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ)
      (sp : Fin p' → ℝ × (Fin d → ℝ)),
      (∀ i, IsTestFun (φ i)) → (∀ j, 0 < (sp j).1) →
      ∀ F : BoundedContinuousFunction ((Fin m → ℝ) × (Fin p' → ℝ)) ℝ,
        Tendsto (fun R : ℝ => ∫ w, F (fun i => scenePair w R (φ i),
              fun j => barDivisible w R (sp j).1 (sp j).2) ∂law d ν) atTop
          (𝓝 (∫ ω, F (fun i => W (φ i) ω, fun j => Uc ω (sp j).1 (sp j).2) ∂Q)))
    (hequicont : ∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K →
      (∀ p ∈ K, 0 < p.1) → ∀ ε : ℝ, 0 < ε → ∀ ε' : ℝ, 0 < ε' →
        ∃ δ : ℝ, 0 < δ ∧ ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
          ((law d ν) {w | ε < ⨆ p ∈ K, ⨆ q ∈ K, ⨆ _ : dist p q ≤ δ,
            |barDivisible w R p.1 p.2 - barDivisible w R q.1 q.2|}).toReal ≤ ε')
    {m : ℕ} (φ : Fin m → (Fin d → ℝ) → ℝ) (hφ : ∀ i, IsTestFun (φ i))
    {K : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K) (hKt : ∀ p ∈ K, 0 < p.1)
    {Φ : (Fin m → ℝ) → ((ℝ × (Fin d → ℝ)) → ℝ) → ℝ}
    (hmeas : ∀ᶠ R : ℝ in atTop, Measurable fun w =>
      Φ (fun i => scenePair w R (φ i)) (fun p => barDivisible w R p.1 p.2))
    {M C D : ℝ} (hΦb : ∀ b v, |Φ b v| ≤ M) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hpath : ∀ b v w, Measurable v → Measurable w →
      (∃ A : ℝ, ∀ p ∈ K, |v p| ≤ A) → (∃ A : ℝ, ∀ p ∈ K, |w p| ≤ A) →
      |Φ b v - Φ b w| ≤ C * supDistOn K v w)
    (hblock : ∀ a b v, Measurable v → (∃ A : ℝ, ∀ p ∈ K, |v p| ≤ A) →
      |Φ a v - Φ b v| ≤ D * dist a b) :
    Tendsto (fun R : ℝ => ∫ w,
      Φ (fun i => scenePair w R (φ i)) (fun p => barDivisible w R p.1 p.2) ∂law d ν) atTop
      (𝓝 (∫ ω, Φ (fun i => W (φ i) ω) (fun p => Uc ω p.1 p.2) ∂Q)) := by
  let Nice : ((ℝ × (Fin d → ℝ)) → ℝ) → Prop := fun v =>
    Measurable v ∧ ∃ A : ℝ, ∀ p ∈ K, |v p| ≤ A
  have hVm : ∀ R : ℝ, Measurable (fun w : Data d => fun i => scenePair w R (φ i)) :=
    fun R => measurable_pi_lambda _ fun _ => measurable_scenePair_any_R R
  have hWm : Measurable (fun ω => fun i => W (φ i) ω) :=
    measurable_pi_lambda _ fun i => hWmeas (φ i) (hφ i)
  have hn : ∀ᶠ R : ℝ in atTop, ∀ w : Data d,
      Nice (fun p => barDivisible w R p.1 p.2) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR w
    exact ⟨measurable_spaceTime_barDivisible w R,
      exists_bound_spaceTime_barDivisible hd w hR hK⟩
  have hlimnice : ∀ ω, Nice (fun p => Uc ω p.1 p.2) := by
    intro ω
    refine ⟨(hUccont ω).measurable, ?_⟩
    obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn (hUccont ω).continuousOn
    exact ⟨A, fun p hp => hA p hp⟩
  have hfdd : ∀ (n : ℕ) (sp : Fin n → ℝ × (Fin d → ℝ)), (∀ k, sp k ∈ K) →
      TendstoInDistribution (fun R w => (fun i => scenePair w R (φ i),
        fun j => barDivisible w R (sp j).1 (sp j).2)) atTop
      (fun ω => (fun i => W (φ i) ω, fun j => Uc ω (sp j).1 (sp j).2))
      (fun _ : ℝ => law d ν) Q := by
    intro n sp hsp
    apply Generic.Slutsky.tendstoInDistribution_of_tendsto_integral
      (fun R => ((hVm R).prodMk (measurable_pi_lambda _ fun j =>
        measurable_barDivisible R (sp j).1 (sp j).2)).aemeasurable)
      ((hWm.prodMk (measurable_pi_lambda _ fun j =>
        hUcmeas (sp j).1 (sp j).2)).aemeasurable)
    exact hjointFDD m n φ sp hφ (fun j => hKt _ (hsp j))
  exact Generic.FddNiceFunctional.tendsto_integral hK
    (Nice := Nice) (G0 := fun _ => 0) ⟨measurable_const, 0, by simp⟩ hn hlimnice
    (Eventually.of_forall hVm) hWm
    (Eventually.of_forall fun R p => measurable_barDivisible R p.1 p.2)
    (fun p => hUcmeas p.1 p.2) (fun ω => (hUccont ω).continuousOn)
    hmeas hfdd (htight_of_spatial_tightness hd ν K hK (hequicont K hK hKt))
    hΦb hC hD (fun b v w hv hw => hpath b v w hv.1 hw.1 hv.2 hw.2)
    (fun a b v hv => hblock a b v hv.1 hv.2)

end Parking
