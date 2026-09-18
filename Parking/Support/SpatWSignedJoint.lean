/- The joint signed-density limit, with the continuum witnesses fixed. -/
import Parking.Support.SpatWJointPairings
import Parking.Support.SpatWSignedPairingResidual
import Parking.Support.NearestEvents

open MeasureTheory ProbabilityTheory LatticeProb Filter Topology

noncomputable section
namespace Parking

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {W : ((Fin d → ℝ) → ℝ) → Ω → ℝ} {Uc : Ω → ℝ → (Fin d → ℝ) → ℝ}

/-- The signed-density limit holds jointly with the scenery and both odometers. -/
theorem tendsto_spatial_signed_joint
    (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : External.SandpileGrowth) (hBernstein : External.Bernstein)
    (hConcentration : External.UConcentration) (hGreenNorms : External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν)
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
    (m k p : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ) (χ : Fin p → (Fin d → ℝ) → ℝ)
    (sp : Fin k → ℝ × (Fin d → ℝ)) (hφ : ∀ i, IsTestFun (φ i))
    (hχ : ∀ j, IsTestFun (χ j)) (hsp : ∀ j, 0 < (sp j).1)
    (F : BoundedContinuousFunction
      ((Fin m → ℝ) × (Fin k → ℝ) × (Fin k → ℝ) × (Fin p → ℝ)) ℝ) :
    Tendsto (fun R : ℝ => ∫ w, F (fun i => scenePair w R (φ i),
      fun j => barDivisible w R (sp j).1 (sp j).2,
      fun j => barOdometer w R (sp j).1 (sp j).2,
      fun l => signedPair w R (χ l)) ∂law d ν) atTop
      (𝓝 (∫ ω, F (fun i => W (φ i) ω,
        fun j => Uc ω (sp j).1 (sp j).2,
        fun j => Uc ω (sp j).1 (sp j).2,
        fun l => W (χ l) ω + ∫ x, Uc ω 1 x * contOp d (χ l) x) ∂Q)) := by
  haveI := hν.prob
  haveI := law_isProb hd ν
  let g := fun l => contOp d (χ l)
  let K : Set (Fin d → ℝ) := {0} ∪ ⋃ l, tsupport (g l)
  have hK : IsCompact K := isCompact_singleton.union
    (isCompact_iUnion fun l => hasCompactSupport_contOp (hχ l))
  have hKne : K.Nonempty := ⟨0, Or.inl rfl⟩
  have hsupp : ∀ l, Function.support (g l) ⊆ K := fun l x hx =>
    Or.inr (Set.mem_iUnion.mpr ⟨l, subset_tsupport (g l) hx⟩)
  let tests := Fin.append φ χ
  have htests : ∀ i, IsTestFun (tests i) := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [tests] using hφ j
    · simpa [tests] using hχ j
  have hbase := tendstoInDistribution_scenePair_barDivisible_pairings hd ν hUccont hUcmeas
    hWmeas hjointFDD hequicont tests htests sp hsp g
    (fun l => continuous_contOp (hχ l)) K hK hKne hsupp
  have hpairmeas : ∀ R l, Measurable fun w : Data d => ∫ x, barDivisible w R 1 x * g l x := by
    intro R l
    have h := measurable_integral_barDivisible_mul R 1 K hK (g l) (continuous_contOp (hχ l))
    have heq : ∀ w : Data d, (∫ x in K, barDivisible w R 1 x * g l x) =
        ∫ x, barDivisible w R 1 x * g l x := by
      intro w
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : g l x = 0 := by by_contra hn; exact hx (hsupp l hn)
      simp [hz]
    simpa only [heq] using h
  let Y := fun R (w : Data d) => Fin.append
    (fun j : Fin k => barOdometer w R (sp j).1 (sp j).2 - barDivisible w R (sp j).1 (sp j).2)
    (fun l : Fin p => signedPair w R (χ l) - scenePair w R (χ l) -
      ∫ x, barDivisible w R 1 x * g l x)
  have hYm : ∀ R, Measurable (Y R) := by
    intro R
    apply measurable_pi_lambda
    intro i
    refine Fin.addCases (fun j => ?_) (fun l => ?_) i
    · simp only [Y, Fin.append_left]
      exact
        (measurable_barOdometer R (sp j).1 (sp j).2).sub
          (measurable_barDivisible R (sp j).1 (sp j).2)
    · simp only [Y, Fin.append_right]
      exact
        ((measurable_signedPair R (χ l)).sub (measurable_scenePair_any_R R)).sub (hpairmeas R l)
  have hYzero : ∀ a : ℝ, 0 < a →
      Tendsto (fun R => ((law d ν) {w | a < ‖Y R w‖}).toReal) atTop (𝓝 0) := by
    apply Generic.Slutsky.tendsto_zero_pi_of_forall_tendsto_zero
    intro i
    refine Fin.addCases (fun j => ?_) (fun l => ?_) i
    · intro a ha
      have h := exists_spatial_vanishing_distance hd hd3 hGrowth hBernstein
        hConcentration hGreenNorms ν hν {sp j} isCompact_singleton
        (fun z hz => by rw [Set.mem_singleton_iff] at hz; rw [hz]; exact hsp j) a ha
      have heq : ∀ R w, (⨆ z ∈ ({sp j} : Set (ℝ × (Fin d → ℝ))),
          |barOdometer w R z.1 z.2 - barDivisible w R z.1 z.2|) =
          |barOdometer w R (sp j).1 (sp j).2 - barDivisible w R (sp j).1 (sp j).2| := by
        intro R w
        apply le_antisymm
        · exact Real.iSup_le (fun z => Real.iSup_le (fun hz => by
            rw [Set.mem_singleton_iff] at hz; rw [hz]) (abs_nonneg _)) (abs_nonneg _)
        · exact le_biSup_of_bound {sp j}
            (fun z => |barOdometer w R z.1 z.2 - barDivisible w R z.1 z.2|)
            (abs_nonneg _) (fun z hz => by rw [Set.mem_singleton_iff] at hz; rw [hz]) rfl
      simpa only [heq, Y, Fin.append_left] using h
    · intro a ha
      simpa only [Y, Fin.append_right, g] using
        tendsto_signedPair_sub_scenePair_sub_pairing_zero hd hd3 hGrowth hBernstein
          hConcentration hGreenNorms ν hν (hχ l) ha
  have hprod := hbase.prodMk_of_tendstoInMeasure_const _ Y _
    (Generic.Slutsky.tendstoInMeasure_zero_of_forall_lt hYzero) (fun R => (hYm R).aemeasurable)
  let H : ((((Fin (m + p) → ℝ) × (Fin k → ℝ)) × (Fin p → ℝ)) × (Fin (k + p) → ℝ)) →
      (Fin m → ℝ) × (Fin k → ℝ) × (Fin k → ℝ) × (Fin p → ℝ) := fun q =>
    (fun i => q.1.1.1 (Fin.castAdd p i), q.1.1.2,
      fun j => q.1.1.2 j + q.2 (Fin.castAdd p j),
      fun l => q.1.1.1 (Fin.natAdd m l) + q.1.2 l + q.2 (Fin.natAdd k l))
  have hH : Continuous H := by
    apply Continuous.prodMk
    · exact continuous_pi fun i => (continuous_apply (Fin.castAdd p i)).comp continuous_fst.fst.fst
    apply Continuous.prodMk continuous_fst.fst.snd
    apply Continuous.prodMk
    · exact continuous_pi fun j => ((continuous_apply j).comp continuous_fst.fst.snd).add
        ((continuous_apply (Fin.castAdd p j)).comp continuous_snd)
    · exact continuous_pi fun l => (((continuous_apply (Fin.natAdd m l)).comp continuous_fst.fst.fst).add
        ((continuous_apply l).comp continuous_fst.snd)).add ((continuous_apply (Fin.natAdd k l)).comp continuous_snd)
  have h := Generic.CramerWold.tendsto_integral_of_tendstoInDistribution (hprod.continuous_comp hH) F
  have heqL : ∀ R w, H (((fun i => scenePair w R (tests i),
      fun j => barDivisible w R (sp j).1 (sp j).2),
      fun l => ∫ x, barDivisible w R 1 x * g l x), Y R w) =
      (fun i => scenePair w R (φ i), fun j => barDivisible w R (sp j).1 (sp j).2,
       fun j => barOdometer w R (sp j).1 (sp j).2, fun l => signedPair w R (χ l)) := by
    intro R w
    simp only [H, Y, tests, Fin.append_left, Fin.append_right]
    congr 1
    ext j <;> dsimp <;> ring
  simp only [Function.comp_apply] at h
  simp_rw [heqL] at h
  simpa only [H, tests, Fin.append_left, Fin.append_right,
    Pi.zero_apply, add_zero, g] using h

end Parking
end
