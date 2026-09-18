/-
The marginal law of the common-table particle construction. With the initial
configuration and priorities fixed, the received directions are independent.
Integrating the fixed-parameter identity gives the joint driving-data law.
-/
import Parking.Support.Matched
import Parking.Support.LayerLaw
import LatticeProb.Prob.Blocks

noncomputable section

open MeasureTheory LatticeProb

variable {d : ℕ}

/-- With the initial configuration and all priorities fixed, the directions
received by the particles still have their independent product law. -/
theorem Parking.map_matchedMoveLayers (hd : 1 ≤ d) (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) :
    (Parking.roundNoiseLaw d).map
        (fun σ t p => Parking.matchedMoves η ρ σ (p, t)) =
      Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : Label d => Parking.stepLaw d := by
  classical
  haveI := Parking.stepLaw_isProbability hd
  let i₀ : Fin d := ⟨0, hd⟩
  apply Parking.map_layers
  · exact measurable_pi_lambda _ fun t => measurable_pi_lambda _ fun p =>
      (measurable_pi_apply (p, t)).comp
        (Parking.measurable_matchedMoves i₀ (fun _ => η) (fun _ => ρ) id
          measurable_const measurable_const measurable_id)
  · intro σ n k v hkn
    funext p
    unfold Parking.matchedMoves
    rw [Parking.matchedState_update η ρ σ n k v (by omega)]
    rw [Function.update_of_ne (by omega)]
  · intro n σ
    have heq : (fun v p => Parking.matchedMoves η ρ (Function.update σ n v) (p, n)) =
        fun v p => v (Parking.matchSlot η ρ (Parking.matchedState η ρ σ n) n p) := by
      funext v p
      unfold Parking.matchedMoves
      rw [Parking.matchedState_update η ρ σ n n v le_rfl,
        Function.update_self]
    rw [heq]
    exact LatticeProb.infinitePi_map_comp' (Parking.stepLaw d) _
      (Parking.matchSlot_injective η ρ _ n)

/-- The same law with the particle-time indexing used by the particle driver. -/
theorem Parking.map_matchedMoves (hd : 1 ≤ d) (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) :
    (Parking.roundNoiseLaw d).map (Parking.matchedMoves η ρ) =
      Parking.moveLaw d := by
  haveI := Parking.stepLaw_isProbability hd
  let F : Parking.RoundNoise d → ℕ → Label d → Fin d × Bool :=
    fun σ t p => Parking.matchedMoves η ρ σ (p, t)
  let C := (MeasurableEquiv.curry ℕ (Label d) (Fin d × Bool)).symm
  let B : (ℕ × Label d → Fin d × Bool) → Label d × ℕ → Fin d × Bool :=
    fun m q => m q.swap
  have hF : Measurable F := by
    refine measurable_pi_lambda _ fun t => measurable_pi_lambda _ fun p => ?_
    exact (measurable_pi_apply (p, t)).comp
      (Parking.measurable_matchedMoves ⟨0, hd⟩ (fun _ => η) (fun _ => ρ) id
        measurable_const measurable_const measurable_id)
  have hB : Measurable B := measurable_pi_lambda _ fun q => measurable_pi_apply q.swap
  have heq : Parking.matchedMoves η ρ = (B ∘ C) ∘ F := rfl
  rw [heq, ← Measure.map_map (hB.comp C.measurable) hF,
    Parking.map_matchedMoveLayers hd η ρ,
    ← Measure.map_map hB C.measurable,
    Measure.infinitePi_map_curry_symm]
  exact LatticeProb.infinitePi_map_comp' (Parking.stepLaw d) Prod.swap Prod.swap_injective

/-- Joint law of the configuration, priorities and received directions. -/
theorem Parking.map_matchedData (hd : 1 ≤ d) (μ : Measure (Site d → ℤ))
    [IsProbabilityMeasure μ] :
    ((μ.prod (LatticeProb.rankLaw d)).prod (Parking.roundNoiseLaw d)).map
        (fun ω => ((ω.1.1,
          Parking.matchedMoves ω.1.1 ω.1.2 ω.2, ω.1.2) : Parking.PData d)) =
      μ.prod ((Parking.moveLaw d).prod (LatticeProb.rankLaw d)) := by
  haveI := Parking.stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (Parking.moveLaw d) := by
    unfold Parking.moveLaw
    infer_instance
  haveI := Parking.roundNoiseLaw_isProbability hd
  haveI := LatticeProb.rankLaw_isProbability d
  have hm : Measurable fun ω : ((Site d → ℤ) × (Label d × ℕ → ℝ)) ×
      Parking.RoundNoise d => Parking.matchedMoves ω.1.1 ω.1.2 ω.2 :=
    Parking.measurable_matchedMoves ⟨0, hd⟩ _ _ _
      (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst) measurable_snd
  have hlaw := LatticeProb.map_prod_pair_of_forall_map
    (μ.prod (LatticeProb.rankLaw d)) (Parking.roundNoiseLaw d)
    (F := fun a σ => Parking.matchedMoves a.1 a.2 σ) hm
    (fun a => Parking.map_matchedMoves hd a.1 a.2)
  let T : (((Site d → ℤ) × (Label d × ℕ → ℝ)) ×
      (Label d × ℕ → Fin d × Bool)) → Parking.PData d :=
    fun ω => (ω.1.1, ω.2, ω.1.2)
  have hT : Measurable T :=
    (measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  change _ = _
  have heq : (fun ω : ((Site d → ℤ) × (Label d × ℕ → ℝ)) × Parking.RoundNoise d =>
      ((ω.1.1, Parking.matchedMoves ω.1.1 ω.1.2 ω.2, ω.1.2) : Parking.PData d)) =
      T ∘ (fun ω => (ω.1, Parking.matchedMoves ω.1.1 ω.1.2 ω.2)) := rfl
  rw [heq, ← Measure.map_map hT (measurable_fst.prodMk hm), hlaw]
  exact Parking.map_reshuffle μ (LatticeProb.rankLaw d) (Parking.moveLaw d)

end
