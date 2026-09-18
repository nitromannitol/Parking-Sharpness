import Parking.Support.SingleAddition

noncomputable section
namespace Parking
open LatticeProb
variable {d : ℕ}

/-- A moving positive discrepancy uses an instruction unused by the smaller process. -/
theorem singleAddition_index_unused (η : Site d → ℤ) (v : Site d)
    (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (t : ℕ)
    (hm : discrepancyDoesMove (singleAdditionPair η v) ρ σ t (v, 0) = true) :
    ∃ j : ℕ, matchedCount η ρ σ t ((discrepancyState (singleAdditionPair η v) ρ σ t).pos (v, 0)) ≤ j ∧
      discrepancyIndex (singleAdditionPair η v) ρ σ t (v, 0) =
        Sum.inl ((discrepancyState (singleAdditionPair η v) ρ σ t).pos (v, 0), j) := by
  classical
  let c := singleAdditionPair η v
  let S := discrepancyState c ρ σ t
  let x := S.pos (v, 0)
  let j := matchedCount η ρ σ t x + rankIn (discrepancyAt c S t x) (matchKey ρ 0) (v, 0)
  refine ⟨j, Nat.le_add_right _ _, ?_⟩
  have hm' := of_decide_eq_true hm
  unfold discrepancyIndex discrepancySlot
  rw [if_pos hm']
  have hc0 : coupledConf false c = η := rfl
  have hc1 : coupledConf true c = addParticle v η := rfl
  change Sum.inl (x, min (matchedCount (coupledConf false c) ρ σ t x)
    (matchedCount (coupledConf true c) ρ σ t x) + rankIn (discrepancyAt c S t x) (matchKey ρ 0) (v, 0)) = _
  rw [hc0, hc1, min_eq_left (singleAddition_counts_mono η v ρ σ t x).1]
end Parking
