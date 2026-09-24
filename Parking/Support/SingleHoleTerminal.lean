import Parking.Support.SingleAddition
import Parking.Support.EscapePotential

noncomputable section
namespace Parking
open LatticeProb
variable {d : ℕ}

/-- Away from the unique discrepancy label, adding one particle leaves hole counts unchanged. -/
theorem singleAddition_holes_eq_off_label (η : Site d → ℤ) (v x : Site d)
    (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (t : ℕ)
    (hx : (discrepancyState (singleAdditionPair η v) ρ σ t).pos (v, 0) ≠ x) :
    (matchedState (addParticle v η) ρ σ t).holes x = (matchedState η ρ σ t).holes x := by
  have he : discrepancyAtSign (singleAdditionPair η v)
      (discrepancyState (singleAdditionPair η v) ρ σ t) t x true = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hmem := (mem_discrepancyAt_iff _ _ _ _ _ _).mp (Finset.mem_filter.mp hq).1
    have hqv := singleAddition_active_label η v ρ σ t q hmem.1
    subst q
    exact hx hmem.2
  have h := discrepancyBalance (singleAdditionPair η v) ρ σ t x
  rw [he, singleAddition_negative_empty, Finset.card_empty, Nat.cast_zero] at h
  have hc0 : coupledConf false (singleAdditionPair η v) = η := rfl
  have hc1 : coupledConf true (singleAdditionPair η v) = addParticle v η := rfl
  rw [hc0, hc1] at h
  have hm := singleAddition_counts_mono η v ρ σ t x
  omega

/-- The base hole count times the discrepancy's escape probability is bounded by the augmented hole count. -/
theorem singleAddition_hole_escape_terminal (hd : 3 ≤ d) (η : Site d → ℤ) (v x : Site d)
    (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (T : ℕ) :
    ((matchedState η ρ σ T).holes x : ℝ) *
        escapePotential d x ((discrepancyState (singleAdditionPair η v) ρ σ T).pos (v, 0)) ≤
      ((matchedState (addParticle v η) ρ σ T).holes x : ℝ) := by
  by_cases hx : (discrepancyState (singleAdditionPair η v) ρ σ T).pos (v, 0) = x
  · rw [hx, escapePotential_self hd, mul_zero]
    exact Nat.cast_nonneg _
  · rw [singleAddition_holes_eq_off_label η v x ρ σ T hx]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) (escapePotential_bounds hd x _).2
end Parking
