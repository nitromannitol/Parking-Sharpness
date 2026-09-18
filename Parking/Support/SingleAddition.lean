/-
A single added particle produces at most one persistent positive discrepancy.
-/
import Parking.Support.DiscrepancyBalance
import Parking.Support.DiscrepancyFresh

noncomputable section
namespace Parking
open LatticeProb
variable {d : ℕ}

/-- A pair of initial fields differing by one added particle. -/
def singleAdditionPair (η : Site d → ℤ) (v : Site d) : Site d → ℤ × ℤ :=
  fun y => (η y, addParticle v η y)

theorem singleAddition_discrepancyConf (η : Site d → ℤ) (v y : Site d) :
    discrepancyConf (singleAdditionPair η v) y = if y = v then 1 else 0 := by
  classical
  simp only [discrepancyConf, singleAdditionPair, addParticle]
  split <;> simp_all

/-- There can be only one live discrepancy label when one particle was added. -/
theorem singleAddition_active_label (η : Site d → ℤ) (v : Site d)
    (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (t : ℕ) (q : Label d)
    (hq : (discrepancyState (singleAdditionPair η v) ρ σ t).active q = true) : q = (v, 0) := by
  have h := discrepancyState_active_le (singleAdditionPair η v) ρ σ q t hq
  change decide (q.2 < (discrepancyConf (singleAdditionPair η v) q.1).toNat) = true at h
  rw [singleAddition_discrepancyConf] at h
  have hv : q.1 = v := by
    by_contra hv
    simp [hv] at h
  simp only [hv, decide_eq_true_eq] at h
  exact Prod.ext hv (by omega)

theorem singleAddition_sign (η : Site d → ℤ) (v : Site d) :
    discrepancySign (singleAdditionPair η v) (v, 0) = true := by
  simp [discrepancySign, singleAdditionPair, addParticle]

/-- No negative discrepancy label is present after adding a particle. -/
theorem singleAddition_negative_empty (η : Site d → ℤ) (v : Site d)
    (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (t : ℕ) (x : Site d) :
    discrepancyAtSign (singleAdditionPair η v) (discrepancyState (singleAdditionPair η v) ρ σ t)
      t x false = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  obtain ⟨hmem, hsign⟩ := Finset.mem_filter.mp hq
  have hact := (mem_discrepancyAt_iff _ _ _ _ _ _).mp hmem |>.1
  have hqv := singleAddition_active_label η v ρ σ t q hact
  subst q
  rw [singleAddition_sign] at hsign
  exact Bool.noConfusion hsign

/-- The common-table coupling is monotone in its active and hole counts under one addition. -/
theorem singleAddition_counts_mono (η : Site d → ℤ) (v : Site d)
    (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (t : ℕ) (x : Site d) :
    matchedCount η ρ σ t x ≤ matchedCount (addParticle v η) ρ σ t x ∧
      (matchedState (addParticle v η) ρ σ t).holes x ≤ (matchedState η ρ σ t).holes x := by
  have hbal := discrepancyBalance (singleAdditionPair η v) ρ σ t x
  rw [singleAddition_negative_empty, Finset.card_empty, Nat.cast_zero, sub_zero] at hbal
  have h0 := matchedCount_eq_zero_or_holes_eq_zero η ρ σ t x
  have h1 := matchedCount_eq_zero_or_holes_eq_zero (addParticle v η) ρ σ t x
  have he0 : coupledConf false (singleAdditionPair η v) = η := rfl
  have he1 : coupledConf true (singleAdditionPair η v) = addParticle v η := rfl
  rw [he0, he1] at hbal
  omega
end Parking
