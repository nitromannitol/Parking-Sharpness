import Parking.Support.HoleNoArrival
import Parking.Support.SinkField

noncomputable section
namespace Parking
open LatticeProb
variable {d : ℕ}

/-- The surviving-hole event is the initial negative atom intersected with no entrance to the sink. -/
theorem clippedHole_eq_one_iff_sink (η : Site d → ℤ) (v : Site d)
    (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (T : ℕ) :
    (matchedState (clippedField η) ρ σ T).holes v = 1 ↔
      clippedField η v = -1 ∧ noArrivalFlag (sparseSinkField T v η) ρ σ T v = true := by
  have hflags (hv : clippedField η v = -1) :
      noArrivalFlag (clippedField η) ρ σ T v = noArrivalFlag (sparseSinkField T v η) ρ σ T v := by
    apply noArrivalFlag_same_nonpositive_origin _ _ v (by omega)
    · simp only [sparseSinkField, horizonSink, Function.update_self]
      omega
    · intro x hx
      exact (sparseSinkField_eq_of_ne T v η x hx).symm
  constructor
  · intro h
    have hb := matchedHoles_le_initial (clippedField η) ρ σ T v
    have hl : -1 ≤ clippedField η v := (clipSparse_bounds (η v)).1
    have hv : clippedField η v = -1 := by omega
    refine ⟨hv, ?_⟩
    rw [← hflags hv]
    exact (matchedHole_eq_one_iff_noArrival _ v hv ρ σ T).mp h
  · rintro ⟨hv, h⟩
    apply (matchedHole_eq_one_iff_noArrival _ v hv ρ σ T).mpr
    rwa [hflags hv]
end Parking
