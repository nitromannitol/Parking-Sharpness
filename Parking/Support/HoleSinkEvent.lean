import Parking.Support.HoleNoArrival
import Parking.Support.SinkField

/-!
# The surviving-hole event as an initial atom and a sink no-arrival event

Rewrites the event that a site `v` remains an unmatched hole to time `T`, under the clipped
field `clippedField η`, as the conjunction of the initial atom `clippedField η v = -1` and the
event `noArrivalFlag (sparseSinkField T v η) ρ σ T v = true` that no active site has yet
entered `v`'s priority list under the sparsified field that turns every site but `v` in the
causal box into a sink. The two no-arrival flags agree by
`noArrivalFlag_same_nonpositive_origin`, since `clippedField η` and `sparseSinkField T v η`
agree away from `v` and are both nonpositive at `v`.
-/

noncomputable section
namespace Parking
open LatticeProb
variable {d : ℕ}

/-- The surviving-hole event is the initial negative atom intersected with no entrance to the
sink. -/
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
