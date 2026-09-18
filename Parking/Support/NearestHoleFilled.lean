/-
Support lemma for `thm:nearest` (`parking.tex:1825-1827`): if the particle
odometer at a site is positive by round `t`, then a particle has left the site,
so every hole there has been filled and `H_t(x) = 0`.
-/
import Parking.Support.NoBoth

open MeasureTheory LatticeProb

noncomputable section
namespace Parking

/-- `parking.tex:1825-1827`: a positive particle odometer at `x` by round `t`
means a particle has left `x`, so every hole there has been filled. -/
theorem H_eq_zero_of_U_pos {d : ℕ} (ω : Parking.Data d)
    (t : ℕ) (x : Site d) (h : 0 < Parking.U ω t x) : Parking.H ω t x = 0 := by
  have hD : 0 < LatticeProb.particleOdometer (Parking.toDriver ω) t x := h
  have hsum : ∃ s : ℕ, s < t ∧ 0 < LatticeProb.activeCount (Parking.toDriver ω) s x := by
    induction t with
    | zero =>
      have h0 : LatticeProb.particleOdometer (Parking.toDriver ω) 0 x = 0 := rfl
      omega
    | succ t ih =>
      rw [LatticeProb.particleOdometer_succ] at hD
      rcases Nat.eq_zero_or_pos (LatticeProb.activeCount (Parking.toDriver ω) t x) with h0 | hpos
      · rw [h0, Nat.add_zero] at hD
        obtain ⟨s, hs, hpos'⟩ := ih hD (by omega)
        exact ⟨s, Nat.lt_succ_of_lt hs, hpos'⟩
      · exact ⟨t, Nat.lt_succ_self t, hpos⟩
  obtain ⟨s, hst, hpos⟩ := hsum
  have h0 : LatticeProb.holeCount (Parking.toDriver ω) s x = 0 :=
    LatticeProb.holeCount_eq_zero_of_activeCount_pos s x hpos
  have hanti : LatticeProb.holeCount (Parking.toDriver ω) t x
      ≤ LatticeProb.holeCount (Parking.toDriver ω) s x :=
    LatticeProb.holeCount_antitone _ x (Nat.le_of_lt hst)
  have hrw : Parking.H ω t x = LatticeProb.holeCount (Parking.toDriver ω) t x := rfl
  omega

end Parking
end
