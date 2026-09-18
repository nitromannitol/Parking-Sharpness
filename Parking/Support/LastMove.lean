/-
The exact effect of changing one particle direction in the final relevant round.
-/
import Parking.Support.Matched
import Parking.Support.RangeLower

noncomputable section
namespace Parking
open LatticeProb
variable {d : ℕ}

/-- Changing one last-round move into a hole-free site adds one terminal departure there. -/
theorem pOdometer_last_move (D : PDriver d) (t : ℕ) (p : Label d) (x : Site d)
    (a b : Fin d × Bool) (hp : (pState D t).active p = true)
    (ha : (pState D t).pos p + stepVec a = x)
    (hb : (pState D t).pos p + stepVec b ≠ x)
    (hh : pHoleCount D t x = 0) :
    pOdometer ⟨D.eta, Function.update D.move (p, t) a, D.rank⟩ (t + 2) x =
      pOdometer ⟨D.eta, Function.update D.move (p, t) b, D.rank⟩ (t + 2) x + 1 := by
  classical
  let E (c : Fin d × Bool) : PDriver d := ⟨D.eta, Function.update D.move (p, t) c, D.rank⟩
  have hS (c : Fin d × Bool) : pState (E c) t = pState D t := by
    apply pState_congr_moves
    intro s hs q
    exact Function.update_of_ne (show (q, s) ≠ (p, t) by
      intro h; have := congrArg Prod.snd h; omega) _ _
  have hn (c : Fin d × Bool) (q : Label d) (hq : q ≠ p) :
      pNextPos (E c) (pState (E c) t) t q = pNextPos D (pState D t) t q := by
    rw [hS]
    simp [pNextPos, E, Function.update_of_ne (show (q, t) ≠ (p, t) by simpa using hq)]
  have hnp (c : Fin d × Bool) :
      pNextPos (E c) (pState (E c) t) t p = (pState D t).pos p + stepVec c := by
    rw [hS]
    simp [pNextPos, hp, E]
  have hmem : p ∈ pArrivalsAt (E a) (pState (E a) t) t x := by
    rw [mem_pArrivalsAt_iff, hS]
    exact ⟨hp, by simpa only [hS] using (hnp a).trans ha⟩
  have hnot : p ∉ pArrivalsAt (E b) (pState (E b) t) t x := by
    rw [mem_pArrivalsAt_iff]
    exact fun h => hb ((hnp b).symm.trans h.2)
  have harr : pArrivalsAt (E a) (pState (E a) t) t x =
      insert p (pArrivalsAt (E b) (pState (E b) t) t x) := by
    ext q
    by_cases hq : q = p
    · subst q; simp [hmem]
    · rw [Finset.mem_insert, or_iff_right hq, mem_pArrivalsAt_iff, mem_pArrivalsAt_iff,
        hn a q hq, hn b q hq, hS a, hS b]
  have hdep : pOdometer (E a) (t + 1) x = pOdometer (E b) (t + 1) x := by
    change (pState (E a) t).departures x + (pActiveAt (E a) (pState (E a) t) t x).card =
      (pState (E b) t).departures x + (pActiveAt (E b) (pState (E b) t) t x).card
    rw [hS a, hS b]
    rfl
  have hhole (c : Fin d × Bool) : pHoleCount (E c) t x = 0 := by
    simpa only [pHoleCount, hS] using hh
  change pOdometer (E a) (t + 1) x + pActiveCount (E a) (t + 1) x =
    (pOdometer (E b) (t + 1) x + pActiveCount (E b) (t + 1) x) + 1
  rw [hdep, pActiveCount_succ (labelOrder d), pActiveCount_succ (labelOrder d),
    hhole a, hhole b, Nat.sub_zero, Nat.sub_zero, harr, Finset.card_insert_of_notMem hnot]
  omega
end Parking
