/-
The label revealed by one step of the particle filtration.

Step 2 of `lem:product` (`parking.tex:2367-2394`) reveals the particles of a
site one at a time, and the comparison functional it uses at step `i` is the
value after THAT particle is deleted.  For the comparison to be legitimate the
step must reveal exactly one label, which is what the canonical enumeration of a
finite set of labels gives: stage `i + 1` of the filtration reveals the labels of
stage `i` together with the `i`-th label of the enumeration, so two consecutive
stages of the splicing agree at every label but that one.
-/
import Parking.Support.ParticleFiltration

noncomputable section

namespace Parking

/-- The `i`-th label of a finite set of labels in its canonical enumeration. -/
def enumLabel {α : Type*} [Inhabited α] (s : Finset α) (i : ℕ) : α :=
  if h : i < s.card then ((s.equivFin.symm ⟨i, h⟩ : {x // x ∈ s}) : α) else default

/-- **One step of the filtration reveals one label.** -/
theorem mem_prefixSet_succ {α : Type*} [Inhabited α] (s : Finset α) {i : ℕ} (hi : i < s.card)
    (p : α) :
    p ∈ prefixSet s (i + 1) ↔ p ∈ prefixSet s i ∨ p = enumLabel s i := by
  constructor
  · rintro ⟨h, hlt⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h1 | h1
    · exact Or.inl ⟨h, h1⟩
    · refine Or.inr ?_
      rw [enumLabel, dif_pos hi]
      have h2 : s.equivFin ⟨p, h⟩ = ⟨i, hi⟩ := Fin.ext h1
      rw [← h2, Equiv.symm_apply_apply]
  · rintro (⟨h, hlt⟩ | rfl)
    · exact ⟨h, Nat.lt_succ_of_lt hlt⟩
    · rw [enumLabel, dif_pos hi]
      refine ⟨(s.equivFin.symm ⟨i, hi⟩).2, ?_⟩
      have h3 : (⟨((s.equivFin.symm ⟨i, hi⟩ : {x // x ∈ s}) : α),
          (s.equivFin.symm ⟨i, hi⟩).2⟩ : {x // x ∈ s}) = s.equivFin.symm ⟨i, hi⟩ := rfl
      rw [h3, Equiv.apply_symm_apply]
      exact Nat.lt_succ_self i

/-- The `i`-th label of the enumeration belongs to the set. -/
theorem enumLabel_mem {α : Type*} [Inhabited α] (s : Finset α) {i : ℕ} (hi : i < s.card) :
    enumLabel s i ∈ s := by
  rw [enumLabel, dif_pos hi]
  exact (s.equivFin.symm ⟨i, hi⟩).2

/-- Two splicings whose label sets agree away from one label agree at every
label but that one. -/
theorem noiseComb_agree_of {d : ℕ} {T T' : Set (Label d)} {p : Label d}
    (hTT' : ∀ r : Label d, r ≠ p → (r ∈ T ↔ r ∈ T')) (ω η : PNoise d)
    {q : Label d × ℕ} (hq : q.1 ≠ p) :
    (noiseComb T ω η).1 q = (noiseComb T' ω η).1 q ∧
      (noiseComb T ω η).2 q = (noiseComb T' ω η).2 q := by
  by_cases h : q.1 ∈ T
  · have h' : q.1 ∈ T' := (hTT' q.1 hq).mp h
    exact ⟨by rw [noiseComb_fst_of_mem h, noiseComb_fst_of_mem h'],
      by rw [noiseComb_snd_of_mem h, noiseComb_snd_of_mem h']⟩
  · have h' : q.1 ∉ T' := fun hc => h ((hTT' q.1 hq).mpr hc)
    exact ⟨by rw [noiseComb_fst_of_notMem h, noiseComb_fst_of_notMem h'],
      by rw [noiseComb_snd_of_notMem h, noiseComb_snd_of_notMem h']⟩

/-- **Two consecutive stages of the particle filtration agree away from the
label the step reveals.** -/
theorem particleSplice_succ_agree {d : ℕ} (N : Finset (Site d)) (a : Site d → ℤ) {i : ℕ}
    (hi : i < (particleLabels N a).card) (ω η : PNoise d) {q : Label d × ℕ}
    (hq : q.1 ≠ enumLabel (particleLabels N a) i) :
    (particleSplice N a (i + 1) ω η).1 q = (particleSplice N a i ω η).1 q ∧
      (particleSplice N a (i + 1) ω η).2 q = (particleSplice N a i ω η).2 q :=
  noiseComb_agree_of
    (fun r hr => by
      rw [mem_prefixSet_succ _ hi]
      exact ⟨fun h => h.elim id fun h' => absurd h' hr, Or.inl⟩)
    ω η hq

end Parking

end
