import Parking.Support.TableDifference

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d K : ℕ}

/-- The increment reads the preceding history and exactly one new entry. -/
theorem tableDiff_reads (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d)
    (e : Fin K ↪ Site d × ℕ) (hK : 0 < K) (n : ℕ) (ω ω' : FlatRoundNoise d)
    (hω : ∀ q ∈ insert (n / K, Sum.inl (e ⟨n % K, Nat.mod_lt n hK⟩))
        (blockReveal (slotEnumeration e) n), ω q = ω' q) :
    tableDiff η ρ T x e hK (n + 1) ω = tableDiff η ρ T x e hK (n + 1) ω' := by
  have hp : ∀ s < n / K, curryRoundNoise ω s = curryRoundNoise ω' s := by
    intro s hs
    funext q
    exact hω (s, q) (Set.mem_insert_of_mem _ (Or.inl hs))
  have hS := matchedState_congr η ρ (curryRoundNoise ω) (curryRoundNoise ω') (n / K) hp
  have hA : matchedCount η ρ (curryRoundNoise ω) (n / K) =
      matchedCount η ρ (curryRoundNoise ω') (n / K) := by
    funext y
    unfold matchedCount
    rw [hS]
  rw [tableDiff_succ, tableDiff_succ, hA, hS]
  apply roundDiff_congr
  intro q hq
  rw [revealPrefix_succ (slotEnumeration e) ⟨n % K, Nat.mod_lt n hK⟩] at hq
  rcases hq with rfl | hq
  · exact hω _ (Set.mem_insert _ _)
  · exact hω _ (Set.mem_insert_of_mem _ (Or.inr ⟨rfl, hq⟩))

/-- The sigma algebra of the chronological reveal history. -/
@[reducible] def tableFiltration (base : FlatRoundNoise d) (e : Fin K ↪ Site d × ℕ) (n : ℕ) :
    MeasurableSpace (FlatRoundNoise d) := productCoordAlg base (blockReveal (slotEnumeration e) n)

theorem tableFiltration_mono (base : FlatRoundNoise d) (e : Fin K ↪ Site d × ℕ) :
    Monotone (tableFiltration base e) := by
  intro m n hmn
  exact productCoordAlg_mono base _ _ (blockReveal_mono (slotEnumeration e) hmn)

theorem tableFiltration_le (base : FlatRoundNoise d) (e : Fin K ↪ Site d × ℕ) (n : ℕ) :
    tableFiltration base e n ≤ (inferInstance : MeasurableSpace (FlatRoundNoise d)) :=
  productCoordAlg_le base _

/-- The chronological reveal increments are adapted to the reveal filtration. -/
theorem measurable_tableDiff_adapted (hd : 1 ≤ d) (base : FlatRoundNoise d)
    (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d)
    (e : Fin K ↪ Site d × ℕ) (hK : 0 < K) (n : ℕ) :
    Measurable[tableFiltration base e n] (tableDiff η ρ T x e hK n) := by
  cases n with
  | zero =>
      change Measurable[tableFiltration base e 0] (fun ω => tableDiff η ρ T x e hK 0 ω)
      simp only [tableDiff_zero]
      exact measurable_const
  | succ n =>
      apply measurable_of_reads_coordinates base (blockReveal (slotEnumeration e) (n + 1)) _
        (measurable_tableDiff hd η ρ T x e hK (n + 1))
      intro ω ω' hω
      apply tableDiff_reads η ρ T x e hK n ω ω'
      intro q hq
      exact hω q (insert_next_subset_blockReveal (slotEnumeration e) hK n hq)
end Parking
