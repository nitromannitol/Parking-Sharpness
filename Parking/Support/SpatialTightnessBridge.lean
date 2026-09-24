/- The equicontinuity clause of `prop:spatial-scaling` in the form the
finite-dimensional-to-functional bridge of the library consumes.

The clause bounds the probability that the rescaled divisible odometer oscillates
by more than a tolerance between two points of a compact set at distance at most
the mesh.  The bridge asks instead for the probability of the event that two such
points exist, and that event is contained in the first: on a bounded set the
rescaled field reads finitely many lattice sites, so the oscillation is a genuine
supremum and not the junk value of an unbounded family.
-/
import Parking.Support.Continuum
import Parking.Support.UBound
import Parking.Support.WBound
import LatticeProb.Prob.FddTight

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset Filter Topology

variable {d : ℕ}

/-- A compact set of space-time is contained in a box. -/
theorem exists_radius_of_isCompact (K : Set (ℝ × (Fin d → ℝ))) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, |p.1| ≤ C ∧ ∀ i, |p.2 i| ≤ C := by
  obtain ⟨C, hC⟩ := hK.isBounded.subset_closedBall 0
  refine ⟨max C 0, le_max_right _ _, fun p hp => ?_⟩
  have h := hC hp
  rw [Metric.mem_closedBall, dist_zero_right] at h
  refine ⟨?_, fun i => ?_⟩
  · calc |p.1| = ‖p.1‖ := rfl
      _ ≤ ‖p‖ := le_max_left _ _
      _ ≤ max C 0 := le_trans h (le_max_left _ _)
  · calc |p.2 i| = ‖p.2 i‖ := rfl
      _ ≤ ‖p.2‖ := norm_le_pi_norm _ i
      _ ≤ ‖p‖ := le_max_right _ _
      _ ≤ max C 0 := le_trans h (le_max_left _ _)


theorem abs_barDivisible_le (hd : 1 ≤ d) (w : Data d) {R : ℝ} (hR : 0 ≤ R)
    {C : ℝ} (_hC : 0 ≤ C) {p : ℝ × (Fin d → ℝ)} (hp1 : |p.1| ≤ C) (hp2 : ∀ i, |p.2 i| ≤ C) :
    |barDivisible w R p.1 p.2|
      ≤ R ^ ((d : ℝ) / 2 - 2) * ((⌊C * R ^ 2⌋₊ : ℝ) *
          confBox w 0 ((⌈C * R⌉₊ + 1) + ⌊C * R ^ 2⌋₊)) := by
  set N : ℕ := ⌊C * R ^ 2⌋₊ with hN
  set m : ℕ := ⌈C * R⌉₊ + 1 with hm
  have hpow : (0 : ℝ) ≤ R ^ ((d : ℝ) / 2 - 2) := Real.rpow_nonneg hR _
  have hkN : ⌊p.1 * R ^ 2⌋₊ ≤ N := by
    refine Nat.floor_le_floor ?_
    have : p.1 ≤ C := le_trans (le_abs_self _) hp1
    nlinarith [sq_nonneg R]
  have hmem : latticePoint R p.2 ∈ boxFinset (0 : Site d) m := by
    rw [mem_boxFinset_iff]
    intro i
    have hx : |R * p.2 i| ≤ C * R := by
      rw [abs_mul, abs_of_nonneg hR, mul_comm]
      exact mul_le_mul_of_nonneg_right (hp2 i) hR
    have h1 : (⌊R * p.2 i⌋ : ℝ) ≤ C * R := le_trans (Int.floor_le _) (le_trans (le_abs_self _) hx)
    have h2 : -(C * R) - 1 ≤ (⌊R * p.2 i⌋ : ℝ) := by
      have := Int.sub_one_lt_floor (R * p.2 i)
      have h3 : -(C * R) ≤ R * p.2 i := neg_le_of_abs_le hx
      linarith
    have hcr : (C * R : ℝ) ≤ (⌈C * R⌉₊ : ℝ) := Nat.le_ceil _
    simp only [latticePoint, Pi.zero_apply, sub_zero]
    rw [abs_le]
    constructor
    · have : -((m : ℝ)) ≤ (⌊R * p.2 i⌋ : ℝ) := by push_cast [hm]; linarith
      exact_mod_cast this
    · have : (⌊R * p.2 i⌋ : ℝ) ≤ (m : ℝ) := by push_cast [hm]; linarith
      exact_mod_cast this
  have hu : uOf w ⌊p.1 * R ^ 2⌋₊ (latticePoint R p.2)
      ≤ (N : ℝ) * confBox w 0 (m + N) := by
    refine (uOf_le_confBox hd w _ _).trans ?_
    have h1 : confBox w (latticePoint R p.2) ⌊p.1 * R ^ 2⌋₊
        ≤ confBox w (0 : Site d) (m + N) :=
      (confBox_mono w _ hkN).trans (confBox_le_of_mem w hmem N)
    have h2 : ((⌊p.1 * R ^ 2⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkN
    exact mul_le_mul h2 h1 (confBox_nonneg _ _ _) (Nat.cast_nonneg _)
  rw [barDivisible, abs_of_nonneg (mul_nonneg hpow (uOf_nonneg w _ _))]
  exact mul_le_mul_of_nonneg_left hu hpow


/-- The equicontinuity-in-probability clause of `prop:spatial-scaling` gives the
tightness hypothesis of `LatticeProb.tendsto_integral_of_fdd_of_equicontinuous`
for the rescaled divisible odometer. -/
theorem htight_of_spatial_tightness (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure (law d ν)] (K : Set (ℝ × (Fin d → ℝ))) (hK : IsCompact K)
    (htight : ∀ ε : ℝ, 0 < ε → ∀ ε' : ℝ, 0 < ε' → ∃ δ : ℝ, 0 < δ ∧ ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      ((law d ν) {w | ε < ⨆ p ∈ K, ⨆ q ∈ K, ⨆ _ : dist p q ≤ δ,
        |barDivisible w R p.1 p.2 - barDivisible w R q.1 q.2|}).toReal ≤ ε') :
    ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ R : ℝ in atTop,
      (law d ν) {w | ∃ z ∈ K, ∃ y ∈ K, dist z y < δ ∧
          η < |barDivisible w R z.1 z.2 - barDivisible w R y.1 y.2|}
        ≤ ENNReal.ofReal ε := by
  intro ε η hε hη
  obtain ⟨δ, hδ, R₀, hR⟩ := htight η hη ε hε
  obtain ⟨C, hC, hKC⟩ := exists_radius_of_isCompact K hK
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [eventually_ge_atTop R₀, eventually_ge_atTop (0 : ℝ)] with R hRge hR0
  have hsub : {w : Data d | ∃ z ∈ K, ∃ y ∈ K, dist z y < δ ∧
      η < |barDivisible w R z.1 z.2 - barDivisible w R y.1 y.2|}
      ⊆ {w : Data d | η < ⨆ p ∈ K, ⨆ q ∈ K, ⨆ _ : dist p q ≤ δ,
        |barDivisible w R p.1 p.2 - barDivisible w R q.1 q.2|} := by
    intro w hw
    obtain ⟨z, hzK, y, hyK, hzy, hgt⟩ := hw
    set Bnd : ℝ := R ^ ((d : ℝ) / 2 - 2) * ((⌊C * R ^ 2⌋₊ : ℝ) *
      confBox w 0 ((⌈C * R⌉₊ + 1) + ⌊C * R ^ 2⌋₊)) with hBnd
    have hBnd0 : 0 ≤ Bnd := by
      refine mul_nonneg (Real.rpow_nonneg hR0 _) (mul_nonneg (Nat.cast_nonneg _) ?_)
      exact confBox_nonneg _ _ _
    set B : ℝ := 2 * Bnd with hBdef
    have hB0 : 0 ≤ B := by positivity
    have hfb : ∀ p ∈ K, |barDivisible w R p.1 p.2| ≤ Bnd := by
      intro p hp
      exact abs_barDivisible_le hd w hR0 hC (hKC p hp).1 (hKC p hp).2
    have hdiff : ∀ p ∈ K, ∀ q ∈ K,
        |barDivisible w R p.1 p.2 - barDivisible w R q.1 q.2| ≤ B := by
      intro p hp q hq
      calc |barDivisible w R p.1 p.2 - barDivisible w R q.1 q.2|
          ≤ |barDivisible w R p.1 p.2| + |barDivisible w R q.1 q.2| := abs_sub _ _
        _ ≤ B := by rw [hBdef]; linarith [hfb p hp, hfb q hq]
    have hMid : ∀ p ∈ K, (⨆ q ∈ K, ⨆ _ : dist p q ≤ δ,
        |barDivisible w R p.1 p.2 - barDivisible w R q.1 q.2|) ≤ B := by
      intro p hp
      exact Real.iSup_le (fun q => Real.iSup_le (fun hq =>
        Real.iSup_le (fun _ => hdiff p hp q hq) hB0) hB0) hB0
    have hOutBdd : BddAbove (Set.range fun p : ℝ × (Fin d → ℝ) => ⨆ _ : p ∈ K,
        ⨆ q ∈ K, ⨆ _ : dist p q ≤ δ,
          |barDivisible w R p.1 p.2 - barDivisible w R q.1 q.2|) := by
      refine ⟨B, ?_⟩
      rintro _ ⟨p, rfl⟩
      exact Real.iSup_le (fun hp => hMid p hp) hB0
    have hMidBdd : BddAbove (Set.range fun q : ℝ × (Fin d → ℝ) => ⨆ _ : q ∈ K,
        ⨆ _ : dist z q ≤ δ, |barDivisible w R z.1 z.2 - barDivisible w R q.1 q.2|) := by
      refine ⟨B, ?_⟩
      rintro _ ⟨q, rfl⟩
      exact Real.iSup_le (fun hq => Real.iSup_le (fun _ => hdiff z hzK q hq) hB0) hB0
    refine lt_of_lt_of_le hgt ?_
    calc |barDivisible w R z.1 z.2 - barDivisible w R y.1 y.2|
        = ⨆ _ : dist z y ≤ δ,
            |barDivisible w R z.1 z.2 - barDivisible w R y.1 y.2| :=
          (ciSup_pos (f := fun _ : dist z y ≤ δ =>
            |barDivisible w R z.1 z.2 - barDivisible w R y.1 y.2|) (le_of_lt hzy)).symm
      _ = ⨆ _ : y ∈ K, ⨆ _ : dist z y ≤ δ,
            |barDivisible w R z.1 z.2 - barDivisible w R y.1 y.2| :=
          (ciSup_pos (f := fun _ : y ∈ K => ⨆ _ : dist z y ≤ δ,
            |barDivisible w R z.1 z.2 - barDivisible w R y.1 y.2|) hyK).symm
      _ ≤ ⨆ q ∈ K, ⨆ _ : dist z q ≤ δ,
            |barDivisible w R z.1 z.2 - barDivisible w R q.1 q.2| := le_ciSup hMidBdd y
      _ = ⨆ _ : z ∈ K, ⨆ q ∈ K, ⨆ _ : dist z q ≤ δ,
            |barDivisible w R z.1 z.2 - barDivisible w R q.1 q.2| :=
          (ciSup_pos (f := fun _ : z ∈ K => ⨆ q ∈ K, ⨆ _ : dist z q ≤ δ,
            |barDivisible w R z.1 z.2 - barDivisible w R q.1 q.2|) hzK).symm
      _ ≤ _ := le_ciSup hOutBdd z
  have hTfin : (law d ν) {w : Data d | η < ⨆ p ∈ K, ⨆ q ∈ K, ⨆ _ : dist p q ≤ δ,
      |barDivisible w R p.1 p.2 - barDivisible w R q.1 q.2|} ≠ ⊤ := measure_ne_top _ _
  calc (law d ν) {w : Data d | ∃ z ∈ K, ∃ y ∈ K, dist z y < δ ∧
        η < |barDivisible w R z.1 z.2 - barDivisible w R y.1 y.2|}
      ≤ (law d ν) {w : Data d | η < ⨆ p ∈ K, ⨆ q ∈ K, ⨆ _ : dist p q ≤ δ,
        |barDivisible w R p.1 p.2 - barDivisible w R q.1 q.2|} := measure_mono hsub
    _ = ENNReal.ofReal _ := (ENNReal.ofReal_toReal hTfin).symm
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (hR R hRge)

end Parking
end
