/-
Independent input tables revealed one round at a time.

A coupled process can inspect both states before choosing the entries each
marginal uses. The previous directions of that marginal alone need not determine
that choice. Treating the whole table of a round as one independent coordinate
avoids this restriction: replacing the current table leaves earlier outputs
unchanged, and every section of the current output has the same prescribed law.
Resampling that table and integrating its section proves the finite cylinder
identity, then the joint product law.
-/
import LatticeProb.Prob.Splice

noncomputable section

open MeasureTheory
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The first `n` output layers satisfy their prescribed events. -/
def Parking.layerEvent (F : (ℕ → X) → ℕ → Y) (B : ℕ → Set Y) (n : ℕ) : Set (ℕ → X) :=
  {ω | ∀ k < n, F ω k ∈ B k}

theorem Parking.measurableSet_layerEvent {F : (ℕ → X) → ℕ → Y}
    (hF : Measurable F) {B : ℕ → Set Y} (hB : ∀ n, MeasurableSet (B n)) (n : ℕ) :
    MeasurableSet (Parking.layerEvent F B n) := by
  have heq : Parking.layerEvent F B n =
      ⋂ k ∈ Finset.range n, (fun ω => F ω k) ⁻¹' B k := by
    ext ω
    simp [Parking.layerEvent]
  rw [heq]
  exact MeasurableSet.biInter (Finset.range n).countable_toSet fun k _ =>
    ((measurable_pi_apply k).comp hF) (hB k)

/-- A sequence of transformations preserves the product law when each output
uses only its own and earlier input layers, and its section at the current
layer has the prescribed law for every fixed past. -/
theorem Parking.measure_layerEvent (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure Y) [IsProbabilityMeasure ν] (F : (ℕ → X) → ℕ → Y)
    (hF : Measurable F)
    (hpast : ∀ (ω : ℕ → X) (n k : ℕ) (v : X), k < n →
      F (Function.update ω n v) k = F ω k)
    (hlaw : ∀ (n : ℕ) (ω : ℕ → X),
      μ.map (fun v => F (Function.update ω n v) n) = ν)
    (B : ℕ → Set Y) (hB : ∀ n, MeasurableSet (B n)) (n : ℕ) :
    (Measure.infinitePi fun _ : ℕ => μ) (Parking.layerEvent F B n)
      = ∏ k ∈ Finset.range n, ν (B k) := by
  classical
  let P := Measure.infinitePi fun _ : ℕ => μ
  induction n with
  | zero =>
      have heq : Parking.layerEvent F B 0 = Set.univ := by
        ext ω; simp [Parking.layerEvent]
      simp [heq]
  | succ n ih =>
      have hAn := Parking.measurableSet_layerEvent hF hB n
      have hAs := Parking.measurableSet_layerEvent hF hB (n + 1)
      let T : (ℕ → X) × X → ℕ → X := fun q => Function.update q.1 n q.2
      have hT : MeasurePreserving T (P.prod μ) P :=
        LatticeProb.measurePreserving_update_infinitePi (fun _ : ℕ => μ) n
      have hsec : ∀ ω : ℕ → X,
          (fun v => (ω, v)) ⁻¹' (T ⁻¹' Parking.layerEvent F B (n + 1)) =
            if ω ∈ Parking.layerEvent F B n then
              (fun v => F (Function.update ω n v) n) ⁻¹' B n else ∅ := by
        intro ω
        ext v
        by_cases hω : ω ∈ Parking.layerEvent F B n
        · rw [if_pos hω]
          change (∀ k < n + 1, F (Function.update ω n v) k ∈ B k) ↔
            F (Function.update ω n v) n ∈ B n
          refine ⟨fun h => h n (by omega), fun h k hk => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
          · rw [hpast ω n k v hk]
            exact hω k hk
          · exact h
        · rw [if_neg hω]
          change (∀ k < n + 1, F (Function.update ω n v) k ∈ B k) ↔ False
          refine ⟨fun h => hω (fun k hk => ?_), False.elim⟩
          rw [← hpast ω n k v hk]
          exact h k (by omega)
      have hsect : ∀ ω : ℕ → X,
          μ ((fun v => (ω, v)) ⁻¹' (T ⁻¹' Parking.layerEvent F B (n + 1))) =
            (Parking.layerEvent F B n).indicator (fun _ => ν (B n)) ω := by
        intro ω
        rw [hsec]
        by_cases hω : ω ∈ Parking.layerEvent F B n
        · rw [if_pos hω, Set.indicator_of_mem hω]
          have hm : Measurable (fun v => F (Function.update ω n v) n) := by
            fun_prop
          rw [← Measure.map_apply hm (hB n), hlaw]
        · rw [if_neg hω, Set.indicator_of_notMem hω, measure_empty]
      change P (Parking.layerEvent F B (n + 1)) = _
      rw [← hT.map_eq, Measure.map_apply hT.measurable hAs,
        Measure.prod_apply (hT.measurable hAs)]
      simp_rw [hsect]
      rw [lintegral_indicator hAn, lintegral_const, Measure.restrict_apply_univ,
        Finset.prod_range_succ]
      change ν (B n) * P (Parking.layerEvent F B n) = _
      rw [ih, mul_comm]

/-- The joint output law of transformations with fresh input layers. -/
theorem Parking.map_layers (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure Y) [IsProbabilityMeasure ν] (F : (ℕ → X) → ℕ → Y)
    (hF : Measurable F)
    (hpast : ∀ (ω : ℕ → X) (n k : ℕ) (v : X), k < n →
      F (Function.update ω n v) k = F ω k)
    (hlaw : ∀ (n : ℕ) (ω : ℕ → X),
      μ.map (fun v => F (Function.update ω n v) n) = ν) :
    (Measure.infinitePi fun _ : ℕ => μ).map F = Measure.infinitePi fun _ : ℕ => ν := by
  classical
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  obtain ⟨n, hn⟩ := s.exists_nat_subset_range
  let B : ℕ → Set Y := fun k => if k ∈ s then t k else Set.univ
  have hB : ∀ k, MeasurableSet (B k) := by
    intro k
    dsimp [B]
    split <;> simp_all
  have heq : F ⁻¹' Set.pi (↑s) t = Parking.layerEvent F B n := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe,
      Parking.layerEvent, Set.mem_setOf_eq]
    constructor
    · intro h k _
      by_cases hk : k ∈ s
      · simpa [B, hk] using h k hk
      · simp [B, hk]
    · intro h k hk
      simpa [B, hk] using h k (Finset.mem_range.mp (hn hk))
  rw [Measure.map_apply hF (MeasurableSet.pi s.countable_toSet fun k _ => ht k), heq,
    Parking.measure_layerEvent μ ν F hF hpast hlaw B hB n]
  calc
    (∏ k ∈ Finset.range n, ν (B k)) = (∏ k ∈ s, ν (B k)) := by
      symm
      exact Finset.prod_subset hn fun k _ hk => by simp [B, hk]
    _ = (∏ k ∈ s, ν (t k)) := Finset.prod_congr rfl fun k hk => by simp [B, hk]

end
