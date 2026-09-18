/-
The probability endgame of `parking.tex:1807-1833`.
The positive-event estimate is an explicit hypothesis. Its derivation uses
spatial scaling and the cited critical-scale lower tail. Substitution of the
radius `sqrt t` recovers every integer horizon exactly.
-/
import Parking.Support.NearestEvents
import Parking.Support.Invariance

noncomputable section
open MeasureTheory LatticeProb Filter Topology

theorem Parking.sqrt_nat_floor_sq (t : ℕ) : ⌊(Real.sqrt (t : ℝ)) ^ 2⌋₊ = t := by
  rw [Real.sq_sqrt (Nat.cast_nonneg t)]
  simp

theorem Parking.tendsto_zero_of_eventual_small {ι : Type*} (l : Filter ι) (f : ι → ℝ)
    (h0 : ∀ i, 0 ≤ f i) (hf : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, f i ≤ ε) :
    Tendsto f l (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun i => ha.trans_le (h0 i)
  · intro b hb
    filter_upwards [hf (b / 2) (by linarith)] with i hi
    linarith

theorem Parking.sqrt_nat_tendsto_atTop :
    Tendsto (fun t : ℕ => Real.sqrt (t : ℝ)) atTop atTop := by
  exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop

theorem Parking.tendsto_of_floor_sq (f : ℕ → ℝ)
    (h : Tendsto (fun R : ℝ => f ⌊R ^ 2⌋₊) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  simpa only [Function.comp_def, Parking.sqrt_nat_floor_sq] using h.comp Parking.sqrt_nat_tendsto_atTop

theorem Parking.nearest_tendsto_of_good_events {d : ℕ} (μ : Measure (Parking.Data d))
    [IsProbabilityMeasure μ] (G : ℝ → ℕ → Set (Parking.Data d))
    (hG : ∀ ε t, MeasurableSet (G ε t))
    (hdisj : ∀ ε t ω, ω ∈ G ε t → ¬ Parking.HoleCloser ω t)
    (hgood : ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℕ in atTop, 1 - ε ≤ (μ (G ε t)).toReal) :
    Tendsto (fun t : ℕ => (μ {ω | Parking.HoleCloser ω t}).toReal) atTop (𝓝 0) := by
  apply Parking.tendsto_zero_of_eventual_small _ _ (fun _ => ENNReal.toReal_nonneg)
  intro ε hε
  filter_upwards [hgood ε hε] with t ht
  have hb := Parking.measureReal_le_one_sub_of_disjoint μ {ω | Parking.HoleCloser ω t}
    (G ε t) (hG ε t) (Set.disjoint_left.mpr (fun ω hω hg => hdisj ε t ω hg hω))
  linarith

/-- The limit follows when positive test events are arbitrarily likely at large scales. -/
theorem Parking.nearest_of_rescaled_positive_events {d : ℕ} (μ : Measure (Parking.Data d))
    [IsProbabilityMeasure μ]
    (hEvents : ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ ∃ φ : (Fin d → ℝ) → ℝ,
      (∀ x, 0 ≤ φ x) ∧ (∀ x, 0 < φ x → (∑ i : Fin d, |x i|) ≤ r) ∧
      ∀ᶠ R : ℝ in atTop, 1 - ε ≤ (μ (Parking.PositiveTestEvent R r φ)).toReal) :
    Tendsto (fun t : ℕ => (μ {ω | Parking.HoleCloser ω t}).toReal) atTop (𝓝 0) := by
  apply Parking.tendsto_of_floor_sq
  apply Parking.tendsto_zero_of_eventual_small _ _ (fun _ => ENNReal.toReal_nonneg)
  intro ε hε
  obtain ⟨r, _, φ, hφ, hsupp, hg⟩ := hEvents ε hε
  filter_upwards [hg, eventually_gt_atTop (0 : ℝ)] with R hgood hR
  have hb := Parking.nearest_probability_le_complement μ hR φ hφ hsupp
  linarith

/-- The same conditional limit for the independent parking law. -/
theorem Parking.nearest_of_positive_test_events {d : ℕ} (hd : 1 ≤ d) (ν : Measure ℤ)
    (hprob : IsProbabilityMeasure ν)
    (hEvents : ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ ∃ φ : (Fin d → ℝ) → ℝ,
      (∀ x, 0 ≤ φ x) ∧ (∀ x, 0 < φ x → (∑ i : Fin d, |x i|) ≤ r) ∧
      ∀ᶠ R : ℝ in atTop, 1 - ε ≤ ((Parking.law d ν) (Parking.PositiveTestEvent R r φ)).toReal) :
    Tendsto (fun t : ℕ => ((Parking.law d ν) {ω | Parking.HoleCloser ω t}).toReal) atTop (𝓝 0) := by
  haveI := hprob
  haveI := Parking.stackRankLaw_isProbability hd
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw
    infer_instance
  haveI : IsProbabilityMeasure (Parking.law d ν) :=
    inferInstanceAs (IsProbabilityMeasure ((LatticeProb.iidLaw d ν).prod (Parking.stackRankLaw d)))
  exact Parking.nearest_of_rescaled_positive_events (Parking.law d ν) hEvents

end
