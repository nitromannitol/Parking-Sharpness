import Parking.Support.RangeSymmetry

/-!
# Reflections into an orthant

A reflection-invariant event of the walk retains at least a fraction `2⁻ᵈ`
of its probability when the endpoint is required to lie in a given orthant.
-/

open MeasureTheory

noncomputable section

namespace Parking

variable {d : ℕ}

/-- The walk endpoint lies in the orthant selected by `q`. -/
def endpointOrthant (n : ℕ) (q : Fin d → Bool) : Set (ℕ → Fin d × Bool) :=
  {p | ∀ i, if q i then 0 ≤ walkPath (0 : Site d) p n i
    else walkPath (0 : Site d) p n i ≤ 0}

/-- The endpoint orthant is measurable. -/
theorem measurableSet_endpointOrthant (n : ℕ) (q : Fin d → Bool) :
    MeasurableSet (endpointOrthant n q) := by
  have heq : endpointOrthant n q = ⋂ i : Fin d,
      {p | if q i then 0 ≤ walkPath (0 : Site d) p n i
        else walkPath (0 : Site d) p n i ≤ 0} := by
    ext p
    simp [endpointOrthant]
  rw [heq]
  refine MeasurableSet.iInter fun i => ?_
  have hm : Measurable fun p : ℕ → Fin d × Bool => walkPath (0 : Site d) p n i :=
    (measurable_of_countable (fun x : Site d => x i)).comp (measurable_walkPath 0 n)
  cases hq : q i
  · simpa only [hq, Bool.false_eq_true, ite_false] using measurableSet_le hm measurable_const
  · simpa only [hq, ite_true] using measurableSet_le measurable_const hm

/-- Every lattice site can be reflected into any prescribed orthant. -/
theorem exists_reflectSite_mem_orthant (x : Site d) (q : Fin d → Bool) :
    ∃ s : Fin d → Bool, ∀ i, if q i then 0 ≤ reflectSite s x i else reflectSite s x i ≤ 0 := by
  let s : Fin d → Bool := fun i => if q i then decide (x i < 0) else decide (0 < x i)
  refine ⟨s, fun i => ?_⟩
  cases hq : q i
  · by_cases hx : 0 < x i <;> simp [reflectSite, s, hq, hx] <;> omega
  · by_cases hx : x i < 0 <;> simp [reflectSite, s, hq, hx] <;> omega

/-- A reflection-invariant event retains at least a `2⁻ᵈ` fraction of its
probability when the endpoint is constrained to a given orthant. -/
theorem measureReal_le_pow_mul_endpointOrthant (hd : 1 ≤ d) (n : ℕ)
    (q : Fin d → Bool) (A : Set (ℕ → Fin d × Bool)) (hA : MeasurableSet A)
    (hinv : ∀ (s : Fin d → Bool) p,
      (fun k => reflectDirection s (p k)) ∈ A ↔ p ∈ A) :
    (walkLaw d).real A ≤ (2 : ℝ) ^ d * (walkLaw d).real (A ∩ endpointOrthant n q) := by
  have := stepLaw_isProbability hd
  have : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  let B := A ∩ endpointOrthant n q
  have hB : MeasurableSet B := hA.inter (measurableSet_endpointOrthant n q)
  have hsub : A ⊆ ⋃ s : Fin d → Bool,
      (fun p : ℕ → Fin d × Bool => fun k => reflectDirection s (p k)) ⁻¹' B := by
    intro p hp
    obtain ⟨s, hs⟩ := exists_reflectSite_mem_orthant (walkPath (0 : Site d) p n) q
    refine Set.mem_iUnion.mpr ⟨s, ?_⟩
    change (fun k => reflectDirection s (p k)) ∈ A ∩ endpointOrthant n q
    constructor
    · exact (hinv s p).mpr hp
    · change ∀ i, if q i then 0 ≤ walkPath (0 : Site d)
          (fun k => reflectDirection s (p k)) n i else walkPath (0 : Site d)
          (fun k => reflectDirection s (p k)) n i ≤ 0
      rw [walkPath_reflectDirections]
      exact hs
  calc (walkLaw d).real A ≤ (walkLaw d).real (⋃ s : Fin d → Bool,
        (fun p : ℕ → Fin d × Bool => fun k => reflectDirection s (p k)) ⁻¹' B) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ s : Fin d → Bool, (walkLaw d).real
        ((fun p : ℕ → Fin d × Bool => fun k => reflectDirection s (p k)) ⁻¹' B) :=
      measureReal_iUnion_fintype_le _
    _ = (2 : ℝ) ^ d * (walkLaw d).real B := by
      have hs (s : Fin d → Bool) : (walkLaw d).real
          ((fun p : ℕ → Fin d × Bool => fun k => reflectDirection s (p k)) ⁻¹' B) =
          (walkLaw d).real B := by
        rw [measureReal_def, (measurePreserving_reflectDirections hd s).measure_preimage
          hB.nullMeasurableSet, ← measureReal_def]
      simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- A walk remains within the graph-norm radius `d * r` through time `n`. -/
def walkDisplacementSmall (n : ℕ) (r : ℝ) : Set (ℕ → Fin d × Bool) :=
  {p | ∀ k ≤ n, (graphNorm (walkPath (0 : Site d) p k) : ℝ) < (d : ℝ) * r}

/-- The small-displacement event is measurable. -/
theorem measurableSet_walkDisplacementSmall (n : ℕ) (r : ℝ) :
    MeasurableSet (walkDisplacementSmall (d := d) n r) := by
  have heq : walkDisplacementSmall (d := d) n r =
      {p | ∃ k ≤ n, (d : ℝ) * r ≤ (graphNorm (walkPath (0 : Site d) p k) : ℝ)}ᶜ := by
    ext p
    simp only [walkDisplacementSmall, Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists,
      not_and, not_le]
  rw [heq]
  exact (measurableSet_walkPath_graphNorm_ge n ((d : ℝ) * r)).compl

/-- A short walk has a uniform chance to stay close and finish in a prescribed orthant. -/
theorem half_le_pow_mul_walkDisplacementSmall_orthant (hd : 1 ≤ d) (n : ℕ)
    {r : ℝ} (hr : 0 < r) (hn : (n : ℝ) ≤ r ^ 2 / 2) (q : Fin d → Bool) :
    (1 : ℝ) / 2 ≤ (2 : ℝ) ^ d * (walkLaw d).real
      (walkDisplacementSmall n r ∩ endpointOrthant n q) := by
  have := stepLaw_isProbability hd
  have : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  let E : Set (ℕ → Fin d × Bool) :=
    {p | ∃ k ≤ n, (d : ℝ) * r ≤ (graphNorm (walkPath (0 : Site d) p k) : ℝ)}
  have hE : MeasurableSet E := measurableSet_walkPath_graphNorm_ge n ((d : ℝ) * r)
  have hEc : walkDisplacementSmall (d := d) n r = Eᶜ := by
    ext p
    simp only [walkDisplacementSmall, E, Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists,
      not_and, not_le]
  have hsmall : (walkLaw d).real E ≤ 1 / 2 := by
    have hbound := measureReal_sup_walkPath_graphNorm_le hd n hr
    have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
    exact hbound.trans ((div_le_iff₀ hr2).2 (by nlinarith [hn]))
  have hlarge : (1 : ℝ) / 2 ≤ (walkLaw d).real (walkDisplacementSmall n r) := by
    have hsum := measureReal_add_measureReal_compl (μ := walkLaw d) hE
    rw [probReal_univ] at hsum
    rw [hEc]
    linarith
  refine hlarge.trans (measureReal_le_pow_mul_endpointOrthant hd n q _
    (measurableSet_walkDisplacementSmall n r) ?_)
  intro s p
  simp only [walkDisplacementSmall, Set.mem_ofPred_eq, walkPath_reflectDirections,
    graphNorm_reflectSite]

end Parking

end
