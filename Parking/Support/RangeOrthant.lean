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

end Parking

end
