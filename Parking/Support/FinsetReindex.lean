/-
The measure-preserving bijection between a `Fintype`-indexed product measure and its
`Fin N`-indexed reindexing, needed to apply the shared library's
`LatticeProb.weighted_exp_conc_exp`/`weighted_exp_conc_tail` (stated for `Fin N → ℝ`) to a
function of a finite BOX of sites (naturally indexed by a `Finset (Site d)`, not by `Fin N`).
General purpose, nothing here is specific to the parking model.
-/
import Mathlib

noncomputable section

open MeasureTheory

variable {ι : Type*} [Fintype ι]

/-- The bijection `(Fin (card ι) → ℝ) ≃ (ι → ℝ)` induced by `Fintype.equivFin`, with
computation lemmas that hold by `rfl`. -/
def finEquivIndex (ι : Type*) [Fintype ι] : (Fin (Fintype.card ι) → ℝ) ≃ (ι → ℝ) where
  toFun ξ k := ξ (Fintype.equivFin ι k)
  invFun ζ j := ζ (Fintype.equivFin ι |>.symm j)
  left_inv ξ := funext fun j => by simp
  right_inv ζ := funext fun k => by simp

theorem finEquivIndex_apply (ξ : Fin (Fintype.card ι) → ℝ) (k : ι) :
    finEquivIndex ι ξ k = ξ (Fintype.equivFin ι k) := rfl

theorem measurable_finEquivIndex : Measurable (finEquivIndex ι) :=
  measurable_pi_lambda _ fun k => measurable_pi_apply (Fintype.equivFin ι k)

theorem measurable_finEquivIndex_symm : Measurable (finEquivIndex ι).symm :=
  measurable_pi_lambda _ fun j => measurable_pi_apply ((Fintype.equivFin ι).symm j)

/-- **The `Fin N` reindexing of a `Fintype`-indexed product measure is measure preserving.** -/
theorem measurePreserving_finEquivIndex (ν0 : Measure ℝ) [IsProbabilityMeasure ν0] :
    MeasurePreserving (finEquivIndex ι) (Measure.pi fun _ : Fin (Fintype.card ι) => ν0)
      (Measure.pi fun _ : ι => ν0) := by
  refine ⟨measurable_finEquivIndex, ?_⟩
  symm
  refine Measure.pi_eq fun t ht => ?_
  rw [Measure.map_apply measurable_finEquivIndex (MeasurableSet.univ_pi ht)]
  have hpre : (finEquivIndex ι) ⁻¹' (Set.univ.pi t)
      = Set.univ.pi (fun j : Fin (Fintype.card ι) => t ((Fintype.equivFin ι).symm j)) := by
    ext ξ
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h j
      have := h ((Fintype.equivFin ι).symm j)
      simpa [finEquivIndex_apply] using this
    · intro h k
      have := h (Fintype.equivFin ι k)
      simpa [finEquivIndex_apply] using this
  rw [hpre, Measure.pi_pi]
  exact (Fintype.prod_equiv (Fintype.equivFin ι) (fun k => ν0 (t k))
    (fun j => ν0 (t ((Fintype.equivFin ι).symm j))) (fun k => by simp)).symm

/-- `finEquivIndex ι` as a measurable equivalence. -/
def finMEquivIndex (ι : Type*) [Fintype ι] : (Fin (Fintype.card ι) → ℝ) ≃ᵐ (ι → ℝ) where
  toEquiv := finEquivIndex ι
  measurable_toFun := measurable_finEquivIndex
  measurable_invFun := measurable_finEquivIndex_symm

theorem measurableEmbedding_finEquivIndex : MeasurableEmbedding (finEquivIndex ι) :=
  (finMEquivIndex ι).measurableEmbedding

/-- **Transporting an integral along the `Fin N` reindexing.** -/
theorem integral_finEquivIndex_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (ν0 : Measure ℝ) [IsProbabilityMeasure ν0] (g : (ι → ℝ) → G) :
    (∫ ξ, g (finEquivIndex ι ξ) ∂(Measure.pi fun _ : Fin (Fintype.card ι) => ν0))
      = ∫ ζ, g ζ ∂(Measure.pi fun _ : ι => ν0) :=
  MeasurePreserving.integral_comp (measurePreserving_finEquivIndex ν0)
    measurableEmbedding_finEquivIndex g

/-- **Transporting a measured set along the `Fin N` reindexing.** -/
theorem measure_preimage_finEquivIndex (ν0 : Measure ℝ) [IsProbabilityMeasure ν0]
    {T : Set (ι → ℝ)} (hT : MeasurableSet T) :
    (Measure.pi fun _ : Fin (Fintype.card ι) => ν0) ((finEquivIndex ι) ⁻¹' T)
      = (Measure.pi fun _ : ι => ν0) T := by
  rw [← (measurePreserving_finEquivIndex (ι := ι) ν0).map_eq,
    Measure.map_apply measurable_finEquivIndex hT]

/-- **Updating `finEquivIndex ι` transports along the index bijection.** -/
theorem finEquivIndex_update (ξ : Fin (Fintype.card ι) → ℝ) (j : Fin (Fintype.card ι))
    (v : ℝ) [DecidableEq ι] :
    finEquivIndex ι (Function.update ξ j v)
      = Function.update (finEquivIndex ι ξ) (Fintype.equivFin ι |>.symm j) v := by
  funext k
  rw [finEquivIndex_apply]
  by_cases hk : k = (Fintype.equivFin ι).symm j
  · subst hk
    rw [Equiv.apply_symm_apply, Function.update_self, Function.update_self]
  · have hne : Fintype.equivFin ι k ≠ j := by
      intro hcontra
      exact hk (by rw [← hcontra, Equiv.symm_apply_apply])
    rw [Function.update_of_ne hne, Function.update_of_ne hk]
    exact (finEquivIndex_apply ξ k).symm

end

variable {ι' : Type*}

/-- **A nonnegative function vanishing outside a nonempty finite set has the same
supremum over the whole type as over that set.** -/
theorem ciSup_eq_ciSup_subtype_of_forall_not_mem_eq_zero [Nonempty ι'] {s : Finset ι'}
    {f : ι' → ℝ} (hf0 : ∀ i, 0 ≤ f i) (hz : ∀ i ∉ s, f i = 0) (hne : s.Nonempty) :
    (⨆ i, f i) = ⨆ i : (s : Finset ι'), f (i : ι') := by
  haveI : Nonempty (s : Finset ι') := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have hbdd : BddAbove (Set.range f) := by
    refine ⟨max 0 (s.sup' hne f), ?_⟩
    rintro _ ⟨i, rfl⟩
    by_cases hi : i ∈ s
    · exact le_max_of_le_right (Finset.le_sup' f hi)
    · rw [hz i hi]; exact le_max_left _ _
  have hbdd' : BddAbove (Set.range (fun i : (s : Finset ι') => f (i : ι'))) :=
    Finite.bddAbove_range _
  have h1 : (⨆ i, f i) ≤ ⨆ i : (s : Finset ι'), f (i : ι') := by
    refine ciSup_le fun i => ?_
    by_cases hi : i ∈ s
    · exact le_ciSup (f := fun i : (s : Finset ι') => f (i : ι')) hbdd' ⟨i, hi⟩
    · rw [hz i hi]
      obtain ⟨i₀, hi₀⟩ := hne
      exact le_trans (hf0 (i₀ : ι'))
        (le_ciSup (f := fun i : (s : Finset ι') => f (i : ι')) hbdd' ⟨i₀, hi₀⟩)
  have h2 : (⨆ i : (s : Finset ι'), f (i : ι')) ≤ ⨆ i, f i :=
    ciSup_le fun i => le_ciSup hbdd (i : ι')
  exact le_antisymm h1 h2
