/-
Joint measurability of the quantities of Step 2 of `lem:mean-horizon`.

The lemma's stopping rule `σ` is a stopping time of the walk for each
configuration and a measurable function of the configuration for each path;
Step 2 integrates over both, so it needs the two together.  The bridge is that a
stopping time bounded by `n` reads only the first `n+1` positions of the path,
and those range over a COUNTABLE set, so the joint measurability follows from
`measurable_from_prod_countable_left`.  The same countability of the lattice
gives joint measurability of `(η, y) ↦ η y` and of `(η, y) ↦ u_ℓ(y; ξ_δ)`,
which are the other two shapes Step 2 integrates.
-/
import Parking.Support.StoppingBlocks

noncomputable section

namespace Parking

open MeasureTheory LatticeProb

variable {d : ℕ}

/-- A path read off its first `n+1` positions. -/
def pathTrunc (n : ℕ) (a : Fin (n + 1) → Site d) : ℕ → Site d :=
  fun j => if h : j < n + 1 then a ⟨j, h⟩ else 0

theorem pathTrunc_eq (n : ℕ) (X : ℕ → Site d) {j : ℕ} (hj : j ≤ n) :
    pathTrunc n (fun i : Fin (n + 1) => X i) j = X j := by
  rw [pathTrunc, dif_pos (by omega : j < n + 1)]

/-- **A bounded family of stopping times, measurable in the configuration, is jointly
measurable.**  The stopping time reads only the first `n+1` positions of the path, and
those range over a countable set. -/
theorem measurable_uncurry_stopping {σ : (Site d → ℤ) → (ℕ → Site d) → ℕ}
    (hσ : ∀ η, LatticeProb.IsWalkStopping (σ η)) {n : ℕ} (hσn : ∀ η X, σ η X ≤ n)
    (hm : ∀ X, Measurable fun η => σ η X) :
    Measurable (Function.uncurry σ) := by
  classical
  have hkey : ∀ (η : Site d → ℤ) (X : ℕ → Site d),
      σ η X = σ η (pathTrunc n (fun i : Fin (n + 1) => X i)) := by
    intro η X
    exact LatticeProb.dependsUpTo_of_isWalkStopping (hσ η) (hσn η) X _
      (fun j hj => (pathTrunc_eq n X hj).symm)
  have hG : Measurable (fun p : (Site d → ℤ) × (Fin (n + 1) → Site d) =>
      σ p.1 (pathTrunc n p.2)) :=
    measurable_from_prod_countable_left (fun a => hm (pathTrunc n a))
  have hr : Measurable (fun p : (Site d → ℤ) × (ℕ → Site d) =>
      (p.1, fun i : Fin (n + 1) => p.2 i)) :=
    measurable_fst.prodMk (measurable_pi_lambda _ fun i => measurable_snd.eval)
  have heq : Function.uncurry σ
      = (fun p : (Site d → ℤ) × (Fin (n + 1) → Site d) => σ p.1 (pathTrunc n p.2))
        ∘ (fun p : (Site d → ℤ) × (ℕ → Site d) => (p.1, fun i : Fin (n + 1) => p.2 i)) := by
    funext p
    exact hkey p.1 p.2
  rw [heq]
  exact hG.comp hr

/-! ### Joint measurability of the quantities of Step 2 -/

theorem measurable_eval_pair {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] :
    Measurable (fun p : (Site d → α) × Site d => p.1 p.2) :=
  measurable_from_prod_countable_left (fun y => measurable_pi_apply y)

theorem measurable_xi_pair (δ : ℝ) :
    Measurable (fun p : (Site d → ℤ) × Site d => Parking.xi δ p.1 p.2) := by
  have h : Measurable (fun p : (Site d → ℤ) × Site d => ((p.1 p.2 : ℤ) : ℝ)) :=
    measurable_intCastReal.comp measurable_eval_pair
  simpa only [Parking.xi] using h.add_const δ

theorem measurable_xiField (δ : ℝ) :
    Measurable (fun η : Site d → ℤ => Parking.xi δ η) :=
  measurable_pi_lambda _ fun y =>
    (measurable_intCastReal.comp (measurable_pi_apply y)).add_const δ

theorem measurable_u_xi_pair (δ : ℝ) (ℓ : ℕ) :
    Measurable (fun p : (Site d → ℤ) × Site d => u (Parking.xi δ p.1) ℓ p.2) :=
  measurable_from_prod_countable_left
    (fun y => (measurable_u_eval ℓ y).comp (measurable_xiField δ))

theorem measurable_rewardSum {σ : (Site d → ℤ) → (ℕ → Site d) → ℕ}
    (hσ : ∀ η, LatticeProb.IsWalkStopping (σ η)) {n : ℕ} (hσn : ∀ η X, σ η X ≤ n)
    (hm : ∀ X, Measurable fun η => σ η X) (δ : ℝ) :
    Measurable (fun p : (Site d → ℤ) × (ℕ → Site d) =>
      ∑ j ∈ Finset.range (σ p.1 p.2), Parking.xi δ p.1 (p.2 j)) := by
  classical
  have hσm : Measurable (Function.uncurry σ) := measurable_uncurry_stopping hσ hσn hm
  have heq : (fun p : (Site d → ℤ) × (ℕ → Site d) =>
        ∑ j ∈ Finset.range (σ p.1 p.2), Parking.xi δ p.1 (p.2 j))
      = fun p => ∑ i ∈ Finset.range (n + 1),
          (if σ p.1 p.2 = i then ∑ j ∈ Finset.range i, Parking.xi δ p.1 (p.2 j) else 0) := by
    funext p
    rw [Finset.sum_eq_single (σ p.1 p.2) (fun i _ hi => if_neg fun h => hi h.symm)
      (fun hmem => absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (hσn p.1 p.2))) hmem)]
    rw [if_pos rfl]
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Measurable.ite (hσm (measurableSet_singleton i)) ?_ measurable_const
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (measurable_xi_pair (d := d) δ).fun_comp
    (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))

theorem measurable_blockTerm {σ : (Site d → ℤ) → (ℕ → Site d) → ℕ}
    (hσ : ∀ η, LatticeProb.IsWalkStopping (σ η)) {n : ℕ} (hσn : ∀ η X, σ η X ≤ n)
    (hm : ∀ X, Measurable fun η => σ η X) (δ : ℝ) (s ℓ : ℕ) :
    Measurable (fun p : (Site d → ℤ) × (ℕ → Site d) =>
      if s < σ p.1 p.2 then u (Parking.xi δ p.1) ℓ (p.2 s) else 0) := by
  have hσm : Measurable (Function.uncurry σ) := measurable_uncurry_stopping hσ hσn hm
  refine Measurable.ite (hσm (measurableSet_Ioi (a := s))) ?_ measurable_const
  exact (measurable_u_xi_pair (d := d) δ ℓ).fun_comp
    (measurable_fst.prodMk ((measurable_pi_apply s).comp measurable_snd))

/-! ### Integrability of a function of one coordinate -/

theorem integrable_eval_iid {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {f : α → ℝ} (hf : Integrable f ν) (z : Site d) :
    Integrable (fun η : Site d → α => f (η z)) (LatticeProb.iidLaw d ν) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  exact (measurePreserving_eval_infinitePi (fun _ : Site d => ν) z).integrable_comp_of_integrable hf

theorem integrable_boxSum_xi (δ : ℝ) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => ((k : ℝ))) ν) (t : ℕ) :
    Integrable (fun η : Site d → ℤ => ∑ z ∈ boxFinset (0 : Site d) t, |Parking.xi δ η z|)
      (LatticeProb.iidLaw d ν) := by
  refine integrable_finsetSum _ fun z _ => ?_
  have h : Integrable (fun k : ℤ => |((k : ℝ)) + δ|) ν :=
    (hint.add (integrable_const δ)).abs
  exact integrable_eval_iid ν h z

end Parking

end
