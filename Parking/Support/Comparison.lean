/-
Theorem 4.1 of `parking.tex`: averaging the instructions while holding the
configuration fixed bounds the divisible odometer above by the particle
odometer.

With the configuration fixed the particle odometer is bounded: the particles
active at a site after `t` rounds are candidates for it, and there are at most
`∑_{y} η(y)⁺` of those over the box of radius `t`.  So every average below is an
average of a bounded function, and the sum over the instruction indices that
turns `I_{y,x}(U_n(y))` into a sum of indicators is a finite sum, which is what
lets `lem:deferred` be summed one index at a time:

  `E[I_{y,x}(U_n(y)) | η] = P(y,x) E[U_n(y) | η]`.

Summing that over the neighbours of `x` gives `(P v_n)(x)`, and the positive
part in the parallel identity is convex, so averaging it can only raise it:
`v_{n+1} ≥ (η + P v_n)⁺`.  Since `v ↦ (η + P v)⁺` is monotone and `u_0 = v_0`,
induction finishes.
-/
import Parking.Support.DeferredIntegral

noncomputable section

namespace Parking

open LatticeProb Finset MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- An a priori bound on the odometer for a fixed configuration. -/
def uBound (η : Site d → ℤ) (n : ℕ) (x : Site d) : ℕ :=
  ∑ s ∈ Finset.range n, ∑ y ∈ boxFinset x s, (η y).toNat

theorem card_candidates_le (η : Site d → ℤ) (x : Site d) (r : ℕ) :
    (candidates η x r).card ≤ ∑ y ∈ boxFinset x r, (η y).toNat := by
  refine le_trans (Finset.card_biUnion_le) (Finset.sum_le_sum fun y _ => ?_)
  rw [Finset.card_map, Finset.card_range]

theorem activeCount_le (ω : Data d) (t : ℕ) (x : Site d) :
    A ω t x ≤ ∑ y ∈ boxFinset x t, (ω.1 y).toNat :=
  le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (card_candidates_le _ _ _)

theorem U_le_uBound (ω : Data d) (n : ℕ) (x : Site d) : U ω n x ≤ uBound ω.1 n x := by
  rw [U_eq_sum_A]
  exact Finset.sum_le_sum fun s _ => activeCount_le ω s x

theorem arrivals_eq_sum (σ : Site d × ℕ → Site d) (y x : Site d) (m M : ℕ) (hm : m ≤ M) :
    arrivals σ y x m = ∑ j ∈ Finset.range M, if j < m ∧ σ (y, j) = x then 1 else 0 := by
  classical
  unfold arrivals
  rw [Finset.card_filter]
  rw [← Finset.sum_subset (show Finset.range m ⊆ Finset.range M from fun j hj =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hm))]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : j < m := Finset.mem_range.mp hj
    by_cases h : σ (y, j) = x <;> simp [h, hjm]
  · intro j _ hj
    rw [if_neg (fun hc => hj (Finset.mem_range.mpr hc.1))]

theorem measurable_Ugiven (η : Site d → ℤ) (n : ℕ) (x : Site d) :
    Measurable fun s : Randomness d => (U ((η, s) : Data d) n x : ℝ) :=
  (measurable_from_countable' fun m : ℕ => (m : ℝ)).comp
    ((measurable_U n x).comp (measurable_const.prodMk measurable_id))

theorem integrable_Ugiven (hd : 1 ≤ d) (η : Site d → ℤ) (n : ℕ) (x : Site d) :
    Integrable (fun s : Randomness d => (U ((η, s) : Data d) n x : ℝ)) (stackRankLaw d) := by
  haveI : ∀ q : Site d × ℕ, IsProbabilityMeasure (instructionLaw (d := d) q.1) :=
    fun q => instructionLaw_isProbability hd q.1
  haveI := rankLaw_isProbability d
  haveI : IsProbabilityMeasure (stackRankLaw d) := by
    unfold stackRankLaw stackLaw; infer_instance
  refine (integrable_const ((uBound η n x : ℝ))).mono'
    (measurable_Ugiven η n x).aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
  have := U_le_uBound ((η, s) : Data d) n x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact_mod_cast this

theorem integrable_indicator_U (hd : 1 ≤ d) (η : Site d → ℤ)
    (E : Set (Data d)) (hE : MeasurableSet E) :
    Integrable (fun s : Randomness d =>
      Set.indicator E (fun _ => (1 : ℝ)) ((η, s) : Data d)) (stackRankLaw d) := by
  haveI : ∀ q : Site d × ℕ, IsProbabilityMeasure (instructionLaw (d := d) q.1) :=
    fun q => instructionLaw_isProbability hd q.1
  haveI := rankLaw_isProbability d
  haveI : IsProbabilityMeasure (stackRankLaw d) := by
    unfold stackRankLaw stackLaw; infer_instance
  refine (integrable_const (1 : ℝ)).mono'
    (((measurable_one.indicator hE).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun s => ?_)
  by_cases hs : ((η, s) : Data d) ∈ E
  · simp [Set.indicator_of_mem hs]
  · simp [Set.indicator_of_notMem hs]

theorem measurableSet_U_ge (n : ℕ) (y : Site d) (j : ℕ) :
    MeasurableSet {ω : Data d | j + 1 ≤ U ω n y} := by
  have : {ω : Data d | j + 1 ≤ U ω n y} = (fun ω : Data d => U ω n y) ⁻¹' {m : ℕ | j + 1 ≤ m} :=
    rfl
  rw [this]
  exact (measurable_U n y) (Set.to_countable _).measurableSet

theorem measurableSet_U_ge_and (n : ℕ) (y x : Site d) (j : ℕ) :
    MeasurableSet {ω : Data d | j + 1 ≤ U ω n y ∧ ω.2.1 (y, j) = x} := by
  have hsplit : {ω : Data d | j + 1 ≤ U ω n y ∧ ω.2.1 (y, j) = x}
      = {ω : Data d | j + 1 ≤ U ω n y} ∩
        ((fun ω : Data d => ω.2.1 (y, j)) ⁻¹' ({x} : Set (Site d))) := rfl
  rw [hsplit]
  exact (measurableSet_U_ge n y j).inter
    (((measurable_pi_apply (y, j)).comp (measurable_fst.comp measurable_snd))
      (measurableSet_singleton x))

theorem arrivals_indicator_sum (η : Site d → ℤ) (n : ℕ) (y x : Site d)
    (s : Randomness d) : (arrivals s.1 y x (U ((η, s) : Data d) n y) : ℝ)
      = ∑ j ∈ Finset.range (uBound η n y),
        Set.indicator {ω : Data d | j + 1 ≤ U ω n y ∧ ω.2.1 (y, j) = x}
          (fun _ => (1 : ℝ)) ((η, s) : Data d) := by
  classical
    rw [arrivals_eq_sum s.1 y x _ (uBound η n y) (U_le_uBound ((η, s) : Data d) n y)]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h1 : j + 1 ≤ U ((η, s) : Data d) n y <;> by_cases h2 : s.1 (y, j) = x
  · rw [Set.indicator_of_mem (show ((η, s) : Data d)
        ∈ {ω : Data d | j + 1 ≤ U ω n y ∧ ω.2.1 (y, j) = x} from ⟨h1, h2⟩)]
    simp [show j < U ((η, s) : Data d) n y from h1, h2]
  · rw [Set.indicator_of_notMem (show ((η, s) : Data d)
        ∉ {ω : Data d | j + 1 ≤ U ω n y ∧ ω.2.1 (y, j) = x} from fun hc => h2 hc.2)]
    simp [h2]
  · rw [Set.indicator_of_notMem (show ((η, s) : Data d)
        ∉ {ω : Data d | j + 1 ≤ U ω n y ∧ ω.2.1 (y, j) = x} from fun hc => h1 hc.1)]
    simp [show ¬ j < U ((η, s) : Data d) n y from h1]
  · rw [Set.indicator_of_notMem (show ((η, s) : Data d)
        ∉ {ω : Data d | j + 1 ≤ U ω n y ∧ ω.2.1 (y, j) = x} from fun hc => h1 hc.1)]
    simp [show ¬ j < U ((η, s) : Data d) n y from h1]

/-- Averaging the arrivals from one neighbour, with the configuration fixed. -/
theorem meanUgiven_arrivals (hd : 1 ≤ d) (η : Site d → ℤ) (n : ℕ) (y x : Site d) :
    ∫ s : Randomness d, (arrivals s.1 y x (U ((η, s) : Data d) n y) : ℝ) ∂(stackRankLaw d)
      = kern d y x * meanUgiven d η n y := by
  classical
  set M := uBound η n y with hM
  have hrw := arrivals_indicator_sum (d := d) η n y x
  simp only [hrw]
  rw [integral_finsetSum _ fun j _ =>
    integrable_indicator_U hd η _ (measurableSet_U_ge_and n y x j)]
  have hj : ∀ j : ℕ,
      ∫ s : Randomness d, Set.indicator {ω : Data d | j + 1 ≤ U ω n y ∧ ω.2.1 (y, j) = x}
          (fun _ => (1 : ℝ)) ((η, s) : Data d) ∂(stackRankLaw d)
        = kern d y x * probGiven d η {ω : Data d | j + 1 ≤ U ω n y} := by
    intro j
    exact deferred_factorization hd n y x j η
  simp only [hj, ← Finset.mul_sum]
  congr 1
  have hsum : ∀ s : Randomness d, ∑ j ∈ Finset.range M,
      Set.indicator {ω : Data d | j + 1 ≤ U ω n y} (fun _ => (1 : ℝ)) ((η, s) : Data d)
      = (U ((η, s) : Data d) n y : ℝ) := by
    intro s
    have hle : U ((η, s) : Data d) n y ≤ M := U_le_uBound ((η, s) : Data d) n y
    have : ∀ j ∈ Finset.range M,
        Set.indicator {ω : Data d | j + 1 ≤ U ω n y} (fun _ => (1 : ℝ)) ((η, s) : Data d)
          = if j < U ((η, s) : Data d) n y then (1 : ℝ) else 0 := by
      intro j _
      by_cases h1 : j + 1 ≤ U ((η, s) : Data d) n y
      · rw [Set.indicator_of_mem (show ((η, s) : Data d)
            ∈ {ω : Data d | j + 1 ≤ U ω n y} from h1),
          if_pos (show j < U ((η, s) : Data d) n y from h1)]
      · rw [Set.indicator_of_notMem (show ((η, s) : Data d)
            ∉ {ω : Data d | j + 1 ≤ U ω n y} from h1),
          if_neg (show ¬ j < U ((η, s) : Data d) n y from h1)]
    rw [Finset.sum_congr rfl this, Finset.sum_boole]
    have hfil : ((Finset.range M).filter fun j => j < U ((η, s) : Data d) n y)
        = Finset.range (U ((η, s) : Data d) n y) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le h hle, h⟩⟩
    rw [hfil, Finset.card_range]
  show ∑ j ∈ Finset.range M, (∫ s : Randomness d,
      Set.indicator {ω : Data d | j + 1 ≤ U ω n y} (fun _ => (1 : ℝ)) ((η, s) : Data d)
        ∂(stackRankLaw d)) = ∫ s, (U ((η, s) : Data d) n y : ℝ) ∂(stackRankLaw d)
  rw [← integral_finsetSum _ fun j _ =>
    integrable_indicator_U hd η _ (measurableSet_U_ge n y j)]
  exact integral_congr_ae (Filter.Eventually.of_forall hsum)

theorem integrable_arrivals (hd : 1 ≤ d) (η : Site d → ℤ) (n : ℕ) (y x : Site d) :
    Integrable (fun s : Randomness d => (arrivals s.1 y x (U ((η, s) : Data d) n y) : ℝ))
      (stackRankLaw d) := by
  refine Integrable.congr
    (integrable_finsetSum (Finset.range (uBound η n y)) fun j _ =>
      integrable_indicator_U hd η
        {ω : Data d | j + 1 ≤ U ω n y ∧ ω.2.1 (y, j) = x} (measurableSet_U_ge_and n y x j)) ?_
  exact Filter.Eventually.of_forall fun s => (arrivals_indicator_sum η n y x s).symm

theorem sum_kern_nbr (η : Site d → ℤ) (n : ℕ) (x : Site d) :
    ∑ y ∈ nbrFinset x, kern d y x * meanUgiven d η n y
      = walkOp (fun y => meanUgiven d η n y) x := by
  rw [walkOp_eq_nbrFinset, Finset.sum_div]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [kern, if_pos (nbrFinset_symm hy)]
  ring

/-- Jensen's inequality for the positive part, averaged over the instructions. -/
theorem meanUgiven_succ_ge (hd : 1 ≤ d) (η : Site d → ℤ) (n : ℕ) (x : Site d) :
    max 0 ((η x : ℝ) + walkOp (fun y => meanUgiven d η n y) x) ≤ meanUgiven d η (n + 1) x := by
  classical
  haveI : ∀ q : Site d × ℕ, IsProbabilityMeasure (instructionLaw (d := d) q.1) :=
    fun q => instructionLaw_isProbability hd q.1
  haveI := rankLaw_isProbability d
  haveI : IsProbabilityMeasure (stackRankLaw d) := by
    unfold stackRankLaw stackLaw; infer_instance
  set f : Randomness d → ℝ := fun s =>
    (η x : ℝ) + ∑ y ∈ nbrFinset x, (arrivals s.1 y x (U ((η, s) : Data d) n y) : ℝ) with hf
  have hfint : Integrable f (stackRankLaw d) :=
    (integrable_const _).add (integrable_finsetSum _ fun y _ => integrable_arrivals hd η n y x)
  have hae : ∀ᵐ s ∂(stackRankLaw d), ∀ q : Site d × ℕ, s.1 q ∈ nbrFinset q.1 :=
    (Measure.quasiMeasurePreserving_fst).ae (stackLaw_ae_nbr hd)
  have hUrw : ∀ᵐ s ∂(stackRankLaw d),
      (U ((η, s) : Data d) (n + 1) x : ℝ) = max 0 (f s) := by
    refine hae.mono fun s hs => ?_
    exact U_succ_real (ω := ((η, s) : Data d)) hs n x
  have hint1 : ∫ s, f s ∂(stackRankLaw d)
      = (η x : ℝ) + walkOp (fun y => meanUgiven d η n y) x := by
    rw [hf, integral_add (integrable_const _)
      (integrable_finsetSum _ fun y _ => integrable_arrivals hd η n y x),
      integral_finsetSum _ fun y _ => integrable_arrivals hd η n y x]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [Finset.sum_congr rfl fun y _ => meanUgiven_arrivals hd η n y x, sum_kern_nbr]
  have hmaxint : Integrable (fun s => max 0 (f s)) (stackRankLaw d) :=
    (hfint.sup (integrable_const 0)).congr (Filter.Eventually.of_forall fun s => by
      simp [max_comm])
  have hUint : Integrable (fun s : Randomness d => (U ((η, s) : Data d) (n + 1) x : ℝ))
      (stackRankLaw d) := integrable_Ugiven hd η (n + 1) x
  have hkey : meanUgiven d η (n + 1) x = ∫ s, max 0 (f s) ∂(stackRankLaw d) := by
    show ∫ s, (U ((η, s) : Data d) (n + 1) x : ℝ) ∂(stackRankLaw d) = _
    exact integral_congr_ae hUrw
  rw [hkey, ← hint1]
  refine max_le ?_ ?_
  · exact integral_nonneg fun s => le_max_left _ _
  · exact integral_mono hfint hmaxint fun s => le_max_right _ _

/-- Theorem 4.1: the divisible odometer is below the averaged particle
odometer. -/
theorem comparison_of_labelOrder (hd : 1 ≤ d) (η : Site d → ℤ) (n : ℕ) (x : Site d) :
    u (fun y => ((η y : ℤ) : ℝ)) n x ≤ meanUgiven d η n x := by
  induction n generalizing x with
  | zero =>
      have h0 : ∀ s : Randomness d, (U ((η, s) : Data d) 0 x : ℝ) = 0 := fun s => by
        norm_num
      show (0 : ℝ) ≤ ∫ s, (U ((η, s) : Data d) 0 x : ℝ) ∂(stackRankLaw d)
      rw [integral_congr_ae (Filter.Eventually.of_forall h0)]
      simp
  | succ n ih =>
      refine le_trans ?_ (meanUgiven_succ_ge hd η n x)
      show max 0 ((η x : ℝ) + walkOp (u (fun y => ((η y : ℤ) : ℝ)) n) x) ≤ _
      refine max_le_max (le_refl 0) ?_
      have := walkOp_mono hd (fun y => ih y) x
      linarith

end Parking

end
