import Parking.Support.DVTrials

/-!
# The trials succeed often

Each present trial succeeds with conditional probability at least `p₀`, by the strong Markov
property at the trial time (`LatticeProb.markov_stopping_family`) and the hitting estimate
`Parking.exists_hit_prob_ge`: at a present trial time the walk stands in a box with more than
`δ m^d` unvisited sites.  Hence, for `q = (1 - e^{-1}) p₀`, the products

  `∏_{i < J} exp(q 1{trial π + 2i present} - 1{trial π + 2i succeeds})`

have expectation at most one (`integral_trialProd_le_one`), and by Markov's inequality

  `P(at least N present trials and at most S successes) ≤ e^{S - q N}`

(`measureReal_present_success_le`).  The trials `π, π + 2, …` are used, so that each trial is
over before the next one starts.
-/

noncomputable section

namespace Parking

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- A function of the first `n + 1` positions of two paths is measurable. -/
theorem measurable_of_dependsUpTo₂ {n : ℕ} {F : (ℕ → Site d) × (ℕ → Site d) → ℝ}
    (hF : ∀ X X' Y Y' : ℕ → Site d, (∀ i ≤ n, X i = X' i) → (∀ i ≤ n, Y i = Y' i) →
      F (X, Y) = F (X', Y')) :
    Measurable F := by
  classical
  set r : (ℕ → Site d) × (ℕ → Site d) → (Fin (n + 1) → Site d) × (Fin (n + 1) → Site d) :=
    fun p => (fun i => p.1 i, fun i => p.2 i)
  set g : (Fin (n + 1) → Site d) × (Fin (n + 1) → Site d) → ℝ :=
    fun q => F (fun k => if h : k < n + 1 then q.1 ⟨k, h⟩ else 0,
      fun k => if h : k < n + 1 then q.2 ⟨k, h⟩ else 0)
  have hfact : F = g ∘ r := by
    funext p
    simp only [Function.comp, g, r]
    exact hF _ _ _ _ (fun k hk => by rw [dite_eq_left (by omega)])
      (fun k hk => by rw [dite_eq_left (by omega)])
  rw [hfact]
  refine (measurable_of_countable g).comp ?_
  exact (Measurable.of_eval fun i => (measurable_pi_apply _).comp measurable_fst).prodMk
    (Measurable.of_eval fun i => (measurable_pi_apply _).comp measurable_snd)

section Weights

variable (m : ℕ) [NeZero m] (δ : ℝ) (ℓ : ℕ)

open scoped Classical in
/-- `exp(q 1{present} - 1{success})` for the trial of block `k`. -/
def trialWeight (q : ℝ) (k : ℕ) (X : ℕ → Site d) : ℝ :=
  Real.exp (q * (if Present m δ ℓ k X then 1 else 0) - (if Success m δ ℓ k X then 1 else 0))

/-- The product of the weights of the trials `π + 2i`, `i < J`. -/
def trialProd (q : ℝ) (π J : ℕ) (X : ℕ → Site d) : ℝ :=
  ∏ i ∈ Finset.range J, trialWeight m δ ℓ q (π + 2 * i) X

end Weights

variable {m : ℕ} [NeZero m] {δ : ℝ} {ℓ : ℕ}

theorem trialWeight_pos (q : ℝ) (k : ℕ) (X : ℕ → Site d) : 0 < trialWeight m δ ℓ q k X :=
  Real.exp_pos _

theorem trialWeight_le (q : ℝ) (hq : 0 ≤ q) (k : ℕ) (X : ℕ → Site d) :
    trialWeight m δ ℓ q k X ≤ Real.exp q := by
  classical
  unfold trialWeight
  refine Real.exp_le_exp.mpr ?_
  split_ifs <;> linarith

theorem trialProd_pos (q : ℝ) (π J : ℕ) (X : ℕ → Site d) : 0 < trialProd m δ ℓ q π J X :=
  Finset.prod_pos fun _ _ => trialWeight_pos q _ X

theorem trialProd_le (q : ℝ) (hq : 0 ≤ q) (π J : ℕ) (X : ℕ → Site d) :
    trialProd m δ ℓ q π J X ≤ Real.exp q ^ J := by
  unfold trialProd
  calc ∏ i ∈ Finset.range J, trialWeight m δ ℓ q (π + 2 * i) X
      ≤ ∏ _i ∈ Finset.range J, Real.exp q :=
        Finset.prod_le_prod₀ (fun _ _ => (trialWeight_pos q _ X).le)
          fun _ _ => trialWeight_le q hq _ X
    _ = Real.exp q ^ J := by rw [Finset.prod_const, Finset.card_range]

/-- The trial of block `k` is decided by the first `(k + 2) ℓ + 1` positions. -/
theorem trialWeight_congr (q : ℝ) (k : ℕ) {X Y : ℕ → Site d}
    (h : ∀ i ≤ (k + 2) * ℓ, X i = Y i) :
    trialWeight m δ ℓ q k X = trialWeight m δ ℓ q k Y := by
  classical
  have hτ : trialTime m δ ℓ k X = trialTime m δ ℓ k Y :=
    trialTime_congr fun i hi => h i (le_trans hi (by nlinarith))
  have hτle := trialTime_le (m := m) (δ := δ) (ℓ := ℓ) (k := k) X
  have hP : Present m δ ℓ k X ↔ Present m δ ℓ k Y := by
    unfold Present; rw [hτ]
  have hS : Success m δ ℓ k X ↔ Success m δ ℓ k Y := by
    unfold Success
    rw [hP, ← hτ]
    have hR : rangeSet X (trialTime m δ ℓ k X) = rangeSet Y (trialTime m δ ℓ k X) :=
      rangeSet_congr fun i hi => h i (by nlinarith)
    have hXτ : X (trialTime m δ ℓ k X) = Y (trialTime m δ ℓ k X) := h _ (by nlinarith)
    rw [hR, hXτ]
    constructor
    · rintro ⟨hp, a, ha1, ha2, hmem⟩
      refine ⟨hp, a, ha1, ha2, ?_⟩
      rwa [← h (trialTime m δ ℓ k X + a) (by nlinarith)]
    · rintro ⟨hp, a, ha1, ha2, hmem⟩
      refine ⟨hp, a, ha1, ha2, ?_⟩
      rwa [h (trialTime m δ ℓ k X + a) (by nlinarith)]
  unfold trialWeight
  simp only [hP, hS]

theorem trialProd_congr (q : ℝ) (π J : ℕ) {X Y : ℕ → Site d}
    (h : ∀ i ≤ (π + 2 * J) * ℓ, X i = Y i) :
    trialProd m δ ℓ q π J X = trialProd m δ ℓ q π J Y := by
  unfold trialProd
  refine Finset.prod_congr rfl fun i hi => trialWeight_congr q _ fun a ha => h a ?_
  have hi' := Finset.mem_range.mp hi
  have : (π + 2 * i + 2) * ℓ ≤ (π + 2 * J) * ℓ := Nat.mul_le_mul_right ℓ (by omega)
  omega

theorem measurable_trialProd (q : ℝ) (π J : ℕ) :
    Measurable (trialProd (d := d) m δ ℓ q π J) :=
  measurable_of_dependsUpTo (n := (π + 2 * J) * ℓ) fun _ _ h => trialProd_congr q π J h

theorem trialProd_succ (q : ℝ) (π J : ℕ) (X : ℕ → Site d) :
    trialProd m δ ℓ q π (J + 1) X = trialProd m δ ℓ q π J X * trialWeight m δ ℓ q (π + 2 * J) X :=
  Finset.prod_range_succ _ _

/-! ### One step of the supermartingale -/

variable (m δ ℓ) in
/-- Within `ℓ` steps the path `Y` visits a site of the box of `X_j` not visited by `X` up to
time `j`. -/
def HitAfter (X : ℕ → Site d) (j : ℕ) (Y : ℕ → Site d) : Prop :=
  ∃ a, 1 ≤ a ∧ a ≤ ℓ ∧ Y a ∈ boxCell m (fullSplit m (X j)).1 \ rangeSet X j

open scoped Classical in
variable (m δ ℓ) in
/-- The product up to the trial `π + 2J`, with the weight of that trial computed for a trial
time `j` and a future path `Y`. -/
def trialStep (q : ℝ) (π J j : ℕ) (X Y : ℕ → Site d) : ℝ :=
  if (π + 2 * J) * ℓ ≤ j then trialProd m δ ℓ q π J X *
    Real.exp (q * (if j < (π + 2 * J + 1) * ℓ then 1 else 0)
      - (if j < (π + 2 * J + 1) * ℓ ∧ HitAfter m ℓ X j Y then 1 else 0)) else 0

theorem hitAfter_congr {X X' Y Y' : ℕ → Site d} {j : ℕ} (hX : ∀ i ≤ j, X i = X' i)
    (hY : ∀ i ≤ ℓ, Y i = Y' i) : HitAfter m ℓ X j Y ↔ HitAfter m ℓ X' j Y' := by
  unfold HitAfter
  rw [rangeSet_congr hX, hX j le_rfl]
  constructor
  · rintro ⟨a, ha1, ha2, hmem⟩
    exact ⟨a, ha1, ha2, by rwa [← hY a ha2]⟩
  · rintro ⟨a, ha1, ha2, hmem⟩
    exact ⟨a, ha1, ha2, by rwa [hY a ha2]⟩

theorem trialStep_congr (q : ℝ) (π J j : ℕ) {X X' Y Y' : ℕ → Site d}
    (hX : ∀ i ≤ j, X i = X' i) (hY : ∀ i ≤ ℓ, Y i = Y' i) :
    trialStep m δ ℓ q π J j X Y = trialStep m δ ℓ q π J j X' Y' := by
  classical
  unfold trialStep
  by_cases h1 : (π + 2 * J) * ℓ ≤ j
  · rw [ite_eq_left h1, ite_eq_left h1, trialProd_congr q π J fun i hi => hX i (le_trans hi h1),
      hitAfter_congr hX hY]
  · rw [ite_eq_right h1, ite_eq_right h1]

theorem trialStep_nonneg (q : ℝ) (π J j : ℕ) (X Y : ℕ → Site d) :
    0 ≤ trialStep m δ ℓ q π J j X Y := by
  classical
  unfold trialStep
  by_cases h1 : (π + 2 * J) * ℓ ≤ j
  · rw [ite_eq_left h1]
    exact (mul_pos (trialProd_pos q π J X) (Real.exp_pos _)).le
  · rw [ite_eq_right h1]

theorem trialStep_le (q : ℝ) (hq : 0 ≤ q) (π J j : ℕ) (X Y : ℕ → Site d) :
    trialStep m δ ℓ q π J j X Y ≤ Real.exp q ^ J * Real.exp q := by
  classical
  unfold trialStep
  by_cases h1 : (π + 2 * J) * ℓ ≤ j
  · rw [ite_eq_left h1]
    have hexp : Real.exp (q * (if j < (π + 2 * J + 1) * ℓ then 1 else 0)
        - (if j < (π + 2 * J + 1) * ℓ ∧ HitAfter m ℓ X j Y then 1 else 0)) ≤ Real.exp q :=
      Real.exp_le_exp.mpr (by split_ifs <;> linarith)
    exact mul_le_mul (trialProd_le q hq π J X) hexp (Real.exp_pos _).le
      (pow_nonneg (Real.exp_pos _).le _)
  · rw [ite_eq_right h1]
    exact mul_nonneg (pow_nonneg (Real.exp_pos _).le _) (Real.exp_pos _).le

theorem trialStep_trialTime (q : ℝ) (π J : ℕ) (X : ℕ → Site d) :
    trialStep m δ ℓ q π J (trialTime m δ ℓ (π + 2 * J) X) X
        (shiftPath (trialTime m δ ℓ (π + 2 * J) X) X)
      = trialProd m δ ℓ q π (J + 1) X := by
  classical
  have hlow := (trialTime_spec (m := m) (δ := δ) (ℓ := ℓ) (k := π + 2 * J) X).1
  unfold trialStep
  rw [ite_eq_left hlow, trialProd_succ]
  congr 1
  unfold trialWeight
  by_cases hP : Present m δ ℓ (π + 2 * J) X
  · have hP' : trialTime m δ ℓ (π + 2 * J) X < (π + 2 * J + 1) * ℓ := hP
    by_cases hS : Success m δ ℓ (π + 2 * J) X
    · have hS' : HitAfter m ℓ X (trialTime m δ ℓ (π + 2 * J) X)
          (shiftPath (trialTime m δ ℓ (π + 2 * J) X) X) := hS.2
      simp [hP, hP', hS, hS']
    · have hS' : ¬ HitAfter m ℓ X (trialTime m δ ℓ (π + 2 * J) X)
          (shiftPath (trialTime m δ ℓ (π + 2 * J) X) X) := fun h => hS ⟨hP, h⟩
      simp [hP, hP', hS, hS']
  · have hP' : ¬ trialTime m δ ℓ (π + 2 * J) X < (π + 2 * J + 1) * ℓ := hP
    have hS : ¬ Success m δ ℓ (π + 2 * J) X := fun h => hP h.1
    simp [hP, hP', hS]



/-- At a present trial time the next trial succeeds with probability at least `p₀`, so the
conditional expectation of the new weight is at most one. -/
theorem integral_trialStep_le (hd : 1 ≤ d) {p₀ : ℝ} (hℓ : ℓ = 2 * m ^ 2)
    (hhit : ∀ (z y : Site d), y ∈ boxCell m z → ∀ A : Finset (Site d), A ⊆ boxCell m z →
      δ * (m : ℝ) ^ d ≤ A.card →
        p₀ ≤ (siteWalkLaw d y).real {Y | ∃ j, 1 ≤ j ∧ j ≤ 2 * m ^ 2 ∧ Y j ∈ A})
    (π J : ℕ) (X : ℕ → Site d) :
    ∫ Y, trialStep m δ ℓ ((1 - Real.exp (-1)) * p₀) π J (trialTime m δ ℓ (π + 2 * J) X) X Y
        ∂(siteWalkLaw d (X (trialTime m δ ℓ (π + 2 * J) X)))
      ≤ trialProd m δ ℓ ((1 - Real.exp (-1)) * p₀) π J X := by
  classical
  have : NeZero d := ⟨by omega⟩
  set c := 1 - Real.exp (-1) with hc
  have hc0 : 0 < c := by
    rw [hc]; linarith [Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)]
  set q := c * p₀ with hq
  set k := π + 2 * J with hk
  set j := trialTime m δ ℓ k X with hj
  have hjlow : (π + 2 * J) * ℓ ≤ j := (trialTime_spec (m := m) (δ := δ) (ℓ := ℓ) (k := k) X).1
  have hTP := trialProd_pos (m := m) (δ := δ) (ℓ := ℓ) q π J X
  by_cases hpres : j < (π + 2 * J + 1) * ℓ
  · have hpor : Porous m δ X j := porous_trialTime X hpres
    set A := boxCell m (fullSplit m (X j)).1 \ rangeSet X j with hA
    have hAcard := card_sdiff_gt_of_porousFor hpor
    set H : Set (ℕ → Site d) := {Y | ∃ a, 1 ≤ a ∧ a ≤ 2 * m ^ 2 ∧ Y a ∈ A} with hH
    have hHiff : ∀ Y, HitAfter m ℓ X j Y ↔ Y ∈ H := by
      intro Y; simp only [HitAfter, hH, Set.mem_ofPred_eq, hℓ, hA]
    have hHm : MeasurableSet H := by
      have hmeas : Measurable fun Y : ℕ → Site d => H.indicator (fun _ => (1 : ℝ)) Y := by
        refine measurable_of_dependsUpTo (n := 2 * m ^ 2) fun Y Y' hY => ?_
        have hiff : Y ∈ H ↔ Y' ∈ H := by
          simp only [hH, Set.mem_ofPred_eq]
          constructor
          · rintro ⟨a, h1, h2, h3⟩; exact ⟨a, h1, h2, by rwa [← hY a h2]⟩
          · rintro ⟨a, h1, h2, h3⟩; exact ⟨a, h1, h2, by rwa [hY a h2]⟩
        by_cases hYm : Y ∈ H
        · rw [Set.indicator_of_mem hYm, Set.indicator_of_mem (hiff.mp hYm)]
        · rw [Set.indicator_of_notMem hYm, Set.indicator_of_notMem (fun h => hYm (hiff.mpr h))]
      have h1 := hmeas (measurableSet_singleton (1 : ℝ))
      convert h1 using 1
      ext Y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      by_cases hYm : Y ∈ H
      · simp [hYm]
      · simp [hYm]
    have hp := hhit (fullSplit m (X j)).1 (X j) (self_mem_boxCell m (X j)) A
      Finset.sdiff_subset hAcard.le
    have hfun : ∀ Y, trialStep m δ ℓ q π J j X Y = trialProd m δ ℓ q π J X * Real.exp q *
        (1 - c * H.indicator (fun _ => (1 : ℝ)) Y) := by
      intro Y
      unfold trialStep
      rw [ite_eq_left hjlow, ite_eq_left hpres, mul_one, mul_assoc]
      congr 1
      by_cases hY : Y ∈ H
      · rw [ite_eq_left ⟨hpres, (hHiff Y).mpr hY⟩, Set.indicator_of_mem hY, mul_one, hc,
          sub_sub_cancel, Real.exp_sub, Real.exp_neg, div_eq_mul_inv]
      · rw [ite_eq_right (fun h => hY ((hHiff Y).mp h.2)), Set.indicator_of_notMem hY]
        simp
    simp_rw [hfun]
    rw [integral_const_mul, integral_sub (integrable_const _)
      (((integrable_const (1 : ℝ)).indicator hHm).const_mul c), integral_const,
      integral_const_mul, integral_indicator_const _ hHm]
    simp only [probReal_univ, smul_eq_mul, mul_one]
    have hu : Real.exp q * (1 - c * p₀) ≤ 1 := by
      have h1 : 1 - c * p₀ ≤ Real.exp (-(c * p₀)) := by
        have := Real.add_one_le_exp (-(c * p₀)); linarith
      calc Real.exp q * (1 - c * p₀) ≤ Real.exp q * Real.exp (-(c * p₀)) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add, hq, add_neg_cancel, Real.exp_zero]
    have hstep : 1 - c * (siteWalkLaw d (X j)).real H ≤ 1 - c * p₀ := by
      have : c * p₀ ≤ c * (siteWalkLaw d (X j)).real H := mul_le_mul_of_nonneg_left hp hc0.le
      linarith
    calc trialProd m δ ℓ q π J X * Real.exp q * (1 - c * (siteWalkLaw d (X j)).real H)
        ≤ trialProd m δ ℓ q π J X * Real.exp q * (1 - c * p₀) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = trialProd m δ ℓ q π J X * (Real.exp q * (1 - c * p₀)) := by ring
      _ ≤ trialProd m δ ℓ q π J X * 1 := mul_le_mul_of_nonneg_left hu hTP.le
      _ = trialProd m δ ℓ q π J X := mul_one _
  · have hfun : ∀ Y, trialStep m δ ℓ q π J j X Y = trialProd m δ ℓ q π J X := by
      intro Y
      unfold trialStep
      rw [ite_eq_left hjlow, ite_eq_right hpres, ite_eq_right (fun h => hpres h.1)]
      simp
    simp_rw [hfun]
    rw [integral_const, probReal_univ, one_smul]

/-- **The expectation of the products is at most one.** -/
theorem integral_trialProd_le_one (hd : 1 ≤ d) {p₀ : ℝ} (hp₀ : 0 ≤ p₀)
    (hℓ : ℓ = 2 * m ^ 2)
    (hhit : ∀ (z y : Site d), y ∈ boxCell m z → ∀ A : Finset (Site d), A ⊆ boxCell m z →
      δ * (m : ℝ) ^ d ≤ A.card →
        p₀ ≤ (siteWalkLaw d y).real {Y | ∃ j, 1 ≤ j ∧ j ≤ 2 * m ^ 2 ∧ Y j ∈ A})
    (π J : ℕ) :
    ∫ X, trialProd m δ ℓ ((1 - Real.exp (-1)) * p₀) π J X ∂(siteWalkLaw d 0) ≤ 1 := by
  classical
  have : NeZero d := ⟨by omega⟩
  set q := (1 - Real.exp (-1)) * p₀ with hq
  have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (show (-1 : ℝ) < 0 by norm_num)
  have hq0 : 0 ≤ q := mul_nonneg (by linarith) hp₀
  induction J with
  | zero => simp [trialProd]
  | succ J ih =>
      have hτs : IsWalkStopping (trialTime (d := d) m δ ℓ (π + 2 * J)) :=
        isWalkStopping_trialTime
      have hτN : ∀ X, trialTime (d := d) m δ ℓ (π + 2 * J) X ≤ (π + 2 * J + 1) * ℓ :=
        fun X => trialTime_le X
      have hΦm : ∀ j, Measurable (Function.uncurry (trialStep (d := d) m δ ℓ q π J j)) :=
        fun j => measurable_of_dependsUpTo₂ (n := j + ℓ) fun X X' Y Y' hX hY =>
          trialStep_congr q π J j (fun i hi => hX i (by omega)) (fun i hi => hY i (by omega))
      have hΦb : ∀ j X Y, ‖trialStep (d := d) m δ ℓ q π J j X Y‖ ≤ Real.exp q ^ J * Real.exp q :=
        fun j X Y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (trialStep_nonneg q π J j X Y)]
          exact trialStep_le q hq0 π J j X Y
      have hpast : ∀ j X X' Y, (∀ i ≤ j, X i = X' i) →
          trialStep (d := d) m δ ℓ q π J j X Y = trialStep m δ ℓ q π J j X' Y :=
        fun j X X' Y hX => trialStep_congr q π J j hX fun _ _ => rfl
      have hmarkov := markov_stopping_family d ((π + 2 * J + 1) * ℓ) 0 _ hτs hτN _ hΦm hΦb hpast
      simp_rw [trialStep_trialTime] at hmarkov
      have hintJ : Integrable (trialProd m δ ℓ q π J) (siteWalkLaw d 0) := by
        refine Integrable.of_bound (measurable_trialProd q π J).aestronglyMeasurable
          (Real.exp q ^ J) (Filter.Eventually.of_forall fun X => ?_)
        rw [Real.norm_eq_abs, abs_of_pos (trialProd_pos q π J X)]
        exact trialProd_le q hq0 π J X
      rw [hmarkov]
      refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun X =>
        integral_nonneg fun Y => trialStep_nonneg _ _ _ _ _ _) hintJ
        (Filter.Eventually.of_forall fun X => integral_trialStep_le hd hℓ hhit π J X)) ih

end Parking

end
