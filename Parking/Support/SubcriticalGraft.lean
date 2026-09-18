/-
The pair `(F, Z)` of `thm:subcritical` with the particles at the origin
prescribed (`parking.tex:2434-2447`).

`graftSurvivalObs w r ω₁ t` and `graftHoleObs w ω₁ t` are the observables of
`Support/SubcriticalPair.lean` read at `graftOrigin ω₁ ω`: the origin carries the
prescribed particles with their prescribed walks and uniform variables, and
every other site is read off `ω`.  They are functions of the data at the sites
of the box OTHER than the origin, which is what `lem:product` asks once the
origin is held fixed, and they keep every other hypothesis of that lemma:

- the relabeling clauses come from `Support/GraftOrigin.lean`, the relabeling at
  the origin being erased by the graft and the relabeling elsewhere commuting
  with it;
- monotonicity in an added particle and the unit Lipschitz bounds are those of
  the ungrafted pair at every site other than the origin, and at the origin the
  observables do not move at all;
- `FZ = 0` is the ungrafted identity read at the grafted realization.
-/
import Parking.Support.GraftOrigin
import Parking.Support.SubcriticalInvariance
import Parking.Support.SubcriticalStep2

noncomputable section

namespace Parking

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- The box the two observables read, with the origin removed: the origin is not
random once its particles are prescribed. -/
def puncturedBox (d : ℕ) (t : ℕ) : Finset (Site d) :=
  (subcriticalBox d t).erase (0 : Site d)

theorem mem_puncturedBox_of_ne {t : ℕ} {x : Site d} (hx : x ≠ (0 : Site d))
    (h : x ∈ subcriticalBox d t) : x ∈ puncturedBox d t :=
  Finset.mem_erase.mpr ⟨hx, h⟩

/-- `F` with the particles at the origin prescribed. -/
def graftSurvivalObs (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) (ω₁ : PData d) (t : ℕ) :
    PData d → ℝ := fun ω => survivalObs w r t (graftOrigin ω₁ ω)

/-- `Z` with the particles at the origin prescribed. -/
def graftHoleObs (w : ℕ → Fin d × Bool) (ω₁ : PData d) (t : ℕ) : PData d → ℝ :=
  fun ω => holeObs w t (graftOrigin ω₁ ω)

theorem graftSurvivalObs_mem_Icc (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) (ω₁ : PData d)
    (t : ℕ) (ω : PData d) : graftSurvivalObs w r ω₁ t ω ∈ Set.Icc (0 : ℝ) 1 :=
  survivalObs_mem_Icc w r t _

theorem graftHoleObs_nonneg (w : ℕ → Fin d × Bool) (ω₁ : PData d) (t : ℕ) (ω : PData d) :
    0 ≤ graftHoleObs w ω₁ t ω := holeObs_nonneg w t _

theorem measurable_graftSurvivalObs (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) (ω₁ : PData d)
    (t : ℕ) : Measurable (graftSurvivalObs w r ω₁ t) :=
  (measurable_survivalObs w r t).comp (measurable_graftOrigin ω₁)

theorem measurable_graftHoleObs (w : ℕ → Fin d × Bool) (ω₁ : PData d) (t : ℕ) :
    Measurable (graftHoleObs w ω₁ t) :=
  (measurable_holeObs w t).comp (measurable_graftOrigin ω₁)

/-- The grafted realizations of two realizations agreeing off the origin agree
on the whole box. -/
theorem graftOrigin_agree {t : ℕ} {ω₁ ω ω' : PData d}
    (hc : ∀ x ∈ puncturedBox d t, ω.1 x = ω'.1 x)
    (hm : ∀ q : Label d × ℕ, q.1.1 ∈ puncturedBox d t → ω.2.1 q = ω'.2.1 q)
    (hr : ∀ q : Label d × ℕ, q.1.1 ∈ puncturedBox d t → ω.2.2 q = ω'.2.2 q) :
    (∀ x ∈ subcriticalBox d t, (graftOrigin ω₁ ω).1 x = (graftOrigin ω₁ ω').1 x) ∧
      (∀ q : Label d × ℕ, q.1.1 ∈ subcriticalBox d t →
        (graftOrigin ω₁ ω).2.1 q = (graftOrigin ω₁ ω').2.1 q) ∧
      (∀ q : Label d × ℕ, q.1.1 ∈ subcriticalBox d t →
        (graftOrigin ω₁ ω).2.2 q = (graftOrigin ω₁ ω').2.2 q) := by
  refine ⟨fun x hx => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · by_cases h0 : x = (0 : Site d)
    · rw [h0, graftOrigin_eta_zero, graftOrigin_eta_zero]
    · rw [graftOrigin_eta_of_ne h0, graftOrigin_eta_of_ne h0]
      exact hc x (mem_puncturedBox_of_ne h0 hx)
  · by_cases h0 : q.1.1 = (0 : Site d)
    · simp [graftOrigin, h0]
    · rw [graftOrigin_move_of_ne h0, graftOrigin_move_of_ne h0]
      exact hm q (mem_puncturedBox_of_ne h0 hq)
  · by_cases h0 : q.1.1 = (0 : Site d)
    · simp [graftOrigin, h0]
    · rw [graftOrigin_rank_of_ne h0, graftOrigin_rank_of_ne h0]
      exact hr q (mem_puncturedBox_of_ne h0 hq)

theorem dependsOn_graftSurvivalObs (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) (ω₁ : PData d)
    (t : ℕ) : DependsOn (puncturedBox d t) (graftSurvivalObs w r ω₁ t) := by
  intro ω ω' hc hm hr
  obtain ⟨h1, h2, h3⟩ := graftOrigin_agree (ω₁ := ω₁) hc hm hr
  exact dependsOn_survivalObs w r t _ _ h1 h2 h3

theorem dependsOn_graftHoleObs (w : ℕ → Fin d × Bool) (ω₁ : PData d) (t : ℕ) :
    DependsOn (puncturedBox d t) (graftHoleObs w ω₁ t) := by
  intro ω ω' hc hm hr
  obtain ⟨h1, h2, h3⟩ := graftOrigin_agree (ω₁ := ω₁) hc hm hr
  exact dependsOn_holeObs w t _ _ h1 h2 h3

/-- **`Z` with the origin prescribed is symmetric in the particles present.** -/
theorem symmetricInParticles_graftHoleObs (w : ℕ → Fin d × Bool) (ω₁ : PData d) (t : ℕ) :
    SymmetricInParticles (graftHoleObs (d := d) w ω₁ t) := by
  intro x₀ σ ω hinj hσ
  show holeObs w t (graftOrigin ω₁ (relabelAt x₀ σ ω)) = holeObs w t (graftOrigin ω₁ ω)
  by_cases hx₀ : x₀ = (0 : Site d)
  · subst hx₀
    rw [graftOrigin_relabelAt_zero]
  · rw [graftOrigin_relabelAt hx₀]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ))
      (pHoleCount_graft_relabelAt (ω₁ := ω₁) hx₀ hσ hinj t x)

/-- **`F` with the origin prescribed is symmetric in the particles present.** -/
theorem symmetricInParticles_graftSurvivalObs (w : ℕ → Fin d × Bool) (r : ℕ → ℝ)
    (ω₁ : PData d) (t : ℕ) : SymmetricInParticles (graftSurvivalObs (d := d) w r ω₁ t) := by
  classical
  intro x₀ σ ω hinj hσ
  show survivalObs w r t (graftOrigin ω₁ (relabelAt x₀ σ ω))
      = survivalObs w r t (graftOrigin ω₁ ω)
  by_cases hx₀ : x₀ = (0 : Site d)
  · subst hx₀
    rw [graftOrigin_relabelAt_zero]
  · rw [graftOrigin_relabelAt hx₀]
    unfold survivalObs
    have h := taggedActive_graft_relabelAt w r (ω₁ := ω₁) hx₀ hσ hinj t
    set S : Set (PData d) :=
      {ω : PData d | (pState (taggedDriver w r ω) t).active (0, 0) = true} with hS
    by_cases hmem : graftOrigin ω₁ ω ∈ S
    · have h1 : relabelAt x₀ σ (graftOrigin ω₁ ω) ∈ S := by
        rw [hS, Set.mem_setOf_eq, h]
        exact hmem
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem hmem]
    · have h1 : relabelAt x₀ σ (graftOrigin ω₁ ω) ∉ S := by
        rw [hS, Set.mem_setOf_eq, h]
        exact hmem
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem hmem]

/-- The survival indicator reads the particles present alone; this is the
statement of `Parking.readsParticles_survivalObs` without its two unused
distinctness hypotheses, which the grafted realization does not have. -/
theorem survivalObs_congr_present (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) (t : ℕ)
    {ω ω' : PData d} (hc : ω.1 = ω'.1)
    (hm : ∀ q : Label d × ℕ, q.1.2 < (ω.1 q.1.1).toNat → ω.2.1 q = ω'.2.1 q)
    (hr : ∀ q : Label d × ℕ, q.1.2 < (ω.1 q.1.1).toNat → ω.2.2 q = ω'.2.2 q) :
    survivalObs w r t ω = survivalObs w r t ω' := by
  classical
  unfold survivalObs
  have h : pState (taggedDriver w r ω) t = pState (taggedDriver w r ω') t :=
    pState_present (agreesOnPresent_taggedDriver w r hc hm hr) t
  set S : Set (PData d) := {ω : PData d | (pState (taggedDriver w r ω) t).active (0, 0) = true}
    with hS
  by_cases hmem : ω ∈ S
  · have h1 : ω' ∈ S := by
      rw [hS, Set.mem_setOf_eq, ← h]
      exact hmem
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem h1]
  · have h1 : ω' ∉ S := by
      rw [hS, Set.mem_setOf_eq, ← h]
      exact hmem
    rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem h1]

/-- Two realizations with the same counts agreeing at the particles present have
grafted realizations with the same counts agreeing at the particles present. -/
theorem graftOrigin_present {ω₁ ω ω' : PData d} (hc : ω.1 = ω'.1)
    (hm : ∀ q : Label d × ℕ, q.1.2 < (ω.1 q.1.1).toNat → ω.2.1 q = ω'.2.1 q)
    (hr : ∀ q : Label d × ℕ, q.1.2 < (ω.1 q.1.1).toNat → ω.2.2 q = ω'.2.2 q) :
    (graftOrigin ω₁ ω).1 = (graftOrigin ω₁ ω').1 ∧
      (∀ q : Label d × ℕ, q.1.2 < ((graftOrigin ω₁ ω).1 q.1.1).toNat →
        (graftOrigin ω₁ ω).2.1 q = (graftOrigin ω₁ ω').2.1 q) ∧
      (∀ q : Label d × ℕ, q.1.2 < ((graftOrigin ω₁ ω).1 q.1.1).toNat →
        (graftOrigin ω₁ ω).2.2 q = (graftOrigin ω₁ ω').2.2 q) := by
  have hcount : (graftOrigin ω₁ ω).1 = (graftOrigin ω₁ ω').1 := by
    funext x
    by_cases h0 : x = (0 : Site d)
    · rw [h0, graftOrigin_eta_zero, graftOrigin_eta_zero]
    · rw [graftOrigin_eta_of_ne h0, graftOrigin_eta_of_ne h0, hc]
  refine ⟨hcount, fun q hq => ?_, fun q hq => ?_⟩
  · by_cases h0 : q.1.1 = (0 : Site d)
    · simp [graftOrigin, h0]
    · rw [graftOrigin_move_of_ne h0, graftOrigin_move_of_ne h0]
      rw [graftOrigin_eta_of_ne h0] at hq
      exact hm q hq
  · by_cases h0 : q.1.1 = (0 : Site d)
    · simp [graftOrigin, h0]
    · rw [graftOrigin_rank_of_ne h0, graftOrigin_rank_of_ne h0]
      rw [graftOrigin_eta_of_ne h0] at hq
      exact hr q hq

theorem readsParticles_graftSurvivalObs (w : ℕ → Fin d × Bool) (r : ℕ → ℝ)
    (ω₁ : PData d) (t : ℕ) : ReadsParticles (graftSurvivalObs (d := d) w r ω₁ t) := by
  intro ω ω' _ _ hc hm hr
  obtain ⟨h1, h2, h3⟩ := graftOrigin_present (ω₁ := ω₁) hc hm hr
  exact survivalObs_congr_present w r t h1 h2 h3

theorem readsParticles_graftHoleObs (w : ℕ → Fin d × Bool) (ω₁ : PData d) (t : ℕ) :
    ReadsParticles (graftHoleObs (d := d) w ω₁ t) := by
  intro ω ω' _ _ hc hm hr
  obtain ⟨h1, h2, h3⟩ := graftOrigin_present (ω₁ := ω₁) hc hm hr
  show holeObs w t (graftOrigin ω₁ ω) = holeObs w t (graftOrigin ω₁ ω')
  unfold holeObs
  refine Finset.sum_congr rfl fun x _ => ?_
  exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (pHoleCount_reads h1 h2 h3 t x)

theorem relabelInvariant_graftSurvivalObs (w : ℕ → Fin d × Bool) (r : ℕ → ℝ)
    (ω₁ : PData d) (t : ℕ) : RelabelInvariant (graftSurvivalObs (d := d) w r ω₁ t) :=
  ⟨symmetricInParticles_graftSurvivalObs w r ω₁ t, readsParticles_graftSurvivalObs w r ω₁ t⟩

theorem relabelInvariant_graftHoleObs (w : ℕ → Fin d × Bool) (ω₁ : PData d) (t : ℕ) :
    RelabelInvariant (graftHoleObs (d := d) w ω₁ t) :=
  ⟨symmetricInParticles_graftHoleObs w ω₁ t, readsParticles_graftHoleObs w ω₁ t⟩

theorem graftSurvivalObs_mono (hd : 1 ≤ d) (w : ℕ → Fin d × Bool) (r : ℕ → ℝ)
    (ω₁ : PData d) (t : ℕ) (x₀ : Site d) (ω : PData d) :
    graftSurvivalObs w r ω₁ t ω ≤ graftSurvivalObs w r ω₁ t (addAt x₀ ω) := by
  show survivalObs w r t (graftOrigin ω₁ ω)
      ≤ survivalObs w r t (graftOrigin ω₁ (addAt x₀ ω))
  by_cases hx₀ : x₀ = (0 : Site d)
  · subst hx₀
    rw [graftOrigin_addAt_zero]
  · rw [graftOrigin_addAt hx₀]
    exact survivalObs_mono hd w r t x₀ (graftOrigin ω₁ ω)

theorem graftHoleObs_anti (hd : 1 ≤ d) (w : ℕ → Fin d × Bool) (ω₁ : PData d) (t : ℕ)
    (x₀ : Site d) (ω : PData d) :
    graftHoleObs w ω₁ t (addAt x₀ ω) ≤ graftHoleObs w ω₁ t ω := by
  show holeObs w t (graftOrigin ω₁ (addAt x₀ ω)) ≤ holeObs w t (graftOrigin ω₁ ω)
  by_cases hx₀ : x₀ = (0 : Site d)
  · subst hx₀
    rw [graftOrigin_addAt_zero]
  · rw [graftOrigin_addAt hx₀]
    exact holeObs_anti hd w t x₀ (graftOrigin ω₁ ω)

theorem graftHoleObs_add_lip (hd : 1 ≤ d) (w : ℕ → Fin d × Bool) (ω₁ : PData d) (t : ℕ)
    (x₀ : Site d) (ω : PData d) :
    |graftHoleObs w ω₁ t (addAt x₀ ω) - graftHoleObs w ω₁ t ω| ≤ 1 := by
  show |holeObs w t (graftOrigin ω₁ (addAt x₀ ω)) - holeObs w t (graftOrigin ω₁ ω)| ≤ 1
  by_cases hx₀ : x₀ = (0 : Site d)
  · subst hx₀
    rw [graftOrigin_addAt_zero, sub_self, abs_zero]
    norm_num
  · rw [graftOrigin_addAt hx₀]
    exact holeObs_add_lip hd w t x₀ (graftOrigin ω₁ ω)

theorem graftHoleObs_del_lip (hd : 1 ≤ d) (w : ℕ → Fin d × Bool) (ω₁ : PData d) (t : ℕ)
    (x₀ : Site d) (ω : PData d) :
    |graftHoleObs w ω₁ t (delAt x₀ ω) - graftHoleObs w ω₁ t ω| ≤ 1 := by
  show |holeObs w t (graftOrigin ω₁ (delAt x₀ ω)) - holeObs w t (graftOrigin ω₁ ω)| ≤ 1
  by_cases hx₀ : x₀ = (0 : Site d)
  · subst hx₀
    rw [graftOrigin_delAt_zero, sub_self, abs_zero]
    norm_num
  · rw [graftOrigin_delAt hx₀]
    exact holeObs_del_lip hd w t x₀ (graftOrigin ω₁ ω)

/-- **`FZ = 0` with the origin prescribed.** -/
theorem graftSurvivalObs_mul_graftHoleObs (w : ℕ → Fin d × Bool) (r : ℕ → ℝ)
    (ω₁ : PData d) (t : ℕ) (ω : PData d)
    (hinj : Function.Injective (taggedRank r (graftOrigin ω₁ ω).2.2)) :
    graftSurvivalObs w r ω₁ t ω * graftHoleObs w ω₁ t ω = 0 :=
  survivalObs_mul_holeObs_of_injective w r t (graftOrigin ω₁ ω) hinj

end Parking

end
