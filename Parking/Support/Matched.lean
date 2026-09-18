/-
Particles coupled by matching their departure ranks at each site. A round has
fresh site tables; each configuration reads an initial segment at its site.
The construction is measurable, and its received directions drive an ordinary
particle process pathwise.
-/
import Parking.Support.Agree
import Parking.Support.Coupling

noncomputable section

open MeasureTheory LatticeProb

variable {d : ℕ}

/-- A round has one table at each site, together with unused directions for
labels that do not depart. -/
abbrev Parking.RoundSlot (d : ℕ) := (LatticeProb.Site d × ℕ) ⊕ LatticeProb.Label d

abbrev Parking.RoundNoise (d : ℕ) := ℕ → Parking.RoundSlot d → Fin d × Bool

/-- The active labels available for matching at a site. -/
def Parking.matchActive (η : Site d → ℤ) (S : State d) (t : ℕ) (x : Site d) :
    Finset (Label d) :=
  (candidates η x t).filter fun p => S.active p ∧ S.pos p = x

/-- Priorities order the matching; the label order resolves ties. -/
def Parking.matchKey (ρ : Label d × ℕ → ℝ) (t : ℕ) (p : Label d) :
    Lex (ℝ × Lex (Lex (Fin d → ℤ) × ℕ)) := toLex (ρ (p, t), labelKey p)

theorem Parking.matchKey_injective (ρ : Label d × ℕ → ℝ) (t : ℕ) :
    Function.Injective (Parking.matchKey ρ t) := by
  intro p q hpq
  exact labelKey_injective (congrArg Prod.snd (toLex_inj.mp hpq))

/-- Departures use consecutive entries of the round's table at their site. -/
def Parking.matchSlot (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (S : State d) (t : ℕ) (p : Label d) : Parking.RoundSlot d :=
  if p ∈ Parking.matchActive η S t (S.pos p) then
    Sum.inl (S.pos p,
      rankIn (Parking.matchActive η S t (S.pos p)) (Parking.matchKey ρ t) p)
  else Sum.inr p

theorem Parking.matchSlot_injective (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (S : State d) (t : ℕ) : Function.Injective (Parking.matchSlot η ρ S t) := by
  classical
  intro p q hpq
  unfold Parking.matchSlot at hpq
  split_ifs at hpq with hp hq hq
  · have heq := Sum.inl_injective hpq
    have hpos : S.pos p = S.pos q := congrArg Prod.fst heq
    have hrank := congrArg Prod.snd heq
    rw [← hpos] at hq hrank
    exact rankIn_injOn (Parking.matchKey_injective ρ t).injOn hp hq hrank
  · exact Sum.inr_injective hpq

theorem Parking.matchSlot_of_mem (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (S : State d) (t : ℕ) (x : Site d) {p : Label d}
    (hp : p ∈ Parking.matchActive η S t x) :
    Parking.matchSlot η ρ S t p =
      Sum.inl (x, rankIn (Parking.matchActive η S t x) (Parking.matchKey ρ t) p) := by
  classical
  have hpos : S.pos p = x := (Finset.mem_filter.mp hp).2.2
  unfold Parking.matchSlot
  rw [hpos, if_pos hp]

/-- The entries used at a site are exactly its initial segment of active
counts. Thus two configurations share the first minimum count of entries. -/
theorem Parking.image_matchSlot (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (S : State d) (t : ℕ) (x : Site d) :
    (Parking.matchActive η S t x).image (Parking.matchSlot η ρ S t) =
      (Finset.range (Parking.matchActive η S t x).card).image
        (fun j => (Sum.inl (x, j) : Parking.RoundSlot d)) := by
  classical
  rw [← image_rankIn (Parking.matchKey_injective ρ t).injOn, Finset.image_image]
  exact Finset.image_congr fun p hp => Parking.matchSlot_of_mem η ρ S t x hp

/-- A driver for a single round using the common tables. -/
def Parking.matchDriver (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (S : State d) : Parking.PDriver d :=
  ⟨η, (fun q => σ q.2 (Parking.matchSlot η ρ S q.2 q.1)), ρ⟩

/-- Two configurations run with this same noise take a common step for every
matched pair at a site. -/
def Parking.matchedState (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) : ℕ → State d
  | 0 => initial η
  | t + 1 => Parking.pStep
      (Parking.matchDriver η ρ σ (Parking.matchedState η ρ σ t))
      (Parking.matchedState η ρ σ t) t

/-- The directions received by each physical particle in the common-table
construction. -/
def Parking.matchedMoves (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (q : Label d × ℕ) : Fin d × Bool :=
  σ q.2 (Parking.matchSlot η ρ (Parking.matchedState η ρ σ q.2) q.2 q.1)

/-- A round depends on the moves of that round only. -/
theorem Parking.pStep_congr_moves (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (m m' : Label d × ℕ → Fin d × Bool) (S : State d) (t : ℕ)
    (h : ∀ p, m (p, t) = m' (p, t)) :
    Parking.pStep ⟨η, m, ρ⟩ S t = Parking.pStep ⟨η, m', ρ⟩ S t := by
  have hn : ∀ p, Parking.pNextPos ⟨η, m, ρ⟩ S t p =
      Parking.pNextPos ⟨η, m', ρ⟩ S t p := by
    intro p
    simp only [Parking.pNextPos, h p]
  have ha : ∀ x, Parking.pArrivalsAt ⟨η, m, ρ⟩ S t x =
      Parking.pArrivalsAt ⟨η, m', ρ⟩ S t x := by
    intro x
    simp only [Parking.pArrivalsAt, hn]
  have hs : ∀ p, Parking.pSettles ⟨η, m, ρ⟩ S t p =
      Parking.pSettles ⟨η, m', ρ⟩ S t p := by
    intro p
    simp only [Parking.pSettles, hn, ha]
  simp only [Parking.pStep, ha, hs, funext hn]
  rfl

theorem Parking.pState_congr_moves (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (m m' : Label d × ℕ → Fin d × Bool) (t : ℕ)
    (h : ∀ s < t, ∀ p, m (p, s) = m' (p, s)) :
    Parking.pState ⟨η, m, ρ⟩ t = Parking.pState ⟨η, m', ρ⟩ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Parking.pState, Parking.pState, ih (fun s hs => h s (by omega))]
      exact Parking.pStep_congr_moves η ρ m m' _ t (h t (by omega))

/-- The common-table state is an ordinary particle process driven by its
received directions, pathwise and at every horizon. -/
theorem Parking.pState_matchedMoves (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (t : ℕ) :
    Parking.pState ⟨η, Parking.matchedMoves η ρ σ, ρ⟩ t =
      Parking.matchedState η ρ σ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Parking.pState, ih, Parking.matchedState]
      exact Parking.pStep_congr_moves η ρ _ _ _ t fun _ => rfl

/-- A state after `t` rounds is unchanged when an input layer at or beyond
round `t` is replaced, including all of that layer at once. -/
theorem Parking.matchedState_congr (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ σ' : Parking.RoundNoise d) (t : ℕ) (h : ∀ s < t, σ s = σ' s) :
    Parking.matchedState η ρ σ t = Parking.matchedState η ρ σ' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Parking.matchedState, Parking.matchedState, ih (fun s hs => h s (by omega))]
      exact Parking.pStep_congr_moves η ρ _ _ _ t fun p =>
        congrFun (h t (by omega)) _

theorem Parking.matchedState_update (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (n t : ℕ) (v : Parking.RoundSlot d → Fin d × Bool)
    (ht : t ≤ n) :
    Parking.matchedState η ρ (Function.update σ n v) t =
      Parking.matchedState η ρ σ t :=
  Parking.matchedState_congr η ρ _ _ t fun s hs =>
    Function.update_of_ne (by omega) _ _

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Measurability of all four fields of a state-valued function. -/
def Parking.MeasurableState (S : Ω → State d) : Prop :=
  (∀ p, Measurable fun ω => (S ω).active p) ∧
  (∀ p, Measurable fun ω => (S ω).pos p) ∧
  (∀ x, Measurable fun ω => (S ω).holes x) ∧
  (∀ x, Measurable fun ω => (S ω).departures x)

theorem Parking.measurableState_pState (e : Ω → Site d → ℤ)
    (m : Ω → Label d × ℕ → Fin d × Bool) (r : Ω → Label d × ℕ → ℝ)
    (he : Measurable e) (hm : Measurable m) (hr : Measurable r) (t : ℕ) :
    Parking.MeasurableState (fun ω => Parking.pState ⟨e ω, m ω, r ω⟩ t) := by
  have hvec : Measurable (Parking.stepVec (d := d)) := measurable_from_countable' _
  let T : Ω → LatticeProb.PData d := fun ω =>
    (e ω, (fun q => Parking.stepVec (m ω q)), r ω)
  have hT : Measurable T := he.prodMk
    ((measurable_pi_lambda _ fun q => hvec.comp ((measurable_pi_apply q).comp hm)).prodMk hr)
  have hst : (fun ω => Parking.pState ⟨e ω, m ω, r ω⟩ t) =
      fun ω => LatticeProb.pState (LatticeProb.toPDriver (T ω)) t :=
    funext fun ω => Parking.pState_stepVec (e ω) (m ω) (r ω) t
  rw [hst]
  have h := Parking.measurable_pState (d := d) t
  exact ⟨fun p => (h.1 p).comp hT, fun p => (h.2.1 p).comp hT,
    fun x => (h.2.2.1 x).comp hT, fun x => (h.2.2.2 x).comp hT⟩

theorem Parking.measurable_matchActive (e : Ω → Site d → ℤ)
    (S : Ω → State d) (he : Measurable e) (hS : Parking.MeasurableState S)
    (t : ℕ) (x : Site d) :
    Measurable fun ω => Parking.matchActive (e ω) (S ω) t x := by
  classical
  apply measurable_finset_iff.mpr
  intro p
  simp only [Parking.matchActive, Finset.mem_filter, mem_candidates_iff]
  have ha := hS.1 p
  have hp := hS.2.1 p
  fun_prop

theorem Parking.measurable_matchSlot (e : Ω → Site d → ℤ)
    (r : Ω → Label d × ℕ → ℝ) (S : Ω → State d)
    (he : Measurable e) (hr : Measurable r) (hS : Parking.MeasurableState S)
    (t : ℕ) (p : Label d) :
    Measurable fun ω => Parking.matchSlot (e ω) (r ω) (S ω) t p := by
  classical
  have hA := Parking.measurable_matchActive e S he hS t
  have hAv : Measurable fun ω => Parking.matchActive (e ω) (S ω) t ((S ω).pos p) :=
    Parking.measurable_eval_var _ (hS.2.1 p) _ hA
  have hRv : Measurable fun ω =>
      rankIn (Parking.matchActive (e ω) (S ω) t ((S ω).pos p))
        (Parking.matchKey (r ω) t) p := by
    refine Parking.measurable_eval_var (fun ω => (S ω).pos p) (hS.2.1 p)
      (fun ω x => rankIn (Parking.matchActive (e ω) (S ω) t x)
        (Parking.matchKey (r ω) t) p) fun x => ?_
    have hfilter : Measurable fun ω => (Parking.matchActive (e ω) (S ω) t x).filter
        (fun q => Parking.matchKey (r ω) t q < Parking.matchKey (r ω) t p) := by
      apply measurable_finset_iff.mpr
      intro q
      simp only [Finset.mem_filter, Parking.matchKey, Prod.Lex.toLex_lt_toLex]
      have hmem := (measurable_finset_mem q).comp (hA x)
      fun_prop
    exact (measurable_from_countable' (Finset.card (α := Label d))).comp hfilter
  unfold Parking.matchSlot
  exact Measurable.ite (hAv (measurableSet_mem_finset p))
    (measurable_inl.comp ((hS.2.1 p).prodMk hRv)) measurable_const

/-- The construction is measurable jointly in the configuration, priorities,
and instruction tables. The proof only reads finitely many time layers. -/
theorem Parking.measurableState_matchedState (i₀ : Fin d) (e : Ω → Site d → ℤ)
    (r : Ω → Label d × ℕ → ℝ) (σ : Ω → Parking.RoundNoise d)
    (he : Measurable e) (hr : Measurable r) (hσ : Measurable σ) (t : ℕ) :
    Parking.MeasurableState (fun ω => Parking.matchedState (e ω) (r ω) (σ ω) t) := by
  classical
  induction t using Nat.strong_induction_on with
  | _ t ih =>
      let m : Ω → Label d × ℕ → Fin d × Bool := fun ω q =>
        if q.2 < t then Parking.matchedMoves (e ω) (r ω) (σ ω) q else (i₀, false)
      have hm : Measurable m := by
        refine measurable_pi_lambda _ fun q => ?_
        dsimp [m]
        by_cases hqt : q.2 < t
        · simp only [if_pos hqt]
          exact Parking.measurable_eval_var
            (fun ω => Parking.matchSlot (e ω) (r ω)
              (Parking.matchedState (e ω) (r ω) (σ ω) q.2) q.2 q.1)
            (Parking.measurable_matchSlot e r _ he hr (ih q.2 hqt) q.2 q.1)
            (fun ω j => σ ω q.2 j)
            (fun j => (measurable_pi_apply j).comp ((measurable_pi_apply q.2).comp hσ))
        · simp only [if_neg hqt]
          exact measurable_const
      have hst : (fun ω => Parking.matchedState (e ω) (r ω) (σ ω) t) =
          fun ω => Parking.pState ⟨e ω, m ω, r ω⟩ t := by
        funext ω
        rw [← Parking.pState_matchedMoves]
        exact Parking.pState_congr_moves _ _ _ _ t fun s hs p => by simp [m, hs]
      rw [hst]
      exact Parking.measurableState_pState e m r he hm hr t

theorem Parking.measurable_matchedMoves (i₀ : Fin d) (e : Ω → Site d → ℤ)
    (r : Ω → Label d × ℕ → ℝ) (σ : Ω → Parking.RoundNoise d)
    (he : Measurable e) (hr : Measurable r) (hσ : Measurable σ) :
    Measurable fun ω => Parking.matchedMoves (e ω) (r ω) (σ ω) := by
  refine measurable_pi_lambda _ fun q => ?_
  exact Parking.measurable_eval_var _
    (Parking.measurable_matchSlot e r _ he hr
      (Parking.measurableState_matchedState i₀ e r σ he hr hσ q.2) q.2 q.1)
    (fun ω j => σ ω q.2 j)
    (fun j => (measurable_pi_apply j).comp ((measurable_pi_apply q.2).comp hσ))

/-- Fresh, independent instruction tables, indexed by the round. -/
def Parking.roundNoiseLaw (d : ℕ) : Measure (Parking.RoundNoise d) :=
  Measure.infinitePi fun _ : ℕ =>
    Measure.infinitePi fun _ : Parking.RoundSlot d => Parking.stepLaw d

theorem Parking.roundNoiseLaw_isProbability (hd : 1 ≤ d) :
    IsProbabilityMeasure (Parking.roundNoiseLaw d) := by
  haveI := Parking.stepLaw_isProbability hd
  unfold Parking.roundNoiseLaw
  infer_instance

end
