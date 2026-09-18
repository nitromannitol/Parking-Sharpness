/-
From the prescribed origin to the conditional survival probability
(`parking.tex:2419-2440`).

`thm:subcritical` bounds `P(τ₁ > t | η(0) = k, X₀,…,X_t)`, which the repository
writes as `Parking.survivalGivenWalk`, while `Support/SubcriticalGraftStep3.lean`
bounds the mean of the survival indicator when the `k` particles at the origin
are PRESCRIBED.  The passage between the two is the paper's own "temporarily
condition on all their walks and uniform variables", and it is an identity of
laws, proved here by splicing rather than by conditioning.

Two observations do it.  First, the realization itself carries a prescription:
`unshiftOrigin ω` removes the bottom particle at the origin and moves the other
labels there down by one index, and putting that particle back with its own data
returns the realization, so the survival indicator of `survivalGivenWalk` is the
grafted one with the prescription read off `ω`.  Second, splicing the data at
the origin between two independent copies of the law is measure preserving, so
that prescription is independent of everything the grafted observable reads.
Averaging the bound of `Support/SubcriticalGraftStep3.lean`, which is uniform in
the prescription, over the copy carrying the origin then gives the conditional
bound, the chance of `{η(0) = k}` appearing exactly as the denominator of the
conditional probability.
-/
import Parking.Support.SubcriticalGraftStep3
import Parking.Support.NoiseSplice

open MeasureTheory

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- The realization with the bottom particle at the origin removed: the count
there drops by one and the labels of the origin move down by one index. -/
def unshiftOrigin (ω : PData d) : PData d :=
  ((fun x => if x = (0 : Site d) then ω.1 x - 1 else ω.1 x),
    (fun q : Label d × ℕ =>
      if q.1.1 = (0 : Site d) then ω.2.1 (((0 : Site d), q.1.2 + 1), q.2) else ω.2.1 q),
    (fun q : Label d × ℕ =>
      if q.1.1 = (0 : Site d) then ω.2.2 (((0 : Site d), q.1.2 + 1), q.2) else ω.2.2 q))

/-- The uniform variables of the bottom particle at the origin. -/
def originRankOf (ω : PData d) : ℕ → ℝ := fun s => ω.2.2 ((((0 : Site d), 0) : Label d), s)

@[simp] theorem unshiftOrigin_eta_zero (ω : PData d) :
    (unshiftOrigin ω).1 (0 : Site d) = ω.1 (0 : Site d) - 1 := by
  simp [unshiftOrigin]

/-- **Putting the bottom particle at the origin back with its own data returns
the realization.** -/
theorem taggedDriver_unshiftOrigin (w : ℕ → Fin d × Bool) (ω : PData d) :
    taggedDriver w (originRankOf ω) (unshiftOrigin ω) = toPDriver (setMoves w ω) := by
  have he : addParticle (0 : Site d) (unshiftOrigin ω).1 = (setMoves w ω).1 := by
    funext x
    show (if x = (0 : Site d) then (unshiftOrigin ω).1 x + 1 else (unshiftOrigin ω).1 x)
      = ω.1 x
    by_cases hx : x = (0 : Site d)
    · rw [if_pos hx, hx]
      show ((if (0 : Site d) = (0 : Site d) then ω.1 (0 : Site d) - 1
        else ω.1 (0 : Site d)) + 1) = ω.1 (0 : Site d)
      rw [if_pos rfl]
      omega
    · rw [if_neg hx]
      show (if x = (0 : Site d) then ω.1 x - 1 else ω.1 x) = ω.1 x
      rw [if_neg hx]
  have hm : taggedMove w (unshiftOrigin ω).2.1 = (setMoves w ω).2.1 := by
    funext q
    obtain ⟨⟨x, i⟩, s⟩ := q
    show taggedMove w (unshiftOrigin ω).2.1 (((x, i) : Label d), s)
      = (if ((x, i) : Label d) = ((0 : Site d), 0) then w s else ω.2.1 (((x, i) : Label d), s))
    rw [taggedMove_apply]
    by_cases hx : x = (0 : Site d)
    · subst hx
      by_cases hi : i = 0
      · subst hi
        rw [if_pos rfl, if_pos rfl, if_pos rfl]
      · have hne : ¬ ((((0 : Site d), i) : Label d) = ((0 : Site d), 0)) := by
          simp [hi]
        rw [if_pos rfl, if_neg hi, if_neg hne]
        show (unshiftOrigin ω).2.1 ((((0 : Site d), i - 1) : Label d), s)
          = ω.2.1 ((((0 : Site d), i) : Label d), s)
        show (if (0 : Site d) = (0 : Site d) then
            ω.2.1 ((((0 : Site d), (i - 1) + 1) : Label d), s)
          else ω.2.1 ((((0 : Site d), i - 1) : Label d), s))
          = ω.2.1 ((((0 : Site d), i) : Label d), s)
        have hii : i - 1 + 1 = i := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hi)
        rw [if_pos rfl, hii]
    · have hne : ¬ ((((x, i) : Label d)) = ((0 : Site d), 0)) := by
        intro hh
        exact hx (congrArg Prod.fst hh)
      rw [if_neg hx, if_neg hne]
      show (if x = (0 : Site d) then ω.2.1 ((((0 : Site d), i + 1) : Label d), s)
        else ω.2.1 ((((x, i) : Label d)), s)) = ω.2.1 ((((x, i) : Label d)), s)
      rw [if_neg hx]
  have hr : taggedRank (originRankOf ω) (unshiftOrigin ω).2.2 = (setMoves w ω).2.2 := by
    funext q
    obtain ⟨⟨x, i⟩, s⟩ := q
    show taggedRank (originRankOf ω) (unshiftOrigin ω).2.2 (((x, i) : Label d), s)
      = ω.2.2 (((x, i) : Label d), s)
    rw [taggedRank_apply]
    by_cases hx : x = (0 : Site d)
    · subst hx
      by_cases hi : i = 0
      · subst hi
        rw [if_pos rfl, if_pos rfl]
        rfl
      · rw [if_pos rfl, if_neg hi]
        show (unshiftOrigin ω).2.2 ((((0 : Site d), i - 1) : Label d), s)
          = ω.2.2 ((((0 : Site d), i) : Label d), s)
        show (if (0 : Site d) = (0 : Site d) then
            ω.2.2 ((((0 : Site d), (i - 1) + 1) : Label d), s)
          else ω.2.2 ((((0 : Site d), i - 1) : Label d), s))
          = ω.2.2 ((((0 : Site d), i) : Label d), s)
        have hii : i - 1 + 1 = i := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hi)
        rw [if_pos rfl, hii]
    · rw [if_neg hx]
      show (if x = (0 : Site d) then ω.2.2 ((((0 : Site d), i + 1) : Label d), s)
        else ω.2.2 ((((x, i) : Label d)), s)) = ω.2.2 ((((x, i) : Label d)), s)
      rw [if_neg hx]
  show PDriver.mk (addParticle (0 : Site d) (unshiftOrigin ω).1)
      (taggedMove w (unshiftOrigin ω).2.1) (taggedRank (originRankOf ω) (unshiftOrigin ω).2.2)
    = PDriver.mk (setMoves w ω).1 (setMoves w ω).2.1 (setMoves w ω).2.2
  rw [he, hm, hr]

/-- Unshifting commutes with the graft: both act at the origin alone. -/
theorem unshiftOrigin_graftOrigin (ω₁ ω : PData d) :
    unshiftOrigin (graftOrigin ω₁ ω) = graftOrigin (unshiftOrigin ω₁) ω := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext x
    by_cases hx : x = (0 : Site d)
    · simp [unshiftOrigin, graftOrigin, hx]
    · simp [unshiftOrigin, graftOrigin, hx]
  · funext q
    by_cases hq : q.1.1 = (0 : Site d)
    · simp [unshiftOrigin, graftOrigin, hq]
    · simp [unshiftOrigin, graftOrigin, hq]
  · funext q
    by_cases hq : q.1.1 = (0 : Site d)
    · simp [unshiftOrigin, graftOrigin, hq]
    · simp [unshiftOrigin, graftOrigin, hq]

theorem originRankOf_graftOrigin (ω₁ ω : PData d) :
    originRankOf (graftOrigin ω₁ ω) = originRankOf ω₁ := by
  funext s
  exact graftOrigin_rank_zero (q := ((((0 : Site d), 0) : Label d), s)) rfl ω₁ ω

/-- The prescription a realization carries at the origin is its own family of
uniform variables there, so it is injective as soon as they are. -/
theorem originRank_unshiftOrigin (ω : PData d) :
    originRank (originRankOf ω) (unshiftOrigin ω)
      = fun p : ℕ × ℕ => ω.2.2 ((((0 : Site d), p.1) : Label d), p.2) := by
  funext p
  obtain ⟨i, s⟩ := p
  by_cases hi : i = 0
  · subst hi
    simp [originRank, originRankOf]
  · show (if i = 0 then originRankOf ω s
      else (unshiftOrigin ω).2.2 ((((0 : Site d), i - 1) : Label d), s))
      = ω.2.2 ((((0 : Site d), i) : Label d), s)
    rw [if_neg hi]
    show (if (0 : Site d) = (0 : Site d) then
        ω.2.2 ((((0 : Site d), (i - 1) + 1) : Label d), s)
      else ω.2.2 ((((0 : Site d), i - 1) : Label d), s))
      = ω.2.2 ((((0 : Site d), i) : Label d), s)
    have hii : i - 1 + 1 = i := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hi)
    rw [if_pos rfl, hii]

theorem injective_originRank_unshiftOrigin {ω : PData d} (h : Function.Injective ω.2.2) :
    Function.Injective (originRank (originRankOf ω) (unshiftOrigin ω)) := by
  rw [originRank_unshiftOrigin]
  rintro ⟨i, s⟩ ⟨j, u⟩ hij
  have h2 := h hij
  have h3 : ((((0 : Site d), i) : Label d)) = (((0 : Site d), j) : Label d) :=
    congrArg Prod.fst h2
  have h4 : s = u := congrArg Prod.snd h2
  have h5 : i = j := congrArg Prod.snd h3
  rw [h5, h4]


theorem graftOrigin_graftOrigin_left (a b c : PData d) :
    graftOrigin (graftOrigin a b) c = graftOrigin a c := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext x
    by_cases hx : x = (0 : Site d) <;> simp [graftOrigin, hx]
  · funext q
    by_cases hq : q.1.1 = (0 : Site d) <;> simp [graftOrigin, hq]
  · funext q
    by_cases hq : q.1.1 = (0 : Site d) <;> simp [graftOrigin, hq]

theorem graftOrigin_graftOrigin_right (a b c : PData d) :
    graftOrigin a (graftOrigin b c) = graftOrigin a c := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext x
    by_cases hx : x = (0 : Site d) <;> simp [graftOrigin, hx]
  · funext q
    by_cases hq : q.1.1 = (0 : Site d) <;> simp [graftOrigin, hq]
  · funext q
    by_cases hq : q.1.1 = (0 : Site d) <;> simp [graftOrigin, hq]

/-- The realization with its own origin grafted back is itself. -/
theorem graftOrigin_unshiftOrigin_self (ω : PData d) :
    graftOrigin (unshiftOrigin ω) ω = unshiftOrigin ω := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext x
    by_cases hx : x = (0 : Site d) <;> simp [graftOrigin, unshiftOrigin, hx]
  · funext q
    by_cases hq : q.1.1 = (0 : Site d) <;> simp [graftOrigin, unshiftOrigin, hq]
  · funext q
    by_cases hq : q.1.1 = (0 : Site d) <;> simp [graftOrigin, unshiftOrigin, hq]

/-- The integrand of `Parking.survivalGivenWalk`: the tagged particle at the
origin carries the prescribed walk `w`, the origin carries `k` particles, and
the tagged particle has not settled by time `t`. -/
def condObs (w : ℕ → Fin d × Bool) (k : ℕ) (t : ℕ) : PData d → ℝ := fun ω =>
  Set.indicator {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ) ∧
      (pState (toPDriver ω') t).active ((0 : Site d), 0) = true}
    (fun _ => (1 : ℝ)) (setMoves w ω)

theorem survivalGivenWalk_eq (d : ℕ) (ν : Measure ℤ) (k : ℕ) (t : ℕ)
    (w : ℕ → Fin d × Bool) :
    survivalGivenWalk d ν k t w
      = (∫ ω, condObs w k t ω ∂(pDataLaw d ν)) / (ν {(k : ℤ)}).toReal := rfl

/-- **The integrand of the conditional survival probability, read through the
prescription the realization itself carries.** -/
theorem condObs_eq (w : ℕ → Fin d × Bool) (k : ℕ) (t : ℕ) (ω : PData d) :
    condObs w k t ω
      = Set.indicator {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} (fun _ => (1 : ℝ)) ω
        * survivalObs w (originRankOf ω) t (unshiftOrigin ω) := by
  classical
  have hdrv : pState (toPDriver (setMoves w ω)) t
      = pState (taggedDriver w (originRankOf ω) (unshiftOrigin ω)) t := by
    rw [taggedDriver_unshiftOrigin]
  have hcount : (setMoves w ω).1 (0 : Site d) = ω.1 (0 : Site d) := rfl
  unfold condObs survivalObs
  by_cases h1 : ω.1 (0 : Site d) = (k : ℤ)
  · by_cases h2 : (pState (taggedDriver w (originRankOf ω) (unshiftOrigin ω)) t).active
        ((0 : Site d), 0) = true
    · rw [Set.indicator_of_mem (by exact ⟨by rw [hcount]; exact h1, by rw [hdrv]; exact h2⟩),
        Set.indicator_of_mem (show ω ∈ {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} from h1),
        Set.indicator_of_mem (show unshiftOrigin ω ∈ {ω' : PData d |
          (pState (taggedDriver w (originRankOf ω) ω') t).active (0, 0) = true}
          from h2)]
      norm_num
    · rw [Set.indicator_of_notMem (by
        intro hmem
        exact h2 (by rw [← hdrv]; exact hmem.2)),
        Set.indicator_of_notMem (show unshiftOrigin ω ∉ {ω' : PData d |
          (pState (taggedDriver w (originRankOf ω) ω') t).active (0, 0) = true}
          from h2)]
      norm_num
  · rw [Set.indicator_of_notMem (by
      intro hmem
      exact h1 (by rw [← hcount]; exact hmem.1)),
      Set.indicator_of_notMem (show ω ∉ {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} from h1)]
    norm_num

theorem condObs_graftOrigin (w : ℕ → Fin d × Bool) (k : ℕ) (t : ℕ) (ω₁ ω : PData d) :
    condObs w k t (graftOrigin ω₁ ω)
      = Set.indicator {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} (fun _ => (1 : ℝ)) ω₁
        * graftSurvivalObs w (originRankOf ω₁) (unshiftOrigin ω₁) t ω := by
  classical
  rw [condObs_eq, originRankOf_graftOrigin, unshiftOrigin_graftOrigin]
  congr 1
  · by_cases h : ω₁.1 (0 : Site d) = (k : ℤ)
    · rw [Set.indicator_of_mem (show graftOrigin ω₁ ω ∈
        {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} from by
          show (graftOrigin ω₁ ω).1 (0 : Site d) = (k : ℤ)
          rw [graftOrigin_eta_zero]; exact h),
        Set.indicator_of_mem (show ω₁ ∈ {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} from h)]
    · rw [Set.indicator_of_notMem (show graftOrigin ω₁ ω ∉
        {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} from by
          intro hmem
          exact h (by rw [← graftOrigin_eta_zero ω₁ ω]; exact hmem)),
        Set.indicator_of_notMem (show ω₁ ∉ {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} from h)]


theorem measurable_graftOrigin_pair :
    Measurable fun p : PData d × PData d => graftOrigin p.1 p.2 := by
  classical
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · refine measurable_pi_lambda _ fun x => ?_
    by_cases hx : x = (0 : Site d)
    · simpa [graftOrigin, hx] using
        (measurable_fst.fst.eval : Measurable fun p : PData d × PData d => p.1.1 x)
    · simpa [graftOrigin, hx] using
        (measurable_snd.fst.eval : Measurable fun p : PData d × PData d => p.2.1 x)
  · refine measurable_pi_lambda _ fun q => ?_
    by_cases hq : q.1.1 = (0 : Site d)
    · simpa [graftOrigin, hq] using
        (measurable_fst.snd.fst.eval : Measurable fun p : PData d × PData d => p.1.2.1 q)
    · simpa [graftOrigin, hq] using
        (measurable_snd.snd.fst.eval : Measurable fun p : PData d × PData d => p.2.2.1 q)
  · refine measurable_pi_lambda _ fun q => ?_
    by_cases hq : q.1.1 = (0 : Site d)
    · simpa [graftOrigin, hq] using
        (measurable_fst.snd.snd.eval : Measurable fun p : PData d × PData d => p.1.2.2 q)
    · simpa [graftOrigin, hq] using
        (measurable_snd.snd.snd.eval : Measurable fun p : PData d × PData d => p.2.2.2 q)

theorem measurable_setMoves (w : ℕ → Fin d × Bool) : Measurable (setMoves (d := d) w) := by
  classical
  refine Measurable.prodMk measurable_fst
    (Measurable.prodMk ?_ (measurable_snd.comp measurable_snd))
  refine measurable_pi_lambda _ fun q => ?_
  by_cases hq : q.1 = ((0 : Site d), 0)
  · simp [hq]
  · simpa [setMoves, hq] using
      (measurable_snd.fst.eval : Measurable fun ω : PData d => ω.2.1 q)

/-- **Splicing the data at the origin between two independent copies of the law
is measure preserving.** -/
theorem measurePreserving_graftOrigin (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun p : PData d × PData d => graftOrigin p.1 p.2)
      ((pDataLaw d ν).prod (pDataLaw d ν)) (pDataLaw d ν) := by
  classical
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI : IsProbabilityMeasure (stepLaw d) := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (moveLaw d) := by unfold moveLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  haveI : IsProbabilityMeasure (noiseLaw d) := by unfold noiseLaw; infer_instance
  have hsp := measurePreserving_pairSplice (LatticeProb.iidLaw d ν) (noiseLaw d)
    (measurePreserving_countComb ν ({(0 : Site d)} : Set (Site d)))
    (measurePreserving_noiseComb hd {p : Label d | p.1 = (0 : Site d)})
  have heq : (fun p : PData d × PData d => graftOrigin p.1 p.2)
      = fun p : PData d × PData d =>
        ((@LatticeProb.comb (Site d) (fun _ => ℤ) ({(0 : Site d)} : Set (Site d))
            (fun a => Classical.propDecidable (a ∈ ({(0 : Site d)} : Set (Site d)))) p.1.1 p.2.1,
          noiseComb {q : Label d | q.1 = (0 : Site d)} p.1.2 p.2.2) : PData d) := by
    funext p
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext x
      by_cases hx : x = (0 : Site d) <;> simp [LatticeProb.comb, graftOrigin, hx]
    · funext q
      by_cases hq : q.1.1 = (0 : Site d) <;>
        simp [noiseComb, LatticeProb.comb, graftOrigin, hq]
    · funext q
      by_cases hq : q.1.1 = (0 : Site d) <;>
        simp [noiseComb, LatticeProb.comb, graftOrigin, hq]

  rw [heq]
  exact hsp

/-- The count at the origin has the one-site law. -/
theorem pDataLaw_eta_zero (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] (m : ℤ) :
    (pDataLaw d ν) {ω : PData d | ω.1 (0 : Site d) = m} = ν {m} := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI : IsProbabilityMeasure (stepLaw d) := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (moveLaw d) := by unfold moveLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  haveI : IsProbabilityMeasure (noiseLaw d) := by unfold noiseLaw; infer_instance
  have h1 : MeasurePreserving (Prod.fst : PData d → (Site d → ℤ)) (pDataLaw d ν)
      (LatticeProb.iidLaw d ν) := by
    unfold pDataLaw
    exact measurePreserving_fst
  have h2 : MeasurePreserving (fun a : Site d → ℤ => a (0 : Site d))
      (LatticeProb.iidLaw d ν) ν := by
    show MeasurePreserving (fun a : Site d → ℤ => a (0 : Site d))
      (Measure.infinitePi fun _ : Site d => ν) ν
    exact measurePreserving_eval_infinitePi _ _
  have hmp : MeasurePreserving (fun ω : PData d => ω.1 (0 : Site d)) (pDataLaw d ν) ν :=
    h2.comp h1
  exact hmp.measure_preimage (measurableSet_singleton m).nullMeasurableSet

/-- **The passage from the prescribed origin to the conditional survival
probability.**  The bound of `Support/SubcriticalGraftStep3.lean` is uniform in
the prescription, and the prescription a realization carries at the origin is
independent of everything the grafted observable reads, so averaging it over the
copy that carries the origin divides by the chance of `{η(0) = k}`, which is the
denominator of the conditional probability. -/
theorem survivalGivenWalk_le_of_graft (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (w : ℕ → Fin d × Bool) (k : ℕ) (hνk : ν {(k : ℤ)} ≠ 0) (t : ℕ) {B : ℝ}
    (hB : ∀ (r : ℕ → ℝ) (ω₁ : PData d), Function.Injective (originRank r ω₁) →
        ω₁.1 (0 : Site d) = (k : ℤ) - 1 →
        ∫ ω, graftSurvivalObs w r ω₁ t ω ∂(pDataLaw d ν) ≤ B) :
    survivalGivenWalk d ν k t w ≤ B := by
  classical
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI : IsProbabilityMeasure (stepLaw d) := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (moveLaw d) := by unfold moveLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  haveI : IsProbabilityMeasure (noiseLaw d) := by unfold noiseLaw; infer_instance
  haveI : IsProbabilityMeasure (pDataLaw d ν) := by unfold pDataLaw; infer_instance
  have hcnt : MeasurableSet {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} := by
    have hm : Measurable fun ω : PData d => ω.1 (0 : Site d) :=
      (measurable_pi_apply (0 : Site d)).comp measurable_fst
    exact hm (measurableSet_singleton ((k : ℤ)))
  have hact : MeasurableSet {ω' : PData d |
      (pState (toPDriver ω') t).active ((0 : Site d), 0) = true} :=
    (measurableState_pState (Ω := PData d) (fun ω : PData d => ω.1) (fun ω => ω.2.1)
      (fun ω => ω.2.2) measurable_fst (measurable_fst.comp measurable_snd)
      (measurable_snd.comp measurable_snd) t).1 ((0 : Site d), 0) (measurableSet_singleton true)
  have hAmeas : MeasurableSet {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ) ∧
      (pState (toPDriver ω') t).active ((0 : Site d), 0) = true} := hcnt.inter hact
  have hcm : Measurable (condObs (d := d) w k t) :=
    (measurable_const.indicator hAmeas).comp (measurable_setMoves w)
  have hc0 : ∀ ω : PData d, 0 ≤ condObs w k t ω := by
    intro ω
    unfold condObs
    exact Set.indicator_apply_nonneg fun _ => zero_le_one
  have hc1 : ∀ ω : PData d, condObs w k t ω ≤ 1 := by
    intro ω
    unfold condObs
    rw [Set.indicator_apply]
    split_ifs <;> norm_num
  have hΦm : Measurable fun p : PData d × PData d => condObs w k t (graftOrigin p.1 p.2) :=
    hcm.comp measurable_graftOrigin_pair
  have hΦint : Integrable (fun p : PData d × PData d => condObs w k t (graftOrigin p.1 p.2))
      ((pDataLaw d ν).prod (pDataLaw d ν)) := by
    refine (integrable_const (1 : ℝ)).mono' hΦm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hc0 _)]
    exact hc1 _
  have hsplit : ∫ ω, condObs w k t ω ∂(pDataLaw d ν)
      = ∫ p, condObs w k t (graftOrigin p.1 p.2) ∂((pDataLaw d ν).prod (pDataLaw d ν)) := by
    have h := integral_map (μ := (pDataLaw d ν).prod (pDataLaw d ν))
      (φ := fun p : PData d × PData d => graftOrigin p.1 p.2) (f := condObs w k t)
      measurable_graftOrigin_pair.aemeasurable
      (by rw [(measurePreserving_graftOrigin hd ν).map_eq]; exact hcm.aestronglyMeasurable)
    rw [(measurePreserving_graftOrigin hd ν).map_eq] at h
    exact h
  have hfub := integral_prod _ hΦint
  have hinner : ∀ᵐ ω₁ ∂(pDataLaw d ν),
      (∫ ω, condObs w k t (graftOrigin ω₁ ω) ∂(pDataLaw d ν))
        ≤ Set.indicator {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} (fun _ => (1 : ℝ)) ω₁ * B := by
    filter_upwards [ae_injective_pDataLaw hd ν] with ω₁ hinj
    have heq : (∫ ω, condObs w k t (graftOrigin ω₁ ω) ∂(pDataLaw d ν))
        = Set.indicator {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} (fun _ => (1 : ℝ)) ω₁
          * ∫ ω, graftSurvivalObs w (originRankOf ω₁) (unshiftOrigin ω₁) t ω ∂(pDataLaw d ν) := by
      simp_rw [condObs_graftOrigin]
      exact integral_const_mul _ _
    rw [heq]
    by_cases h : ω₁.1 (0 : Site d) = (k : ℤ)
    · rw [Set.indicator_of_mem (show ω₁ ∈ {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} from h)]
      have hcount : (unshiftOrigin ω₁).1 (0 : Site d) = (k : ℤ) - 1 := by
        rw [unshiftOrigin_eta_zero, h]
      exact mul_le_mul_of_nonneg_left (hB (originRankOf ω₁) (unshiftOrigin ω₁)
        (injective_originRank_unshiftOrigin hinj) hcount) zero_le_one
    · rw [Set.indicator_of_notMem
        (show ω₁ ∉ {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} from h), zero_mul, zero_mul]
  have hIint : Integrable
      (fun ω₁ => ∫ ω, condObs w k t (graftOrigin ω₁ ω) ∂(pDataLaw d ν)) (pDataLaw d ν) :=
    hΦint.integral_prod_left
  have hIconst : Integrable (fun ω₁ : PData d =>
      Set.indicator {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} (fun _ => (1 : ℝ)) ω₁ * B)
      (pDataLaw d ν) :=
    ((integrable_const (1 : ℝ)).indicator hcnt).mul_const B
  have hmono := integral_mono_ae hIint hIconst hinner
  have hrhs : (∫ ω₁ : PData d,
      Set.indicator {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} (fun _ => (1 : ℝ)) ω₁ * B
        ∂(pDataLaw d ν)) = (ν {(k : ℤ)}).toReal * B := by
    rw [integral_mul_const, integral_indicator_const _ hcnt]
    have hreal : (pDataLaw d ν).real {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)}
        = (ν {(k : ℤ)}).toReal := by
      rw [MeasureTheory.measureReal_def, pDataLaw_eta_zero hd ν]
    rw [hreal]
    simp
  have hpos : 0 < (ν {(k : ℤ)}).toReal := ENNReal.toReal_pos hνk (measure_ne_top ν _)
  rw [survivalGivenWalk_eq, div_le_iff₀ hpos, hsplit, hfub]
  rw [hrhs] at hmono
  linarith [hmono]

end Parking

end
