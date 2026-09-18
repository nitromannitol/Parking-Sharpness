/-
The second inequality of Step 1 of `thm:subcritical` (`parking.tex:2456-2462`).

"If the origin instead has value `j`, then passing from that value to the
prescribed configuration takes at most `|j| + k - 1` single-particle changes,
each changing `Z` by at most one by Lemma lem:one-particle.  Averaging over `j`
proves the second inequality."

The passage is made in three stages.  From a count `j` at the origin, `|j|`
additions or deletions bring the count to zero.  At a count of zero the origin
carries no particle, so replacing its walks and uniform variables by the
prescribed ones changes nothing, by `lem:product`'s own clause that the
observable reads the particles present alone.  Then `k - 1` additions put the
prescribed particles there.  Each stage is a single-particle change, so the hole
count of the range moves by at most one at each of the `|j| + k - 1` steps.
-/
import Parking.Support.SubcriticalGraft
import Parking.Support.SubcriticalStep1

open MeasureTheory

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- The realization with the count at the origin replaced by `c`. -/
def setOriginCount (c : ℤ) (ω : PData d) : PData d :=
  ((fun x => if x = (0 : Site d) then c else ω.1 x), ω.2)

@[simp] theorem setOriginCount_eta_zero (c : ℤ) (ω : PData d) :
    (setOriginCount c ω).1 (0 : Site d) = c := by simp [setOriginCount]

theorem setOriginCount_eta_of_ne {x : Site d} (hx : x ≠ (0 : Site d)) (c : ℤ) (ω : PData d) :
    (setOriginCount c ω).1 x = ω.1 x := by simp [setOriginCount, hx]

theorem setOriginCount_self (ω : PData d) : setOriginCount (ω.1 (0 : Site d)) ω = ω := by
  refine Prod.ext ?_ rfl
  funext x
  by_cases hx : x = (0 : Site d)
  · simp [setOriginCount, hx]
  · simp [setOriginCount, hx]

theorem addAt_iter_origin (n : ℕ) (ω : PData d) :
    (addAt (0 : Site d))^[n] ω = setOriginCount (ω.1 (0 : Site d) + (n : ℤ)) ω := by
  induction n with
  | zero => simpa using (setOriginCount_self ω).symm
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    refine Prod.ext ?_ rfl
    funext x
    by_cases hx : x = (0 : Site d)
    · simp only [addAt, addParticle, setOriginCount, hx]
      push_cast
      ring
    · simp [addAt, addParticle, setOriginCount, hx]

theorem delAt_iter_origin (n : ℕ) (ω : PData d) :
    (delAt (0 : Site d))^[n] ω = setOriginCount (ω.1 (0 : Site d) - (n : ℤ)) ω := by
  induction n with
  | zero => simpa using (setOriginCount_self ω).symm
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    refine Prod.ext ?_ rfl
    funext x
    by_cases hx : x = (0 : Site d)
    · simp only [delAt, setOriginCount, hx]
      push_cast
      ring
    · simp [delAt, setOriginCount, hx]

theorem abs_holeObs_add_iter (hd : 1 ≤ d) (w : ℕ → Fin d × Bool) (t : ℕ) (n : ℕ)
    (ω : PData d) :
    |holeObs w t ((addAt (0 : Site d))^[n] ω) - holeObs w t ω| ≤ (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h1 := holeObs_add_lip hd w t (0 : Site d) ((addAt (0 : Site d))^[n] ω)
    have h2 := abs_sub_le (holeObs w t (addAt (0 : Site d) ((addAt (0 : Site d))^[n] ω)))
      (holeObs w t ((addAt (0 : Site d))^[n] ω)) (holeObs w t ω)
    push_cast
    linarith

theorem abs_holeObs_del_iter (hd : 1 ≤ d) (w : ℕ → Fin d × Bool) (t : ℕ) (n : ℕ)
    (ω : PData d) :
    |holeObs w t ((delAt (0 : Site d))^[n] ω) - holeObs w t ω| ≤ (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h1 := holeObs_del_lip hd w t (0 : Site d) ((delAt (0 : Site d))^[n] ω)
    have h2 := abs_sub_le (holeObs w t (delAt (0 : Site d) ((delAt (0 : Site d))^[n] ω)))
      (holeObs w t ((delAt (0 : Site d))^[n] ω)) (holeObs w t ω)
    push_cast
    linarith

/-- Emptying the origin costs at most `|η(0)|` single-particle changes. -/
theorem abs_holeObs_setOriginCount_zero (hd : 1 ≤ d) (w : ℕ → Fin d × Bool) (t : ℕ)
    (ω : PData d) :
    |holeObs w t (setOriginCount 0 ω) - holeObs w t ω| ≤ |((ω.1 (0 : Site d) : ℤ) : ℝ)| := by
  rcases le_or_gt (0 : ℤ) (ω.1 (0 : Site d)) with h | h
  · have hiter : (delAt (0 : Site d))^[(ω.1 (0 : Site d)).toNat] ω = setOriginCount 0 ω := by
      rw [delAt_iter_origin, Int.toNat_of_nonneg h, sub_self]
    have hb := abs_holeObs_del_iter hd w t (ω.1 (0 : Site d)).toNat ω
    rw [hiter] at hb
    refine le_trans hb (le_of_eq ?_)
    rw [abs_of_nonneg (by exact_mod_cast h : (0 : ℝ) ≤ ((ω.1 (0 : Site d) : ℤ) : ℝ))]
    exact_mod_cast congrArg (fun m : ℤ => (m : ℝ)) (Int.toNat_of_nonneg h)
  · have hiter : (addAt (0 : Site d))^[(-(ω.1 (0 : Site d))).toNat] ω = setOriginCount 0 ω := by
      rw [addAt_iter_origin, Int.toNat_of_nonneg (by omega)]
      simp
    have hb := abs_holeObs_add_iter hd w t (-(ω.1 (0 : Site d))).toNat ω
    rw [hiter] at hb
    refine le_trans hb (le_of_eq ?_)
    rw [abs_of_neg (by exact_mod_cast h : ((ω.1 (0 : Site d) : ℤ) : ℝ) < 0)]
    have : ((-(ω.1 (0 : Site d))).toNat : ℤ) = -(ω.1 (0 : Site d)) :=
      Int.toNat_of_nonneg (by omega)
    exact_mod_cast congrArg (fun m : ℤ => (m : ℝ)) this

/-- With the origin empty the prescription is invisible: no label of the origin
carries a particle, and everywhere else the data is that of `ω`. -/
theorem holeObs_setOriginCount_zero_graft (w : ℕ → Fin d × Bool) (t : ℕ)
    (ω₁ ω : PData d) :
    holeObs w t (setOriginCount 0 (graftOrigin ω₁ ω)) = holeObs w t (setOriginCount 0 ω) := by
  have hc : (setOriginCount 0 (graftOrigin ω₁ ω)).1 = (setOriginCount 0 ω).1 := by
    funext x
    by_cases hx : x = (0 : Site d)
    · rw [hx, setOriginCount_eta_zero, setOriginCount_eta_zero]
    · rw [setOriginCount_eta_of_ne hx, setOriginCount_eta_of_ne hx,
        graftOrigin_eta_of_ne hx]
  have hpres : ∀ q : Label d × ℕ,
      q.1.2 < ((setOriginCount 0 (graftOrigin ω₁ ω)).1 q.1.1).toNat → q.1.1 ≠ (0 : Site d) := by
    intro q hq h0
    rw [h0, setOriginCount_eta_zero] at hq
    simp at hq
  have hm : ∀ q : Label d × ℕ,
      q.1.2 < ((setOriginCount 0 (graftOrigin ω₁ ω)).1 q.1.1).toNat →
      (setOriginCount 0 (graftOrigin ω₁ ω)).2.1 q = (setOriginCount 0 ω).2.1 q := by
    intro q hq
    exact graftOrigin_move_of_ne (hpres q hq) ω₁ ω
  have hr : ∀ q : Label d × ℕ,
      q.1.2 < ((setOriginCount 0 (graftOrigin ω₁ ω)).1 q.1.1).toNat →
      (setOriginCount 0 (graftOrigin ω₁ ω)).2.2 q = (setOriginCount 0 ω).2.2 q := by
    intro q hq
    exact graftOrigin_rank_of_ne (hpres q hq) ω₁ ω
  unfold holeObs
  refine Finset.sum_congr rfl fun x _ => ?_
  exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (pHoleCount_reads hc hm hr t x)

/-- **The cost of prescribing the particles at the origin.** -/
theorem abs_graftHoleObs_sub_le (hd : 1 ≤ d) (w : ℕ → Fin d × Bool) (t : ℕ)
    {ω₁ : PData d} (hc : 0 ≤ ω₁.1 (0 : Site d)) (ω : PData d) :
    |graftHoleObs w ω₁ t ω - holeObs w t ω|
      ≤ ((ω₁.1 (0 : Site d)).toNat : ℝ) + |((ω.1 (0 : Site d) : ℤ) : ℝ)| := by
  have hiter : (addAt (0 : Site d))^[(ω₁.1 (0 : Site d)).toNat]
      (setOriginCount 0 (graftOrigin ω₁ ω)) = graftOrigin ω₁ ω := by
    rw [addAt_iter_origin, setOriginCount_eta_zero, zero_add, Int.toNat_of_nonneg hc]
    have h1 : (graftOrigin ω₁ ω).1 (0 : Site d) = ω₁.1 (0 : Site d) := graftOrigin_eta_zero ω₁ ω
    refine Prod.ext ?_ rfl
    funext x
    by_cases hx : x = (0 : Site d)
    · simp [setOriginCount, hx, h1]
    · simp [setOriginCount, hx]
  have h1 := abs_holeObs_add_iter hd w t (ω₁.1 (0 : Site d)).toNat
    (setOriginCount 0 (graftOrigin ω₁ ω))
  rw [hiter] at h1
  have h2 := abs_holeObs_setOriginCount_zero hd w t ω
  have h3 := holeObs_setOriginCount_zero_graft w t ω₁ ω
  have h4 : |graftHoleObs w ω₁ t ω - holeObs w t ω|
      ≤ |holeObs w t (graftOrigin ω₁ ω) - holeObs w t (setOriginCount 0 (graftOrigin ω₁ ω))|
        + |holeObs w t (setOriginCount 0 (graftOrigin ω₁ ω)) - holeObs w t ω| :=
    abs_sub_le _ _ _
  rw [h3] at h1 h4
  linarith [h4, h1, h2]

/-- The integral of a functional of the counts alone is taken against the
configuration law. -/
theorem integral_counts_pDataLaw (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {G : (Site d → ℤ) → ℝ} (hG : AEStronglyMeasurable G (LatticeProb.iidLaw d ν)) :
    ∫ ω : PData d, G ω.1 ∂(pDataLaw d ν) = ∫ a, G a ∂(LatticeProb.iidLaw d ν) := by
  haveI := Parking.stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (moveLaw d) := by unfold moveLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  have hmp : MeasurePreserving (Prod.fst : PData d → (Site d → ℤ))
      (pDataLaw d ν) (LatticeProb.iidLaw d ν) := by
    unfold pDataLaw
    exact measurePreserving_fst
  have h := integral_map (μ := pDataLaw d ν) (φ := (Prod.fst : PData d → (Site d → ℤ)))
    (f := G) measurable_fst.aemeasurable (by rw [hmp.map_eq]; exact hG)
  rw [hmp.map_eq] at h
  exact h.symm

/-- The mean absolute count at the origin is the first absolute moment of the
one-site law. -/
theorem integral_abs_eta_pDataLaw (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν] :
    ∫ ω : PData d, |((ω.1 (0 : Site d) : ℤ) : ℝ)| ∂(pDataLaw d ν) = ∫ k, |(k : ℝ)| ∂ν := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hmeas : AEStronglyMeasurable (fun a : Site d → ℤ => |((a (0 : Site d) : ℤ) : ℝ)|)
      (LatticeProb.iidLaw d ν) :=
    ((measurable_from_countable' fun k : ℤ => |(k : ℝ)|).comp
      (measurable_pi_apply (0 : Site d))).aestronglyMeasurable
  rw [integral_counts_pDataLaw hd hmeas]
  have hmap : (LatticeProb.iidLaw d ν).map (fun η : Site d → ℤ => η 0) = ν :=
    Measure.infinitePi_map_eval _ 0
  have h := integral_map (μ := LatticeProb.iidLaw d ν) (φ := fun η : Site d → ℤ => η 0)
    (f := fun k : ℤ => |(k : ℝ)|) (measurable_pi_apply (0 : Site d)).aemeasurable
    ((measurable_from_countable' fun k : ℤ => |(k : ℝ)|).aestronglyMeasurable)
  rw [hmap] at h
  exact h.symm

theorem integrable_abs_eta_pDataLaw (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) :
    Integrable (fun ω : PData d => |((ω.1 (0 : Site d) : ℤ) : ℝ)|) (pDataLaw d ν) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  refine integrable_pDataLaw_of_counts (G := fun a : Site d → ℤ => |((a (0 : Site d) : ℤ) : ℝ)|)
    hd ?_
  have hmap : (LatticeProb.iidLaw d ν).map (fun η : Site d → ℤ => η 0) = ν :=
    Measure.infinitePi_map_eval _ 0
  refine (integrable_map_measure (g := fun k : ℤ => |(k : ℝ)|)
    (f := fun η : Site d → ℤ => η 0) (μ := LatticeProb.iidLaw d ν)
    (by rw [hmap]; exact hint.aestronglyMeasurable)
    (measurable_pi_apply (0 : Site d)).aemeasurable).mp (by rw [hmap]; exact hint)

theorem integrable_graftHoleObs (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (w : ℕ → Fin d × Bool) (t : ℕ)
    {ω₁ : PData d} (hc : 0 ≤ ω₁.1 (0 : Site d)) :
    Integrable (graftHoleObs w ω₁ t) (pDataLaw d ν) := by
  haveI := noiseLaw_isProbability hd
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI : IsProbabilityMeasure (pDataLaw d ν) := by rw [pDataLaw_eq_prod]; infer_instance
  have hZ : Integrable (holeObs (d := d) w t) (pDataLaw d ν) := by
    unfold holeObs
    exact integrable_finsetSum _ fun x _ => integrable_pHoleCount hd hint t x
  refine Integrable.mono' (hZ.abs.add (((integrable_abs_eta_pDataLaw hd hint).add
    (integrable_const ((ω₁.1 (0 : Site d)).toNat : ℝ)))))
    (measurable_graftHoleObs w ω₁ t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  have h := abs_graftHoleObs_sub_le hd w t hc ω
  have h2 : |graftHoleObs w ω₁ t ω| ≤ |holeObs w t ω|
      + (|((ω.1 (0 : Site d) : ℤ) : ℝ)| + ((ω₁.1 (0 : Site d)).toNat : ℝ)) := by
    have := abs_sub_abs_le_abs_sub (graftHoleObs w ω₁ t ω) (holeObs w t ω)
    linarith
  rw [Real.norm_eq_abs]
  exact h2

/-- **The second inequality of Step 1 of `thm:subcritical`**: with the `k`
particles at the origin prescribed, the mean number of unfilled holes of the
range is at least `δ(λ)|R_t| - E_λ|η(0)| - (k-1)`. -/
theorem rangeCard_mul_sub_le_integral_graftHoleObs (hd : 1 ≤ d) {ν : Measure ℤ}
    [IsProbabilityMeasure ν] (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (w : ℕ → Fin d × Bool) (t : ℕ) {ω₁ : PData d} (hc : 0 ≤ ω₁.1 (0 : Site d)) :
    (rangeCard (0 : Site d) w t : ℝ) * (-∫ k, (k : ℝ) ∂ν) - (∫ k, |(k : ℝ)| ∂ν)
        - ((ω₁.1 (0 : Site d)).toNat : ℝ)
      ≤ ∫ ω, graftHoleObs w ω₁ t ω ∂(pDataLaw d ν) := by
  haveI := noiseLaw_isProbability hd
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI : IsProbabilityMeasure (pDataLaw d ν) := by rw [pDataLaw_eq_prod]; infer_instance
  have hZ : Integrable (holeObs (d := d) w t) (pDataLaw d ν) := by
    unfold holeObs
    exact integrable_finsetSum _ fun x _ => integrable_pHoleCount hd hint t x
  have hA : Integrable (fun ω : PData d => holeObs w t ω
      - (|((ω.1 (0 : Site d) : ℤ) : ℝ)| + ((ω₁.1 (0 : Site d)).toNat : ℝ))) (pDataLaw d ν) :=
    hZ.sub ((integrable_abs_eta_pDataLaw hd hint).add (integrable_const _))
  have hmono : ∀ ω : PData d, holeObs w t ω
      - (|((ω.1 (0 : Site d) : ℤ) : ℝ)| + ((ω₁.1 (0 : Site d)).toNat : ℝ))
      ≤ graftHoleObs w ω₁ t ω := by
    intro ω
    have h := abs_graftHoleObs_sub_le hd w t hc ω
    have h2 := abs_le.mp h
    linarith [h2.1]
  have hle := integral_mono hA (integrable_graftHoleObs hd hint w t hc) hmono
  have hsplit : ∫ ω : PData d, (holeObs w t ω
        - (|((ω.1 (0 : Site d) : ℤ) : ℝ)| + ((ω₁.1 (0 : Site d)).toNat : ℝ))) ∂(pDataLaw d ν)
      = (∫ ω, holeObs w t ω ∂(pDataLaw d ν)) - ((∫ k, |(k : ℝ)| ∂ν)
        + ((ω₁.1 (0 : Site d)).toNat : ℝ)) := by
    have e1 : ∫ ω : PData d,
          (|((ω.1 (0 : Site d) : ℤ) : ℝ)| + ((ω₁.1 (0 : Site d)).toNat : ℝ)) ∂(pDataLaw d ν)
        = (∫ k, |(k : ℝ)| ∂ν) + ((ω₁.1 (0 : Site d)).toNat : ℝ) := by
      rw [integral_add (integrable_abs_eta_pDataLaw hd hint) (integrable_const _),
        integral_abs_eta_pDataLaw hd, integral_const]
      simp
    rw [integral_sub (f := fun ω : PData d => holeObs w t ω)
      (g := fun ω : PData d =>
        |((ω.1 (0 : Site d) : ℤ) : ℝ)| + ((ω₁.1 (0 : Site d)).toNat : ℝ))
      hZ ((integrable_abs_eta_pDataLaw hd hint).add (integrable_const _)), e1]
  rw [hsplit] at hle
  have hstep1 := rangeCard_mul_le_integral_holeObs hd hint w t
  linarith

end Parking

end
