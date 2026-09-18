/-
The joint bound `P(η(0) = k, τ₁ > t) ≤ ν{k} C_k E₀ e^{-a|R_t|}`
(`parking.tex:2493-2496`).

The last assertion of `thm:subcritical` averages `eq:range-upper` over the walk
of the tagged particle and sums over `k`.  Averaging over the walk needs no new
conditioning: the walk of the bottom particle at the origin is itself part of the
realization, so the same splicing that proved the conditional bound proves the
joint one, and the bound then depends on the realization through that walk alone.
The count at the origin and the walks are independent fields of the law, so the
average factorizes, and the law of the walk of one label is the law of a simple
random walk's direction sequence.
-/
import Parking.Support.SubcriticalBound

open MeasureTheory

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

theorem graftOrigin_move_zero {q : Label d × ℕ} (hq : q.1.1 = (0 : Site d))
    (ω₁ ω : PData d) : (graftOrigin ω₁ ω).2.1 q = ω₁.2.1 q := by
  simp [graftOrigin, hq]

/-- The walk of the bottom particle at the origin. -/
def originMoveOf (ω : PData d) : ℕ → Fin d × Bool :=
  fun s => ω.2.1 ((((0 : Site d), 0) : Label d), s)

theorem setMoves_originMoveOf (ω : PData d) : setMoves (originMoveOf ω) ω = ω := by
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext q
  show (if q.1 = ((0 : Site d), 0) then originMoveOf ω q.2 else ω.2.1 q) = ω.2.1 q
  by_cases hq : q.1 = ((0 : Site d), 0)
  · rw [if_pos hq]
    show ω.2.1 ((((0 : Site d), 0) : Label d), q.2) = ω.2.1 q
    rw [← hq]
  · rw [if_neg hq]

theorem originMoveOf_graftOrigin (ω₁ ω : PData d) :
    originMoveOf (graftOrigin ω₁ ω) = originMoveOf ω₁ := by
  funext s
  exact graftOrigin_move_zero (q := ((((0 : Site d), 0) : Label d), s)) rfl ω₁ ω

/-- The observable of `eq:S-expand`: the origin carries `k` particles and the
bottom one has not settled by time `t`. -/
def jointObs (k : ℕ) (t : ℕ) : PData d → ℝ :=
  Set.indicator {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ) ∧
      (pState (toPDriver ω') t).active ((0 : Site d), 0) = true} (fun _ => (1 : ℝ))

theorem jointObs_eq_condObs (k t : ℕ) (ω : PData d) :
    jointObs k t ω = condObs (originMoveOf ω) k t ω := by
  unfold condObs jointObs
  rw [setMoves_originMoveOf]

theorem jointObs_graftOrigin (k t : ℕ) (ω₁ ω : PData d) :
    jointObs k t (graftOrigin ω₁ ω)
      = Set.indicator {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} (fun _ => (1 : ℝ)) ω₁
        * graftSurvivalObs (originMoveOf ω₁) (originRankOf ω₁) (unshiftOrigin ω₁) t ω := by
  rw [jointObs_eq_condObs, originMoveOf_graftOrigin, condObs_graftOrigin]

/-- **The law of the walk of one label is the law of a direction sequence.** -/
theorem moveLaw_map_originMove (d : ℕ) (hd : 1 ≤ d) :
    (moveLaw d).map (fun m : Label d × ℕ → Fin d × Bool =>
      fun s : ℕ => m ((((0 : Site d), 0) : Label d), s)) = walkLaw d := by
  haveI : IsProbabilityMeasure (stepLaw d) := stepLaw_isProbability hd
  have hinj : Function.Injective (fun s : ℕ => ((((0 : Site d), 0) : Label d), s)) := by
    intro a b h
    exact congrArg Prod.snd h
  show (Measure.infinitePi fun _ : Label d × ℕ => stepLaw d).map
      (fun m => fun s : ℕ => m ((((0 : Site d), 0) : Label d), s))
    = Measure.infinitePi fun _ : ℕ => stepLaw d
  exact Measure.map_infinitePi_infinitePi_of_inj hinj

theorem measurable_originMoveOf : Measurable (originMoveOf (d := d)) := by
  refine measurable_pi_lambda _ fun s => ?_
  exact (measurable_pi_apply ((((0 : Site d), 0) : Label d), s)).comp
    (measurable_fst.comp measurable_snd)

/-- **The count at the origin and the walk of the bottom particle there are
independent**, so an average against both factorizes. -/
theorem integral_indicator_mul_originMove (hd : 1 ≤ d) {ν : Measure ℤ}
    [IsProbabilityMeasure ν] (k : ℕ) {Bd : (ℕ → Fin d × Bool) → ℝ}
    (hBm : Measurable Bd) {M : ℝ} (hBb : ∀ w, |Bd w| ≤ M) :
    (∫ ω, Set.indicator {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} (fun _ => (1 : ℝ)) ω
        * Bd (originMoveOf ω) ∂(pDataLaw d ν))
      = (ν {(k : ℤ)}).toReal * ∫ p, Bd p ∂(walkLaw d) := by
  classical
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI : IsProbabilityMeasure (stepLaw d) := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (moveLaw d) := by unfold moveLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  haveI : IsProbabilityMeasure (noiseLaw d) := by unfold noiseLaw; infer_instance
  have hcnt : MeasurableSet {a : Site d → ℤ | a (0 : Site d) = (k : ℤ)} := by
    have hm : Measurable fun a : Site d → ℤ => a (0 : Site d) := measurable_pi_apply _
    exact hm (measurableSet_singleton ((k : ℤ)))
  set G : (Site d → ℤ) → ℝ :=
    Set.indicator {a : Site d → ℤ | a (0 : Site d) = (k : ℤ)} (fun _ => (1 : ℝ)) with hGdef
  set H : PNoise d → ℝ :=
    fun b => Bd (fun s : ℕ => b.1 ((((0 : Site d), 0) : Label d), s)) with hHdef
  have hGm : Measurable G := measurable_const.indicator hcnt
  have hHm : Measurable H :=
    hBm.comp (measurable_pi_lambda _ fun s => (measurable_pi_apply _).comp measurable_fst)
  have hG1 : ∀ a, |G a| ≤ 1 := by
    intro a
    rw [hGdef, Set.indicator_apply]
    split_ifs <;> norm_num
  have hH1 : ∀ b, |H b| ≤ M := fun b => hBb _
  have hGi : Integrable G (LatticeProb.iidLaw d ν) :=
    (integrable_const (1 : ℝ)).mono' hGm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hG1 a)
  have hHi : Integrable H (noiseLaw d) :=
    (integrable_const M).mono' hHm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun b => by rw [Real.norm_eq_abs]; exact hH1 b)
  have hstep : ∀ ω : PData d,
      Set.indicator {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} (fun _ => (1 : ℝ)) ω
          * Bd (originMoveOf ω) = G ω.1 * H ω.2 := by
    intro ω
    have hind : Set.indicator {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} (fun _ => (1 : ℝ)) ω
        = G ω.1 := by
      rw [hGdef]
      by_cases h : ω.1 (0 : Site d) = (k : ℤ)
      · rw [Set.indicator_of_mem (show ω ∈ {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} from h),
          Set.indicator_of_mem
            (show ω.1 ∈ {a : Site d → ℤ | a (0 : Site d) = (k : ℤ)} from h)]
      · rw [Set.indicator_of_notMem
          (show ω ∉ {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} from h),
          Set.indicator_of_notMem
            (show ω.1 ∉ {a : Site d → ℤ | a (0 : Site d) = (k : ℤ)} from h)]
    rw [hind, hHdef]
    rfl
  rw [integral_congr_ae (Filter.Eventually.of_forall hstep)]
  have hprodint : Integrable (fun z : (Site d → ℤ) × PNoise d => G z.1 * H z.2)
      ((LatticeProb.iidLaw d ν).prod (noiseLaw d)) := by
    refine Integrable.mono' (integrable_const M)
      ((hGm.comp measurable_fst).mul (hHm.comp measurable_snd)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hG1 z.1
    have h2 := hH1 z.2
    have h3 : (0 : ℝ) ≤ |H z.2| := abs_nonneg _
    nlinarith [abs_nonneg (G z.1)]
  rw [show pDataLaw d ν = (LatticeProb.iidLaw d ν).prod (noiseLaw d) from rfl,
    integral_prod _ hprodint]
  simp_rw [integral_const_mul]
  rw [integral_mul_const]
  have h1 : (∫ a, G a ∂(LatticeProb.iidLaw d ν)) = (ν {(k : ℤ)}).toReal := by
    rw [hGdef, integral_indicator_const _ hcnt]
    have hmp : MeasurePreserving (fun a : Site d → ℤ => a (0 : Site d))
        (LatticeProb.iidLaw d ν) ν := by
      show MeasurePreserving (fun a : Site d → ℤ => a (0 : Site d))
        (Measure.infinitePi fun _ : Site d => ν) ν
      exact measurePreserving_eval_infinitePi _ _
    have hval : (LatticeProb.iidLaw d ν) {a : Site d → ℤ | a (0 : Site d) = (k : ℤ)}
        = ν {(k : ℤ)} :=
      hmp.measure_preimage (measurableSet_singleton ((k : ℤ))).nullMeasurableSet
    rw [MeasureTheory.measureReal_def, hval]
    simp
  have h2 : (∫ b, H b ∂(noiseLaw d)) = ∫ p, Bd p ∂(walkLaw d) := by
    have hmp : MeasurePreserving (Prod.fst : PNoise d → (Label d × ℕ → Fin d × Bool))
        (noiseLaw d) (moveLaw d) := by
      unfold noiseLaw
      exact measurePreserving_fst
    have hstep1 : (∫ b, H b ∂(noiseLaw d))
        = ∫ m, Bd (fun s : ℕ => m ((((0 : Site d), 0) : Label d), s)) ∂(moveLaw d) := by
      have h := integral_map (μ := noiseLaw d)
        (φ := (Prod.fst : PNoise d → (Label d × ℕ → Fin d × Bool)))
        (f := fun m => Bd (fun s : ℕ => m ((((0 : Site d), 0) : Label d), s)))
        measurable_fst.aemeasurable
        (by rw [hmp.map_eq]
            exact (hBm.comp (measurable_pi_lambda _ fun s =>
              measurable_pi_apply _)).aestronglyMeasurable)
      rw [hmp.map_eq] at h
      exact h.symm
    rw [hstep1]
    have hBi : Integrable Bd (walkLaw d) := by
      haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
      exact (integrable_const M).mono' hBm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hBb p)
    have h := integral_map (μ := moveLaw d)
      (φ := fun m : Label d × ℕ → Fin d × Bool =>
        fun s : ℕ => m ((((0 : Site d), 0) : Label d), s)) (f := Bd)
      (measurable_pi_lambda _ fun s => measurable_pi_apply _).aemeasurable
      (by rw [moveLaw_map_originMove d hd]; exact hBi.aestronglyMeasurable)
    rw [moveLaw_map_originMove d hd] at h
    exact h.symm
  rw [h1, h2]

end Parking

end
