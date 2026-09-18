/-
The joint bound of `parking.tex:2493-2496`, and the last assertion of
`thm:subcritical`.

`eq:range-upper` bounds the survival probability of the tagged particle for a
PRESCRIBED walk.  The walk of the bottom particle at the origin is itself part
of the realization, so the same splice that proved the conditional bound bounds
the joint probability `P(η(0) = k, τ₁ > t)` by `ν{k}` times the average of the
walk-dependent bound, and that average is over the law of a simple random
walk's direction sequence.  Summing over `k` against `eq:S-expand` then gives
`S_t ≤ C E₀ e^{-a|R_t|}`, the constant being finite because
`k e^{λ₁k/3} ≤ C e^{λ₁ k}` and `E e^{θ η(0)} < ∞` with `λ₁ < θ`.
-/
import Parking.Support.SubcriticalJoint
import Parking.Support.RangeLower
import Parking.Support.Near

open MeasureTheory

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- The range of the walk read off its direction sequence is measurable. -/
theorem measurable_rangeCard_walk (t : ℕ) :
    Measurable fun p : ℕ → Fin d × Bool => ((rangeCard (0 : Site d) p t : ℕ) : ℝ) :=
  (measurable_from_countable' (fun k : ℕ => (k : ℝ))).comp (measurable_rangeCard (0 : Site d) t)

theorem measurable_jointObs (k t : ℕ) : Measurable (jointObs (d := d) k t) := by
  classical
  exact measurable_const.indicator (measurableSet_conf_active (k : ℤ) t 0)

theorem jointObs_nonneg (k t : ℕ) (ω : PData d) : 0 ≤ jointObs k t ω := by
  unfold jointObs
  exact Set.indicator_apply_nonneg fun _ => zero_le_one

theorem jointObs_le_one (k t : ℕ) (ω : PData d) : jointObs k t ω ≤ 1 := by
  unfold jointObs
  rw [Set.indicator_apply]
  split_ifs <;> norm_num

/-- The mean of the joint observable IS the joint probability of the stack
construction. -/
theorem integral_jointObs_eq (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (k t : ℕ) :
    ∫ ω, jointObs k t ω ∂(pDataLaw d ν)
      = ((law d ν) {ω : Data d | ω.1 0 = (k : ℤ) ∧
          (LatticeProb.state (toDriver ω) t).active (0, 0) = true}).toReal := by
  classical
  have hS : MeasurableSet {ω : PData d | ω.1 0 = (k : ℤ) ∧
      (pState (toPDriver ω) t).active (0, 0) = true} := measurableSet_conf_active (k : ℤ) t 0
  have h1 : ∫ ω, jointObs k t ω ∂(pDataLaw d ν)
      = (pDataLaw d ν).real {ω : PData d | ω.1 0 = (k : ℤ) ∧
          (pState (toPDriver ω) t).active (0, 0) = true} := by
    rw [show jointObs (d := d) k t = Set.indicator {ω : PData d | ω.1 0 = (k : ℤ) ∧
        (pState (toPDriver ω) t).active (0, 0) = true} (fun _ => (1 : ℝ)) from rfl,
      integral_indicator_const (1 : ℝ) hS]
    simp
  rw [h1, measureReal_def, ← measure_conf_active_transfer hd ν (k : ℤ) t]

/-- `a ≥ 0` whenever the tilted means are nonpositive on `[0, λ₁]`. -/
theorem drift_intervalIntegral_nonneg {ν : Measure ℤ} {lam₁ : ℝ} (hlam₁ : 0 ≤ lam₁)
    (hnonpos : ∀ s ∈ Set.Icc (0 : ℝ) lam₁, ∫ k, (k : ℝ) ∂(tiltLaw ν s) ≤ 0) :
    0 ≤ (1 / 3) * ∫ s in (0 : ℝ)..lam₁, drift ν s := by
  have h : 0 ≤ ∫ s in (0 : ℝ)..lam₁, drift ν s := by
    refine intervalIntegral.integral_nonneg hlam₁ fun u hu => ?_
    have := hnonpos u hu
    unfold drift
    linarith
  linarith

/-- **`eq:range-upper` for the joint observable**: with the origin carrying `k`
particles, the bound holds with the walk the bottom particle there carries. -/
theorem integral_jointObs_graftOrigin_le (hd : 1 ≤ d) {ν : Measure ℤ}
    [IsProbabilityMeasure ν] (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) {θ : ℝ}
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    {lam₁ : ℝ} (hlam₁ : 0 < lam₁) (hlam₁θ : lam₁ < θ)
    (hnonpos : ∀ s ∈ Set.Icc (0 : ℝ) lam₁,
      Integrable (fun k : ℤ => (k : ℝ)) (tiltLaw ν s) ∧
      ∫ k, (k : ℝ) ∂(tiltLaw ν s) ≤ 0)
    (k : ℕ) (hk : 1 ≤ k) (t : ℕ) {ω₁ : PData d} (hinj : Function.Injective ω₁.2.2)
    (h : ω₁.1 (0 : Site d) = (k : ℤ)) :
    (∫ ω, jointObs k t (graftOrigin ω₁ ω) ∂(pDataLaw d ν))
      ≤ Real.exp ((1 / 3) * ∫ s in (0 : ℝ)..lam₁, ∫ j, |(j : ℝ)| ∂(tiltLaw ν s))
        * Real.exp (lam₁ * ((k : ℝ) - 1) / 3
          - ((1 / 3) * ∫ s in (0 : ℝ)..lam₁, drift ν s)
            * (rangeCard (0 : Site d) (originMoveOf ω₁) t : ℝ)) := by
  have heq : (∫ ω, jointObs k t (graftOrigin ω₁ ω) ∂(pDataLaw d ν))
      = Set.indicator {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} (fun _ => (1 : ℝ)) ω₁
        * ∫ ω, graftSurvivalObs (originMoveOf ω₁) (originRankOf ω₁) (unshiftOrigin ω₁) t ω
            ∂(pDataLaw d ν) := by
    simp_rw [jointObs_graftOrigin]
    exact integral_const_mul _ _
  rw [heq, Set.indicator_of_mem (show ω₁ ∈ {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} from h),
    one_mul]
  have hcount : (unshiftOrigin ω₁).1 (0 : Site d) = (k : ℤ) - 1 := by
    rw [unshiftOrigin_eta_zero, h]
  have hc : 0 ≤ (unshiftOrigin ω₁).1 (0 : Site d) := by
    rw [hcount]
    have h1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    omega
  have hb := integral_graftSurvivalObs_le_exp hd hint hexp hlam₁ hlam₁θ hnonpos
    (originMoveOf ω₁) (injective_originRank_unshiftOrigin hinj) hc t
  have hcast : (((unshiftOrigin ω₁).1 (0 : Site d)).toNat : ℝ) = (k : ℝ) - 1 := by
    rw [hcount]
    have h1 : ((k : ℤ) - 1).toNat = k - 1 := by omega
    rw [h1]
    have h2 : (1 : ℕ) ≤ k := hk
    push_cast [Nat.cast_sub h2]
    ring
  rw [hcast] at hb
  exact hb

/-- The walk average of the bound of `eq:range-upper` factorizes. -/
theorem integral_exp_sub_rangeCard (A B a : ℝ) (t : ℕ) :
    ∫ p, Real.exp A * Real.exp (B - a * (rangeCard (0 : Site d) p t : ℝ)) ∂(walkLaw d)
      = Real.exp A * (Real.exp B
        * ∫ p, Real.exp (-(a * (rangeCard (0 : Site d) p t : ℝ))) ∂(walkLaw d)) := by
  have hpt : ∀ p : ℕ → Fin d × Bool,
      Real.exp A * Real.exp (B - a * (rangeCard (0 : Site d) p t : ℝ))
        = (Real.exp A * Real.exp B) * Real.exp (-(a * (rangeCard (0 : Site d) p t : ℝ))) := by
    intro p
    rw [show B - a * (rangeCard (0 : Site d) p t : ℝ)
      = B + -(a * (rangeCard (0 : Site d) p t : ℝ)) by ring, Real.exp_add]
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  ring

/-- **The joint bound.**  `P(η(0) = k, τ₁ > t) ≤ ν{k} e^{A} e^{λ₁(k-1)/3} E₀ e^{-a|R_t|}`. -/
theorem integral_jointObs_le (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) {θ : ℝ}
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    {lam₁ : ℝ} (hlam₁ : 0 < lam₁) (hlam₁θ : lam₁ < θ)
    (hnonpos : ∀ s ∈ Set.Icc (0 : ℝ) lam₁,
      Integrable (fun k : ℤ => (k : ℝ)) (tiltLaw ν s) ∧
      ∫ k, (k : ℝ) ∂(tiltLaw ν s) ≤ 0)
    (k : ℕ) (hk : 1 ≤ k) (t : ℕ) :
    ∫ ω, jointObs k t ω ∂(pDataLaw d ν)
      ≤ (ν {(k : ℤ)}).toReal
        * (Real.exp ((1 / 3) * ∫ s in (0 : ℝ)..lam₁, ∫ j, |(j : ℝ)| ∂(tiltLaw ν s))
          * (Real.exp (lam₁ * ((k : ℝ) - 1) / 3)
            * ∫ p, Real.exp (-(((1 / 3) * ∫ s in (0 : ℝ)..lam₁, drift ν s)
                * (rangeCard (0 : Site d) p t : ℝ))) ∂(walkLaw d))) := by
  classical
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI : IsProbabilityMeasure (stepLaw d) := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (moveLaw d) := by unfold moveLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  haveI : IsProbabilityMeasure (noiseLaw d) := by unfold noiseLaw; infer_instance
  haveI : IsProbabilityMeasure (pDataLaw d ν) := by unfold pDataLaw; infer_instance
  set a : ℝ := (1 / 3) * ∫ s in (0 : ℝ)..lam₁, drift ν s with hadef
  set A : ℝ := (1 / 3) * ∫ s in (0 : ℝ)..lam₁, ∫ j, |(j : ℝ)| ∂(tiltLaw ν s) with hAdef
  have ha0 : 0 ≤ a := drift_intervalIntegral_nonneg hlam₁.le fun s hs => (hnonpos s hs).2
  set Bd : (ℕ → Fin d × Bool) → ℝ := fun p =>
    Real.exp A * Real.exp (lam₁ * ((k : ℝ) - 1) / 3
      - a * (rangeCard (0 : Site d) p t : ℝ)) with hBdef
  have hBm : Measurable Bd := by
    rw [hBdef]
    exact measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.sub (measurable_const.mul (measurable_rangeCard_walk t))))
  have hBb : ∀ p, |Bd p| ≤ Real.exp A * Real.exp (lam₁ * ((k : ℝ) - 1) / 3) := by
    intro p
    have hrc : (0 : ℝ) ≤ a * (rangeCard (0 : Site d) p t : ℝ) :=
      mul_nonneg ha0 (Nat.cast_nonneg _)
    have hval : Bd p = Real.exp A * Real.exp (lam₁ * ((k : ℝ) - 1) / 3
        - a * (rangeCard (0 : Site d) p t : ℝ)) := by rw [hBdef]
    have hnn : (0 : ℝ) ≤ Bd p := by
      rw [hval]
      exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    rw [abs_of_nonneg hnn, hval]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
  have hjm : Measurable (jointObs (d := d) k t) := measurable_jointObs k t
  have hΦm : Measurable fun p : PData d × PData d => jointObs k t (graftOrigin p.1 p.2) :=
    hjm.comp measurable_graftOrigin_pair
  have hΦint : Integrable (fun p : PData d × PData d => jointObs k t (graftOrigin p.1 p.2))
      ((pDataLaw d ν).prod (pDataLaw d ν)) := by
    refine (integrable_const (1 : ℝ)).mono' hΦm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (jointObs_nonneg k t _)]
    exact jointObs_le_one k t _
  have hsplit : ∫ ω, jointObs k t ω ∂(pDataLaw d ν)
      = ∫ p, jointObs k t (graftOrigin p.1 p.2) ∂((pDataLaw d ν).prod (pDataLaw d ν)) := by
    have h := integral_map (μ := (pDataLaw d ν).prod (pDataLaw d ν))
      (φ := fun p : PData d × PData d => graftOrigin p.1 p.2) (f := jointObs k t)
      measurable_graftOrigin_pair.aemeasurable
      (by rw [(measurePreserving_graftOrigin hd ν).map_eq]; exact hjm.aestronglyMeasurable)
    rw [(measurePreserving_graftOrigin hd ν).map_eq] at h
    exact h
  have hfub := integral_prod _ hΦint
  have hcnt : MeasurableSet {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} := by
    have hm : Measurable fun ω : PData d => ω.1 (0 : Site d) :=
      (measurable_pi_apply (0 : Site d)).comp measurable_fst
    exact hm (measurableSet_singleton ((k : ℤ)))
  have hinner : ∀ᵐ ω₁ ∂(pDataLaw d ν),
      (∫ ω, jointObs k t (graftOrigin ω₁ ω) ∂(pDataLaw d ν))
        ≤ Set.indicator {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} (fun _ => (1 : ℝ)) ω₁
          * Bd (originMoveOf ω₁) := by
    filter_upwards [ae_injective_pDataLaw hd ν] with ω₁ hinj
    by_cases h : ω₁.1 (0 : Site d) = (k : ℤ)
    · rw [Set.indicator_of_mem (show ω₁ ∈ {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} from h),
        one_mul, hBdef]
      exact integral_jointObs_graftOrigin_le hd hint hexp hlam₁ hlam₁θ hnonpos k hk t hinj h
    · have hz : ∀ ω : PData d, jointObs k t (graftOrigin ω₁ ω) = 0 := by
        intro ω
        rw [jointObs_graftOrigin, Set.indicator_of_notMem
          (show ω₁ ∉ {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} from h), zero_mul]
      rw [Set.indicator_of_notMem
        (show ω₁ ∉ {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} from h), zero_mul]
      simp_rw [hz]
      simp
  have hIint : Integrable
      (fun ω₁ => ∫ ω, jointObs k t (graftOrigin ω₁ ω) ∂(pDataLaw d ν)) (pDataLaw d ν) :=
    hΦint.integral_prod_left
  have hIconst : Integrable (fun ω₁ : PData d =>
      Set.indicator {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)} (fun _ => (1 : ℝ)) ω₁
        * Bd (originMoveOf ω₁)) (pDataLaw d ν) := by
    refine (integrable_const (Real.exp A * Real.exp (lam₁ * ((k : ℝ) - 1) / 3))).mono'
      ((measurable_const.indicator hcnt).mul
        (hBm.comp measurable_originMoveOf)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω₁ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |Set.indicator {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)}
        (fun _ => (1 : ℝ)) ω₁| ≤ 1 := by
      rw [Set.indicator_apply]; split_ifs <;> norm_num
    have h2 := hBb (originMoveOf ω₁)
    have h3 : (0 : ℝ) ≤ |Bd (originMoveOf ω₁)| := abs_nonneg _
    nlinarith [abs_nonneg (Set.indicator {ω' : PData d | ω'.1 (0 : Site d) = (k : ℤ)}
      (fun _ => (1 : ℝ)) ω₁)]
  have hmono := integral_mono_ae hIint hIconst hinner
  have hBint : ∫ p, Bd p ∂(walkLaw d)
      = Real.exp A * (Real.exp (lam₁ * ((k : ℝ) - 1) / 3)
        * ∫ p, Real.exp (-(a * (rangeCard (0 : Site d) p t : ℝ))) ∂(walkLaw d)) := by
    rw [hBdef]
    exact integral_exp_sub_rangeCard A (lam₁ * ((k : ℝ) - 1) / 3) a t
  rw [hsplit, hfub]
  refine le_trans hmono ?_
  rw [integral_indicator_mul_originMove hd k hBm hBb, hBint]


/-- Markov's inequality at one atom. -/
theorem measureReal_singleton_mul_exp_le (ν : Measure ℤ) {θ : ℝ}
    (hexp : Integrable (fun j : ℤ => Real.exp (θ * j)) ν) (m : ℤ) :
    (ν {m}).toReal * Real.exp (θ * m) ≤ ∫ j, Real.exp (θ * j) ∂ν := by
  have hnn : (0 : ℤ → ℝ) ≤ᵐ[ν] fun j : ℤ => Real.exp (θ * j) :=
    Filter.Eventually.of_forall fun j => (Real.exp_pos _).le
  have h1 : ∫ j in ({m} : Set ℤ), Real.exp (θ * j) ∂ν ≤ ∫ j, Real.exp (θ * j) ∂ν :=
    setIntegral_le_integral hexp hnn
  rw [integral_singleton, smul_eq_mul, measureReal_def] at h1
  exact h1

/-- **The termwise bound behind the constant of `thm:subcritical`.**  Markov at
the atom `m+1` turns the weight into a geometric one. -/
theorem exp_weight_le (ν : Measure ℤ) {θ lam₁ : ℝ} (hlam₁ : 0 < lam₁) (hlam₁θ : lam₁ < θ)
    (hexp : Integrable (fun j : ℤ => Real.exp (θ * j)) ν) (m : ℕ) :
    ((m : ℝ) + 1) * (ν {(m : ℤ) + 1}).toReal * Real.exp (lam₁ * (m : ℝ) / 3)
      ≤ (∫ j, Real.exp (θ * j) ∂ν) * Real.exp (-θ)
        * (((m : ℝ) + 1) * Real.exp (-(θ - lam₁ / 3)) ^ m) := by
  have hθ : 0 < θ := lt_trans hlam₁ hlam₁θ
  have hmk := measureReal_singleton_mul_exp_le ν hexp ((m : ℤ) + 1)
  have hcast : ((((m : ℤ) + 1 : ℤ)) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hmk
  have hEpos : (0 : ℝ) < Real.exp (θ * ((m : ℝ) + 1)) := Real.exp_pos _
  have hp : (ν {(m : ℤ) + 1}).toReal
      ≤ (∫ j, Real.exp (θ * j) ∂ν) / Real.exp (θ * ((m : ℝ) + 1)) :=
    (le_div_iff₀ hEpos).mpr hmk
  have hrm : Real.exp (-(θ - lam₁ / 3)) ^ m = Real.exp (-((θ - lam₁ / 3) * (m : ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h0 : (0 : ℝ) ≤ ((m : ℝ) + 1) := by positivity
  have h1 : (0 : ℝ) ≤ Real.exp (lam₁ * (m : ℝ) / 3) := (Real.exp_pos _).le
  have hstep : ((m : ℝ) + 1) * (ν {(m : ℤ) + 1}).toReal * Real.exp (lam₁ * (m : ℝ) / 3)
      ≤ ((m : ℝ) + 1) * ((∫ j, Real.exp (θ * j) ∂ν) / Real.exp (θ * ((m : ℝ) + 1)))
        * Real.exp (lam₁ * (m : ℝ) / 3) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp h0) h1
  refine le_trans hstep (le_of_eq ?_)
  rw [hrm, div_eq_mul_inv, ← Real.exp_neg,
    show -(θ * ((m : ℝ) + 1)) = -θ + -(θ * (m : ℝ)) by ring, Real.exp_add,
    show -((θ - lam₁ / 3) * (m : ℝ)) = -(θ * (m : ℝ)) + lam₁ * (m : ℝ) / 3 by ring,
    Real.exp_add]
  ring

/-- The weighted atom sum of an integer law with an exponential moment. -/
theorem summable_exp_weight (ν : Measure ℤ) {θ lam₁ : ℝ} (hlam₁ : 0 < lam₁)
    (hlam₁θ : lam₁ < θ) (hexp : Integrable (fun j : ℤ => Real.exp (θ * j)) ν) :
    Summable (fun m : ℕ => ((m : ℝ) + 1) * (ν {(m : ℤ) + 1}).toReal
      * Real.exp (lam₁ * (m : ℝ) / 3)) := by
  have hθ : 0 < θ := lt_trans hlam₁ hlam₁θ
  have hM0 : (0:ℝ) ≤ ∫ j, Real.exp (θ * j) ∂ν := integral_nonneg fun j => (Real.exp_pos _).le
  have hβ : 0 < θ - lam₁ / 3 := by linarith
  have hr1 : ‖Real.exp (-(θ - lam₁ / 3))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeo : Summable (fun m : ℕ => ((m : ℝ) + 1) * Real.exp (-(θ - lam₁ / 3)) ^ m) := by
    have h1 : Summable (fun m : ℕ => (m : ℝ) ^ 1 * Real.exp (-(θ - lam₁ / 3)) ^ m) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 hr1
    have h2 : Summable (fun m : ℕ => Real.exp (-(θ - lam₁ / 3)) ^ m) :=
      summable_geometric_of_norm_lt_one hr1
    refine (h1.add h2).congr fun m => ?_
    ring
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
    (hgeo.mul_left ((∫ j, Real.exp (θ * j) ∂ν) * Real.exp (-θ)))
  · exact mul_nonneg (mul_nonneg (by positivity) ENNReal.toReal_nonneg) (Real.exp_pos _).le
  · exact exp_weight_le ν hlam₁ hlam₁θ hexp m

/-- The constant of the last assertion of `thm:subcritical`: the exponential of
the tilting integral times the exponential moment `∑ (m+1) ν{m+1} e^{λ₁m/3}` that
the sum over `k` produces. -/
def subcriticalConst (ν : Measure ℤ) (lam₁ : ℝ) : ℝ :=
  Real.exp ((1 / 3) * ∫ s in (0 : ℝ)..lam₁, ∫ j, |(j : ℝ)| ∂(tiltLaw ν s))
    * ∑' m : ℕ, ((m : ℝ) + 1) * (ν {(m : ℤ) + 1}).toReal * Real.exp (lam₁ * (m : ℝ) / 3)

theorem subcriticalConst_nonneg (ν : Measure ℤ) (lam₁ : ℝ) : 0 ≤ subcriticalConst ν lam₁ := by
  refine mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun m => ?_)
  exact mul_nonneg (mul_nonneg (by positivity) ENNReal.toReal_nonneg) (Real.exp_pos _).le

/-- **The constant of `thm:subcritical` is bounded by the exponential moment.**
This is the form a family of laws with a uniform exponential moment needs: the
sum on the right depends on `θ` and `λ₁` alone. -/
theorem subcriticalConst_le (ν : Measure ℤ) {θ lam₁ : ℝ} (hlam₁ : 0 < lam₁)
    (hlam₁θ : lam₁ < θ) (hexp : Integrable (fun j : ℤ => Real.exp (θ * j)) ν) :
    subcriticalConst ν lam₁
      ≤ Real.exp ((1 / 3) * ∫ s in (0 : ℝ)..lam₁, ∫ j, |(j : ℝ)| ∂(tiltLaw ν s))
        * ((∫ j, Real.exp (θ * j) ∂ν) * Real.exp (-θ)
          * ∑' m : ℕ, ((m : ℝ) + 1) * Real.exp (-(θ - lam₁ / 3)) ^ m) := by
  have hθ : 0 < θ := lt_trans hlam₁ hlam₁θ
  have hr1 : ‖Real.exp (-(θ - lam₁ / 3))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeo : Summable (fun m : ℕ => ((m : ℝ) + 1) * Real.exp (-(θ - lam₁ / 3)) ^ m) := by
    have h1 : Summable (fun m : ℕ => (m : ℝ) ^ 1 * Real.exp (-(θ - lam₁ / 3)) ^ m) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 hr1
    have h2 : Summable (fun m : ℕ => Real.exp (-(θ - lam₁ / 3)) ^ m) :=
      summable_geometric_of_norm_lt_one hr1
    refine (h1.add h2).congr fun m => ?_
    ring
  have hmaj : Summable (fun m : ℕ => ((∫ j, Real.exp (θ * j) ∂ν) * Real.exp (-θ))
      * (((m : ℝ) + 1) * Real.exp (-(θ - lam₁ / 3)) ^ m)) := hgeo.mul_left _
  have hle : (∑' m : ℕ, ((m : ℝ) + 1) * (ν {(m : ℤ) + 1}).toReal
        * Real.exp (lam₁ * (m : ℝ) / 3))
      ≤ (∫ j, Real.exp (θ * j) ∂ν) * Real.exp (-θ)
        * ∑' m : ℕ, ((m : ℝ) + 1) * Real.exp (-(θ - lam₁ / 3)) ^ m := by
    calc (∑' m : ℕ, ((m : ℝ) + 1) * (ν {(m : ℤ) + 1}).toReal
            * Real.exp (lam₁ * (m : ℝ) / 3))
        ≤ ∑' m : ℕ, ((∫ j, Real.exp (θ * j) ∂ν) * Real.exp (-θ))
            * (((m : ℝ) + 1) * Real.exp (-(θ - lam₁ / 3)) ^ m) :=
          (summable_exp_weight ν hlam₁ hlam₁θ hexp).tsum_le_tsum
            (fun m => by
              have h := exp_weight_le ν hlam₁ hlam₁θ hexp m
              calc ((m : ℝ) + 1) * (ν {(m : ℤ) + 1}).toReal * Real.exp (lam₁ * (m : ℝ) / 3)
                  ≤ (∫ j, Real.exp (θ * j) ∂ν) * Real.exp (-θ)
                      * (((m : ℝ) + 1) * Real.exp (-(θ - lam₁ / 3)) ^ m) := h
                _ = ((∫ j, Real.exp (θ * j) ∂ν) * Real.exp (-θ))
                      * (((m : ℝ) + 1) * Real.exp (-(θ - lam₁ / 3)) ^ m) := by ring) hmaj
      _ = ((∫ j, Real.exp (θ * j) ∂ν) * Real.exp (-θ))
            * ∑' m : ℕ, ((m : ℝ) + 1) * Real.exp (-(θ - lam₁ / 3)) ^ m := tsum_mul_left
      _ = (∫ j, Real.exp (θ * j) ∂ν) * Real.exp (-θ)
            * ∑' m : ℕ, ((m : ℝ) + 1) * Real.exp (-(θ - lam₁ / 3)) ^ m := by ring
  rw [subcriticalConst]
  exact mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le

/-- `E₀ e^{-a|R_t|}` is nonnegative. -/
theorem rangeExp_nonneg (d : ℕ) (a : ℝ) (t : ℕ) : 0 ≤ rangeExp d a t := by
  rw [rangeExp]
  exact integral_nonneg fun p => (Real.exp_pos _).le

/-- The number of survivors from the origin is integrable. -/
theorem integrable_survivorsFrom_law (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (t : ℕ) :
    Integrable (fun ω => (LatticeProb.survivorsFrom (toDriver ω) t 0 : ℝ)) (law d ν) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hti : TranslationInvariant (LatticeProb.iidLaw d ν) := fun v => iidLaw_map_shiftConf' ν v
  have hmap : (LatticeProb.iidLaw d ν).map (fun η : Site d → ℤ => η 0) = ν := by
    show (Measure.infinitePi fun _ : Site d => ν).map (fun η : Site d → ℤ => η 0) = ν
    exact Measure.infinitePi_map_eval _ 0
  have hint' : Integrable (fun η : Site d → ℤ => |((η 0 : ℤ) : ℝ)|)
      (LatticeProb.iidLaw d ν) := by
    refine (integrable_map_measure (g := fun k : ℤ => |(k : ℝ)|)
      (f := fun η : Site d → ℤ => η 0) (μ := LatticeProb.iidLaw d ν) ?_
      (measurable_pi_apply (0 : Site d)).aemeasurable).mp ?_
    · rw [hmap]; exact hint.aestronglyMeasurable
    · rw [hmap]; exact hint
  show Integrable _ (dataLaw d (LatticeProb.iidLaw d ν))
  exact integrable_survivorsFrom_data hd hti hint' t 0

/-- **The last assertion of `thm:subcritical`, with the constant explicit**:
`S_t ≤ subcriticalConst · E₀ e^{-a|R_t|}`. -/
theorem S_le_subcriticalConst (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) {θ : ℝ}
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    {lam₁ : ℝ} (hlam₁ : 0 < lam₁) (hlam₁θ : lam₁ < θ)
    (hnonpos : ∀ s ∈ Set.Icc (0 : ℝ) lam₁,
      Integrable (fun k : ℤ => (k : ℝ)) (tiltLaw ν s) ∧
      ∫ k, (k : ℝ) ∂(tiltLaw ν s) ≤ 0) (t : ℕ) :
    S (law d ν) t
      ≤ subcriticalConst ν lam₁ * rangeExp d ((1 / 3) * ∫ s in (0 : ℝ)..lam₁, drift ν s) t := by
  classical
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hlaw : law d ν = dataLaw d (LatticeProb.iidLaw d ν) := rfl
  set A : ℝ := Real.exp ((1 / 3) * ∫ s in (0 : ℝ)..lam₁, ∫ j, |(j : ℝ)| ∂(tiltLaw ν s))
    with hAdef
  set u : ℕ → ℝ := fun m => ((m : ℝ) + 1) * (ν {(m : ℤ) + 1}).toReal
    * Real.exp (lam₁ * (m : ℝ) / 3) with hudef
  have hu : Summable u := summable_exp_weight ν hlam₁ hlam₁θ hexp
  obtain ⟨hsum, hSeq⟩ := S_expansion hd (LatticeProb.iidLaw d ν) t
    (by
      have := integrable_survivorsFrom_law hd hint (ν := ν) t
      rwa [hlaw] at this)
  set I : ℝ := rangeExp d ((1 / 3) * ∫ s in (0 : ℝ)..lam₁, drift ν s) t with hIdef
  have hI0 : 0 ≤ I := by
    rw [hIdef]
    exact rangeExp_nonneg d _ t
  set f : ℕ → ℝ := fun m => ((m : ℝ) + 1) *
    ((dataLaw d (LatticeProb.iidLaw d ν)) {ω : Data d | ω.1 0 = (m : ℤ) + 1 ∧
      (LatticeProb.state (toDriver ω) t).active (0, 0) = true}).toReal with hfdef
  have hfle : ∀ m : ℕ, f m ≤ u m * (A * I) := by
    intro m
    have hcast : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
    have hcastR : (((m + 1 : ℕ) : ℝ) - 1) = (m : ℝ) := by push_cast; ring
    have h1 := integral_jointObs_eq hd ν (m + 1) t
    have h2 := integral_jointObs_le hd hint hexp hlam₁ hlam₁θ hnonpos (m + 1)
      (Nat.le_add_left 1 m) t
    rw [h1, hcast, hcastR] at h2
    have h0 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
    have h3 := mul_le_mul_of_nonneg_left h2 h0
    rw [hfdef, hudef, hIdef, rangeExp, hlaw] at *
    calc ((m : ℝ) + 1) * ((dataLaw d (LatticeProb.iidLaw d ν))
            {ω : Data d | ω.1 0 = (m : ℤ) + 1 ∧
              (LatticeProb.state (toDriver ω) t).active (0, 0) = true}).toReal
        ≤ ((m : ℝ) + 1) * ((ν {(m : ℤ) + 1}).toReal
            * (A * (Real.exp (lam₁ * (m : ℝ) / 3) * I))) := h3
      _ = ((m : ℝ) + 1) * (ν {(m : ℤ) + 1}).toReal * Real.exp (lam₁ * (m : ℝ) / 3)
            * (A * I) := by ring
  have hmaj : Summable (fun m : ℕ => u m * (A * I)) := hu.mul_right _
  calc S (law d ν) t = ∑' m : ℕ, f m := by rw [hlaw]; exact hSeq
    _ ≤ ∑' m : ℕ, u m * (A * I) := hsum.tsum_le_tsum hfle hmaj
    _ = (∑' m : ℕ, u m) * (A * I) := tsum_mul_right
    _ = (A * ∑' m : ℕ, u m) * I := by ring
    _ = subcriticalConst ν lam₁ * I := by rw [subcriticalConst, hAdef, hudef]

/-- **The last assertion of `thm:subcritical`**: `S_t ≤ C E₀ e^{-a|R_t|}`. -/
theorem S_le_rangeExp (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) {θ : ℝ}
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    {lam₁ : ℝ} (hlam₁ : 0 < lam₁) (hlam₁θ : lam₁ < θ)
    (hnonpos : ∀ s ∈ Set.Icc (0 : ℝ) lam₁,
      Integrable (fun k : ℤ => (k : ℝ)) (tiltLaw ν s) ∧
      ∫ k, (k : ℝ) ∂(tiltLaw ν s) ≤ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ,
      Integrable (fun ω => (LatticeProb.survivorsFrom (toDriver ω) t 0 : ℝ)) (law d ν) ∧
      S (law d ν) t
        ≤ C * ∫ p, Real.exp (-(((1 / 3) * ∫ s in (0 : ℝ)..lam₁, drift ν s)
            * (rangeCard (0 : Site d) p t : ℝ))) ∂(walkLaw d) := by
  refine ⟨max 1 (subcriticalConst ν lam₁),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun t => ?_⟩
  refine ⟨integrable_survivorsFrom_law hd hint t, ?_⟩
  have hI0 : (0 : ℝ) ≤ rangeExp d ((1 / 3) * ∫ s in (0 : ℝ)..lam₁, drift ν s) t :=
    rangeExp_nonneg d _ t
  exact le_trans (S_le_subcriticalConst hd hint hexp hlam₁ hlam₁θ hnonpos t)
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hI0)

end Parking

end
