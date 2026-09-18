/-
Step 2 of the proof of `prop:resolvent` (`parking.tex:2693-2706`):

  "For every integer `m ≥ 2`, `E_0 e^{-a|R_t|} ≤ P_0(|R_t| < m) + e^{-am}`."

The threshold is taken at `blockThreshold d n`, half the expected range at the
horizon `n`, which is the largest threshold for which Step 1 applies at that
horizon; the paper instead fixes `m` and chooses the horizon, and the two
readings differ only by the constants.  This file also carries the bridge from
the signed-direction walk model in which `Parking.rangeExp` is stated to the
position paths of the library, in which Step 1 is proved.
-/
import Parking.Support.BlockTail
import Parking.Support.RoundHitting

open MeasureTheory

noncomputable section

namespace Parking

variable {d : ℕ}

/-- The law of the position path of the signed-direction walk is the law of the
simple random walk on position paths. -/
theorem map_walkLaw_walkPath (hd : 1 ≤ d) (x : Site d) :
    (Parking.walkLaw d).map (Parking.walkPath x) = LatticeProb.siteWalkLaw d x := by
  haveI : NeZero d := ⟨by omega⟩
  haveI := Parking.stepLaw_isProbability hd
  let M : (ℕ → Fin d × Bool) → ℕ → Site d := fun p n => Parking.stepVec (p n)
  have hM : Measurable M := measurable_pi_lambda _ fun n =>
    (measurable_of_countable Parking.stepVec).comp (measurable_pi_apply n)
  have hMLaw : (Parking.walkLaw d).map M
      = Measure.infinitePi fun _ : ℕ => LatticeProb.incLaw d := by
    rw [Parking.walkLaw,
      LatticeProb.infinitePi_map_pi (Parking.stepLaw d)
        (measurable_of_countable Parking.stepVec), Parking.map_stepLaw_stepVec]
    rfl
  have heq : Parking.walkPath x = LatticeProb.sitePath x ∘ M :=
    funext fun p => funext fun t => Parking.walkPath_eq_sitePath x p t
  rw [heq, ← Measure.map_map (LatticeProb.measurable_sitePath x) hM, hMLaw]
  rfl

/-- The two readings of the range agree. -/
theorem rangeCard_eq_rangeCard (x : Site d) (p : ℕ → Fin d × Bool) (t : ℕ) :
    Parking.rangeCard x p t = LatticeProb.rangeCard (Parking.walkPath x p) t := rfl

/-- `E_0 e^{-a|R_t|}` read on position paths. -/
theorem rangeExp_eq (hd : 1 ≤ d) (a : ℝ) (t : ℕ) :
    rangeExp d a t
      = ∫ X, Real.exp (-(a * (LatticeProb.rangeCard X t : ℝ)))
          ∂(LatticeProb.siteWalkLaw d 0) := by
  haveI : NeZero d := ⟨by omega⟩
  have hwm : Measurable (Parking.walkPath (0 : Site d)) :=
    measurable_pi_lambda _ fun j => Parking.measurable_walkPath 0 j
  have hfm : Measurable fun X : ℕ → Site d =>
      Real.exp (-(a * (LatticeProb.rangeCard X t : ℝ))) :=
    (LatticeProb.measurable_from_countable'
      (fun k : ℕ => Real.exp (-(a * (k : ℝ))))).comp (LatticeProb.measurable_rangeCard t)
  rw [← map_walkLaw_walkPath hd (0 : Site d),
    integral_map hwm.aemeasurable hfm.aestronglyMeasurable]
  rfl


/-- The geometric factor of Step 1 as an exponential: `(7/8)^{⌊t/n⌋}` is at most
`(8/7) e^{-γ t/n}` with `γ = log(8/7)`. -/
theorem pow_seven_eighths_le (n t : ℕ) (hn : 1 ≤ n) :
    (7 / 8 : ℝ) ^ (t / n)
      ≤ (8 / 7) * Real.exp (-(Real.log (8 / 7) * (t : ℝ) / (n : ℝ))) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hg : 0 < Real.log (8 / 7) := Real.log_pos (by norm_num)
  have hlt : t < n * (t / n) + n := by
    have h1 : t % n < n := Nat.mod_lt t (by omega)
    have h2 : n * (t / n) + t % n = t := Nat.div_add_mod t n
    omega
  have h3 : (t : ℝ) < (n : ℝ) * ((t / n : ℕ) : ℝ) + (n : ℝ) := by exact_mod_cast hlt
  have hreal : (t : ℝ) / (n : ℝ) - 1 ≤ ((t / n : ℕ) : ℝ) := by
    rw [sub_le_iff_le_add, div_le_iff₀ hn0]
    nlinarith
  have hpow : (7 / 8 : ℝ) ^ (t / n)
      = Real.exp (-(Real.log (8 / 7) * ((t / n : ℕ) : ℝ))) := by
    rw [show -(Real.log (8 / 7) * ((t / n : ℕ) : ℝ))
        = ((t / n : ℕ) : ℝ) * (-(Real.log (8 / 7))) by ring, Real.exp_nat_mul]
    congr 1
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 8 / 7)]
    norm_num
  rw [hpow]
  have hgoal : -(Real.log (8 / 7) * ((t / n : ℕ) : ℝ))
      ≤ Real.log (8 / 7) + -(Real.log (8 / 7) * (t : ℝ) / (n : ℝ)) := by
    have hdiv : Real.log (8 / 7) * (t : ℝ) / (n : ℝ)
        = Real.log (8 / 7) * ((t : ℝ) / (n : ℝ)) := by ring
    rw [hdiv]
    nlinarith [hreal, hg]
  calc Real.exp (-(Real.log (8 / 7) * ((t / n : ℕ) : ℝ)))
      ≤ Real.exp (Real.log (8 / 7) + -(Real.log (8 / 7) * (t : ℝ) / (n : ℝ))) :=
        Real.exp_le_exp.mpr hgoal
    _ = 8 / 7 * Real.exp (-(Real.log (8 / 7) * (t : ℝ) / (n : ℝ))) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 8 / 7)]

/-- **Step 2 of `prop:resolvent`**: `E_0 e^{-a|R_t|} ≤ P_0(|R_t| < m) + e^{-am}`
(`parking.tex:2695-2697`). -/
theorem rangeExp_le_add (hd : 1 ≤ d) {a : ℝ} (ha : 0 < a) (m t : ℕ) :
    rangeExp d a t
      ≤ (LatticeProb.siteWalkLaw d 0).real
          {X : ℕ → Site d | LatticeProb.rangeCard X t < m} + Real.exp (-(a * (m : ℝ))) := by
  haveI : NeZero d := ⟨by omega⟩
  rw [rangeExp_eq hd]
  set S : Set (ℕ → Site d) := {X : ℕ → Site d | LatticeProb.rangeCard X t < m} with hS
  have hSm : MeasurableSet S := measurableSet_rangeCard_lt t m
  have hfm : Measurable fun X : ℕ → Site d =>
      Real.exp (-(a * (LatticeProb.rangeCard X t : ℝ))) :=
    (LatticeProb.measurable_from_countable'
      (fun k : ℕ => Real.exp (-(a * (k : ℝ))))).comp (LatticeProb.measurable_rangeCard t)
  have hpt : ∀ X : ℕ → Site d,
      Real.exp (-(a * (LatticeProb.rangeCard X t : ℝ)))
        ≤ S.indicator 1 X + Real.exp (-(a * (m : ℝ))) := by
    intro X
    have hpos : (0 : ℝ) ≤ (LatticeProb.rangeCard X t : ℝ) := by positivity
    have hexp : (0 : ℝ) < Real.exp (-(a * (m : ℝ))) := Real.exp_pos _
    by_cases hX : X ∈ S
    · rw [Set.indicator_of_mem hX]
      have h1 : Real.exp (-(a * (LatticeProb.rangeCard X t : ℝ))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith)
      simp only [Pi.one_apply]
      linarith
    · rw [Set.indicator_of_notMem hX]
      have hge : (m : ℝ) ≤ (LatticeProb.rangeCard X t : ℝ) := by
        simp only [hS, Set.mem_setOf_eq, not_lt] at hX
        exact_mod_cast hX
      have h1 : Real.exp (-(a * (LatticeProb.rangeCard X t : ℝ)))
          ≤ Real.exp (-(a * (m : ℝ))) := Real.exp_le_exp.mpr (by nlinarith)
      linarith
  have hind : Integrable (fun X : ℕ → Site d => S.indicator 1 X)
      (LatticeProb.siteWalkLaw d 0) := (integrable_const (1 : ℝ)).indicator hSm
  have hint1 : Integrable (fun X : ℕ → Site d =>
      Real.exp (-(a * (LatticeProb.rangeCard X t : ℝ)))) (LatticeProb.siteWalkLaw d 0) := by
    refine Integrable.of_bound hfm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun X => ?_)
    have hpos : (0 : ℝ) ≤ (LatticeProb.rangeCard X t : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hint2 : Integrable (fun X : ℕ → Site d =>
      S.indicator 1 X + Real.exp (-(a * (m : ℝ)))) (LatticeProb.siteWalkLaw d 0) :=
    hind.add (integrable_const _)
  calc ∫ X, Real.exp (-(a * (LatticeProb.rangeCard X t : ℝ)))
          ∂(LatticeProb.siteWalkLaw d 0)
      ≤ ∫ X, (S.indicator 1 X + Real.exp (-(a * (m : ℝ))))
          ∂(LatticeProb.siteWalkLaw d 0) := integral_mono hint1 hint2 hpt
    _ = (LatticeProb.siteWalkLaw d 0).real S + Real.exp (-(a * (m : ℝ))) := by
        rw [integral_add hind (integrable_const _), integral_indicator_one hSm]
        simp


theorem ceil_le_two_mul {x : ℝ} (hx : 1 ≤ x) : ((⌈x⌉₊ : ℕ) : ℝ) ≤ 2 * x := by
  have h0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
  have h := Nat.ceil_lt_add_one h0
  linarith

/-- **The pointwise bound of Steps 1 and 2 at a free horizon.**  For every
horizon `n ≥ 1`,

    E_0 e^{-a|R_t|} ≤ C (e^{-c t/n} + e^{-c a (n+1)/φ_d(n)}) ,

the first term the geometric lower tail of Step 1 and the second the
exponential of Step 2.  The optimization of `eq:resolvent-pointwise` is the
choice of `n` in this bound. -/
theorem exists_rangeExp_horizon_bound (hd : 1 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ n t : ℕ, 1 ≤ n →
      rangeExp d a t
        ≤ C * (Real.exp (-(c * (t : ℝ) / (n : ℝ)))
          + Real.exp (-(c * a * (((n : ℝ) + 1) / greenScale d n)))) := by
  obtain ⟨c₀, hc₀, hthr⟩ := blockThreshold_lower (d := d) hd
  refine ⟨min (Real.log (8 / 7)) c₀, Real.exp 1,
    lt_min (Real.log_pos (by norm_num)) hc₀, Real.exp_pos 1, fun a ha ha1 n t hn => ?_⟩
  have hq : (0 : ℝ) < ((n : ℝ) + 1) / greenScale d n :=
    div_pos (by positivity) (greenScale_pos d n)
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  have hstep1 := rangeExp_le_add hd ha (blockThreshold d n) t
  have hstep2 := rangeTail_le hd n t (0 : Site d)
  have hstep3 := pow_seven_eighths_le n t hn
  have hthrn := hthr n
  have hmin1 : min (Real.log (8 / 7)) c₀ ≤ Real.log (8 / 7) := min_le_left _ _
  have hmin2 : min (Real.log (8 / 7)) c₀ ≤ c₀ := min_le_right _ _
  have hexp2 : Real.exp (-(a * (blockThreshold d n : ℝ)))
      ≤ Real.exp 1
        * Real.exp (-(min (Real.log (8 / 7)) c₀ * a * (((n : ℝ) + 1) / greenScale d n))) := by
    have h1 : min (Real.log (8 / 7)) c₀ * a * (((n : ℝ) + 1) / greenScale d n)
        ≤ a * (blockThreshold d n : ℝ) + a := by
      have hqa : (0 : ℝ) ≤ a * (((n : ℝ) + 1) / greenScale d n) := by positivity
      have hA : min (Real.log (8 / 7)) c₀ * (a * (((n : ℝ) + 1) / greenScale d n))
          ≤ c₀ * (a * (((n : ℝ) + 1) / greenScale d n)) :=
        mul_le_mul_of_nonneg_right hmin2 hqa
      have hC : a * (c₀ * (((n : ℝ) + 1) / greenScale d n) - 1)
          ≤ a * (blockThreshold d n : ℝ) := mul_le_mul_of_nonneg_left hthrn ha.le
      nlinarith [hA, hC]
    calc Real.exp (-(a * (blockThreshold d n : ℝ)))
        ≤ Real.exp (1
            + -(min (Real.log (8 / 7)) c₀ * a * (((n : ℝ) + 1) / greenScale d n))) := by
          refine Real.exp_le_exp.mpr ?_
          linarith
      _ = Real.exp 1
            * Real.exp (-(min (Real.log (8 / 7)) c₀ * a
                * (((n : ℝ) + 1) / greenScale d n))) := Real.exp_add _ _
  have hmono : Real.exp (-(Real.log (8 / 7) * (t : ℝ) / (n : ℝ)))
      ≤ Real.exp (-(min (Real.log (8 / 7)) c₀ * (t : ℝ) / (n : ℝ))) := by
    refine Real.exp_le_exp.mpr ?_
    have hdiv : (0 : ℝ) ≤ (t : ℝ) / (n : ℝ) := by positivity
    have he1 : Real.log (8 / 7) * (t : ℝ) / (n : ℝ)
        = Real.log (8 / 7) * ((t : ℝ) / (n : ℝ)) := by ring
    have he2 : min (Real.log (8 / 7)) c₀ * (t : ℝ) / (n : ℝ)
        = min (Real.log (8 / 7)) c₀ * ((t : ℝ) / (n : ℝ)) := by ring
    rw [he1, he2]
    nlinarith [hmin1, hdiv]
  have he : (8 / 7 : ℝ) ≤ Real.exp 1 := by
    nlinarith [Real.exp_one_gt_d9]
  have hexp1 : (8 / 7 : ℝ) * Real.exp (-(Real.log (8 / 7) * (t : ℝ) / (n : ℝ)))
      ≤ Real.exp 1 * Real.exp (-(min (Real.log (8 / 7)) c₀ * (t : ℝ) / (n : ℝ))) := by
    have hpos := Real.exp_pos (-(min (Real.log (8 / 7)) c₀ * (t : ℝ) / (n : ℝ)))
    nlinarith [hmono, hpos, he]
  rw [mul_add]
  linarith [hstep1, hstep2, hstep3, hexp1, hexp2]


theorem mul_sqrt_div_self {a t : ℝ} (ha : 0 < a) (_ht : 0 ≤ t) :
    a * Real.sqrt (t / a) = Real.sqrt (a * t) := by
  nth_rewrite 1 [← Real.sqrt_sq ha.le]
  rw [← Real.sqrt_mul (sq_nonneg a)]
  congr 1
  field_simp

theorem div_sqrt_div_self {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    t / Real.sqrt (t / a) = Real.sqrt (a * t) := by
  have hta : (0 : ℝ) < t / a := div_pos ht ha
  have hs : (0 : ℝ) < Real.sqrt (t / a) := Real.sqrt_pos.mpr hta
  rw [div_eq_iff (ne_of_gt hs), ← Real.sqrt_mul (by positivity : (0:ℝ) ≤ a * t),
    show a * t * (t / a) = t ^ 2 by field_simp, Real.sqrt_sq ht.le]

/-- **`eq:resolvent-pointwise` in dimension three and above**
(`parking.tex:2698-2701`): the horizon of Step 2 is `n = ⌈√(t/a)⌉`. -/
theorem exists_rangeExp_bound_high (hd : 3 ≤ d) : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ t : ℕ, 1 ≤ t →
      rangeExp d a t ≤ C * Real.exp (-(c * Real.sqrt (a * (t : ℝ)))) := by
  obtain ⟨c₁, C₁, hc₁, hC₁, hbound⟩ := exists_rangeExp_horizon_bound (d := d) (by omega)
  refine ⟨c₁ / 2, 2 * C₁, by positivity, by positivity, fun a ha ha1 t ht => ?_⟩
  have ht0 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hta : (1 : ℝ) ≤ (t : ℝ) / a := by
    rw [le_div_iff₀ ha]; nlinarith
  have hs1 : (1 : ℝ) ≤ Real.sqrt ((t : ℝ) / a) := by
    have h := Real.sqrt_le_sqrt hta
    rwa [Real.sqrt_one] at h
  set s : ℝ := Real.sqrt ((t : ℝ) / a) with hsdef
  set n : ℕ := ⌈s⌉₊ with hndef
  have hns : s ≤ (n : ℝ) := Nat.le_ceil s
  have hn2 : (n : ℝ) ≤ 2 * s := ceil_le_two_mul hs1
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := le_trans hs1 hns
  have hn1 : 1 ≤ n := by exact_mod_cast hn1R
  have hspos : (0 : ℝ) < s := lt_of_lt_of_le zero_lt_one hs1
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1R
  have hgs : greenScale d n = 1 := by
    have h1 : d ≠ 1 := by omega
    have h2 : d ≠ 2 := by omega
    simp only [greenScale, if_neg h1, if_neg h2]
  have hsqrt : Real.sqrt (a * (t : ℝ)) = (t : ℝ) / s :=
    (div_sqrt_div_self ha (by linarith)).symm
  have hsqrt2 : a * s = Real.sqrt (a * (t : ℝ)) := mul_sqrt_div_self ha (by linarith)
  have hb := hbound a ha ha1 n t hn1
  have h0t : (0 : ℝ) ≤ (t : ℝ) := by linarith
  have hterm1 : Real.exp (-(c₁ * (t : ℝ) / (n : ℝ)))
      ≤ Real.exp (-(c₁ / 2 * Real.sqrt (a * (t : ℝ)))) := by
    refine Real.exp_le_exp.mpr ?_
    have hdiv : (t : ℝ) / (2 * s) ≤ (t : ℝ) / (n : ℝ) :=
      div_le_div_of_nonneg_left h0t hnpos hn2
    have heq : (t : ℝ) / (2 * s) = Real.sqrt (a * (t : ℝ)) / 2 := by
      rw [hsqrt]; field_simp
    have hmul : c₁ * ((t : ℝ) / (2 * s)) ≤ c₁ * ((t : ℝ) / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hdiv hc₁.le
    rw [heq] at hmul
    have hrw : c₁ * (t : ℝ) / (n : ℝ) = c₁ * ((t : ℝ) / (n : ℝ)) := by ring
    rw [hrw]
    linarith
  have hterm2 : Real.exp (-(c₁ * a * (((n : ℝ) + 1) / greenScale d n)))
      ≤ Real.exp (-(c₁ / 2 * Real.sqrt (a * (t : ℝ)))) := by
    refine Real.exp_le_exp.mpr ?_
    rw [hgs, div_one]
    have hsq0 : (0 : ℝ) ≤ Real.sqrt (a * (t : ℝ)) := Real.sqrt_nonneg _
    have has : a * s ≤ a * ((n : ℝ) + 1) := by nlinarith [hns, ha]
    nlinarith [has, hsqrt2, hc₁, hsq0]
  nlinarith [hb, hterm1, hterm2, hC₁]


theorem div_rpow_two_thirds {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    t / ((t / a) ^ ((2 : ℝ) / 3)) = a ^ ((2 : ℝ) / 3) * t ^ ((1 : ℝ) / 3) := by
  have hne : ((t / a) ^ ((2 : ℝ) / 3)) ≠ 0 := by positivity
  rw [div_eq_iff hne, Real.div_rpow ht.le ha.le]
  field_simp
  rw [← Real.rpow_add ht]
  norm_num

theorem mul_rpow_one_third {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    a * ((t / a) ^ ((1 : ℝ) / 3)) = a ^ ((2 : ℝ) / 3) * t ^ ((1 : ℝ) / 3) := by
  rw [Real.div_rpow ht.le ha.le]
  field_simp
  rw [← Real.rpow_add ha]
  norm_num

theorem sqrt_rpow_two_thirds {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (x ^ ((2 : ℝ) / 3)) = x ^ ((1 : ℝ) / 3) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num

/-- **`eq:resolvent-pointwise` in dimension one** (`parking.tex:2698-2701`): the
horizon of Step 2 is `n = ⌈(t/a)^{2/3}⌉`. -/
theorem exists_rangeExp_bound_one (hd : d = 1) : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ t : ℕ, 1 ≤ t →
      rangeExp d a t
        ≤ C * Real.exp (-(c * a ^ ((2 : ℝ) / 3) * (t : ℝ) ^ ((1 : ℝ) / 3))) := by
  obtain ⟨c₁, C₁, hc₁, hC₁, hbound⟩ := exists_rangeExp_horizon_bound (d := d) (by omega)
  refine ⟨c₁ / 2, 2 * C₁, by positivity, by positivity, fun a ha ha1 t ht => ?_⟩
  have ht0 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have htpos : (0 : ℝ) < (t : ℝ) := by linarith
  have hta : (1 : ℝ) ≤ (t : ℝ) / a := by
    rw [le_div_iff₀ ha]; nlinarith
  have hu1 : (1 : ℝ) ≤ ((t : ℝ) / a) ^ ((2 : ℝ) / 3) :=
    Real.one_le_rpow hta (by norm_num)
  set u : ℝ := ((t : ℝ) / a) ^ ((2 : ℝ) / 3) with hudef
  set n : ℕ := ⌈u⌉₊ with hndef
  have hns : u ≤ (n : ℝ) := Nat.le_ceil u
  have hn2 : (n : ℝ) ≤ 2 * u := ceil_le_two_mul hu1
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := le_trans hu1 hns
  have hn1 : 1 ≤ n := by exact_mod_cast hn1R
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu1
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1R
  have hgs : greenScale d n = Real.sqrt ((n : ℝ) + 1) := by
    simp only [greenScale, if_pos hd]
  have hrate : (0 : ℝ) ≤ a ^ ((2 : ℝ) / 3) * (t : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have hb := hbound a ha ha1 n t hn1
  have hterm1 : Real.exp (-(c₁ * (t : ℝ) / (n : ℝ)))
      ≤ Real.exp (-(c₁ / 2 * a ^ ((2 : ℝ) / 3) * (t : ℝ) ^ ((1 : ℝ) / 3))) := by
    refine Real.exp_le_exp.mpr ?_
    have hdiv : (t : ℝ) / (2 * u) ≤ (t : ℝ) / (n : ℝ) :=
      div_le_div_of_nonneg_left htpos.le hnpos hn2
    have heq : (t : ℝ) / (2 * u) = (a ^ ((2 : ℝ) / 3) * (t : ℝ) ^ ((1 : ℝ) / 3)) / 2 := by
      rw [← div_rpow_two_thirds ha htpos, hudef]
      field_simp
    have hmul : c₁ * ((t : ℝ) / (2 * u)) ≤ c₁ * ((t : ℝ) / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hdiv hc₁.le
    rw [heq] at hmul
    have hrw : c₁ * (t : ℝ) / (n : ℝ) = c₁ * ((t : ℝ) / (n : ℝ)) := by ring
    rw [hrw]
    linarith
  have hterm2 : Real.exp (-(c₁ * a * (((n : ℝ) + 1) / greenScale d n)))
      ≤ Real.exp (-(c₁ / 2 * a ^ ((2 : ℝ) / 3) * (t : ℝ) ^ ((1 : ℝ) / 3))) := by
    refine Real.exp_le_exp.mpr ?_
    rw [hgs, Real.div_sqrt]
    have hsu : Real.sqrt u ≤ Real.sqrt ((n : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    have hsqu : Real.sqrt u = ((t : ℝ) / a) ^ ((1 : ℝ) / 3) := by
      rw [hudef]
      exact sqrt_rpow_two_thirds (by positivity)
    have hau : a * Real.sqrt u = a ^ ((2 : ℝ) / 3) * (t : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [hsqu]
      exact mul_rpow_one_third ha htpos
    have hstep : a * Real.sqrt u ≤ a * Real.sqrt ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hsu ha.le
    nlinarith [hstep, hau, hc₁, hrate]
  nlinarith [hb, hterm1, hterm2, hC₁]

theorem div_sqrt_eq_sqrt {t x : ℝ} (ht : 0 ≤ t) (_hx : 0 < x) :
    t / Real.sqrt x = Real.sqrt (t ^ 2 / x) := by
  rw [Real.sqrt_div (sq_nonneg t), Real.sqrt_sq ht]

theorem sqrt_mul_div_self {y L : ℝ} (hy : 0 ≤ y) (hL : 0 < L) :
    Real.sqrt (y * L) / L = Real.sqrt (y / L) := by
  rw [eq_comm, eq_div_iff (ne_of_gt hL)]
  nth_rewrite 2 [← Real.sqrt_sq hL.le]
  rw [← Real.sqrt_mul (div_nonneg hy hL.le)]
  congr 1
  field_simp


/-- **`eq:resolvent-pointwise` in dimension two** (`parking.tex:2698-2703`): the
horizon of Step 2 is `n = ⌈√(t log(t+2)/a)⌉`, and the hypothesis `t ≥ e/a` is
what bounds `log(n+2)` by `3 log(t+2)`. -/
theorem exists_rangeExp_bound_two (hd : d = 2) : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ t : ℕ, 1 ≤ t → Real.exp 1 / a ≤ (t : ℝ) →
      rangeExp d a t
        ≤ C * Real.exp (-(c * Real.sqrt (a * (t : ℝ) / Real.log ((t : ℝ) + 2)))) := by
  obtain ⟨c₁, C₁, hc₁, hC₁, hbound⟩ := exists_rangeExp_horizon_bound (d := d) (by omega)
  refine ⟨c₁ / 3, 2 * C₁, by positivity, by positivity, fun a ha ha1 t ht hte => ?_⟩
  have ht0 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have htpos : (0 : ℝ) < (t : ℝ) := by linarith
  set L : ℝ := Real.log ((t : ℝ) + 2) with hLdef
  have hainv : (1 : ℝ) / a ≤ (t : ℝ) := by
    rw [div_le_iff₀ ha]
    have h1 : Real.exp 1 / a ≤ (t : ℝ) := hte
    rw [div_le_iff₀ ha] at h1
    nlinarith [Real.exp_one_gt_d9]
  have hexp1 : Real.exp 1 ≤ (t : ℝ) := by
    have h1 : Real.exp 1 / a ≤ (t : ℝ) := hte
    have h2 : Real.exp 1 ≤ Real.exp 1 / a := by
      rw [le_div_iff₀ ha]; nlinarith [Real.exp_pos 1]
    linarith
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]
    linarith
  have hLpos : (0 : ℝ) < L := by linarith
  have hLt : L ≤ (t : ℝ) + 2 := by
    rw [hLdef]
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < (t : ℝ) + 2 by linarith)
    linarith
  have harg : (1 : ℝ) ≤ (t : ℝ) * L / a := by
    rw [le_div_iff₀ ha]
    nlinarith
  set v : ℝ := Real.sqrt ((t : ℝ) * L / a) with hvdef
  have hv1 : (1 : ℝ) ≤ v := by
    have h := Real.sqrt_le_sqrt harg
    rwa [Real.sqrt_one] at h
  set n : ℕ := ⌈v⌉₊ with hndef
  have hns : v ≤ (n : ℝ) := Nat.le_ceil v
  have hn2v : (n : ℝ) ≤ 2 * v := ceil_le_two_mul hv1
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := le_trans hv1 hns
  have hn1 : 1 ≤ n := by exact_mod_cast hn1R
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1R
  have hvpos : (0 : ℝ) < v := lt_of_lt_of_le zero_lt_one hv1
  have hgs : greenScale d n = Real.log ((n : ℝ) + 2) := by
    simp only [greenScale, if_neg (by omega : d ≠ 1), if_pos hd]
  have hlogpos : (0 : ℝ) < Real.log ((n : ℝ) + 2) := Real.log_pos (by linarith)
  -- the horizon is at most `t log(t+2)`
  have hvt : v ≤ (t : ℝ) * L := by
    have e1 : (t : ℝ) * L / a = (t : ℝ) * L * (1 / a) := by field_simp
    have h1 : (t : ℝ) * L / a ≤ ((t : ℝ) * L) ^ 2 := by
      rw [e1]
      have h2 : (t : ℝ) * L * (1 / a) ≤ (t : ℝ) * L * (t : ℝ) :=
        mul_le_mul_of_nonneg_left hainv (by positivity)
      nlinarith
    have h3 := Real.sqrt_le_sqrt h1
    rw [hvdef]
    rwa [Real.sqrt_sq (by positivity)] at h3
  have htL : (t : ℝ) * L ≤ (t : ℝ) * ((t : ℝ) + 2) :=
    mul_le_mul_of_nonneg_left hLt htpos.le
  have hnle : (n : ℝ) + 2 ≤ ((t : ℝ) + 2) ^ 3 := by nlinarith [hvt, hn2v, htL, ht0]
  have hlogn : Real.log ((n : ℝ) + 2) ≤ 3 * L := by
    have h3 : Real.log ((n : ℝ) + 2) ≤ Real.log (((t : ℝ) + 2) ^ 3) :=
      Real.log_le_log (by linarith) hnle
    rw [Real.log_pow] at h3
    push_cast at h3
    rw [hLdef]
    linarith
  have hb := hbound a ha ha1 n t hn1
  have hS0 : (0 : ℝ) ≤ Real.sqrt (a * (t : ℝ) / L) := Real.sqrt_nonneg _
  have hTV : (t : ℝ) / v = Real.sqrt (a * (t : ℝ) / L) := by
    rw [hvdef, div_sqrt_eq_sqrt htpos.le (by positivity)]
    congr 1
    field_simp
  have hav : a * v = Real.sqrt (a * (t : ℝ) * L) := by
    rw [hvdef, mul_sqrt_div_self ha (by positivity)]
    congr 1
    ring
  have havL : a * v / L = Real.sqrt (a * (t : ℝ) / L) := by
    rw [hav, sqrt_mul_div_self (by positivity) hLpos]
  have hterm1 : Real.exp (-(c₁ * (t : ℝ) / (n : ℝ)))
      ≤ Real.exp (-(c₁ / 3 * Real.sqrt (a * (t : ℝ) / L))) := by
    refine Real.exp_le_exp.mpr ?_
    have hdiv : (t : ℝ) / (2 * v) ≤ (t : ℝ) / (n : ℝ) :=
      div_le_div_of_nonneg_left htpos.le hnpos hn2v
    have heq : (t : ℝ) / (2 * v) = Real.sqrt (a * (t : ℝ) / L) / 2 := by
      rw [← hTV]; field_simp
    rw [heq] at hdiv
    have hrw : c₁ * (t : ℝ) / (n : ℝ) = c₁ * ((t : ℝ) / (n : ℝ)) := by ring
    rw [hrw]
    have hmul := mul_le_mul_of_nonneg_left hdiv hc₁.le
    have e1 : c₁ * (Real.sqrt (a * (t : ℝ) / L) / 2)
        = c₁ / 2 * Real.sqrt (a * (t : ℝ) / L) := by ring
    rw [e1] at hmul
    nlinarith [hmul, hc₁, hS0]
  have hterm2 : Real.exp (-(c₁ * a * (((n : ℝ) + 1) / greenScale d n)))
      ≤ Real.exp (-(c₁ / 3 * Real.sqrt (a * (t : ℝ) / L))) := by
    refine Real.exp_le_exp.mpr ?_
    rw [hgs]
    have hn1' : (0 : ℝ) ≤ a * ((n : ℝ) + 1) := mul_nonneg ha.le (by linarith)
    have hav1 : a * v ≤ a * ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) ha.le
    have hquot : a * v / (3 * L) ≤ a * ((n : ℝ) + 1) / Real.log ((n : ℝ) + 2) := by
      rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 3 * L) hlogpos]
      have hstep1 : a * v * Real.log ((n : ℝ) + 2)
          ≤ a * ((n : ℝ) + 1) * Real.log ((n : ℝ) + 2) :=
        mul_le_mul_of_nonneg_right hav1 hlogpos.le
      have hstep2 : a * ((n : ℝ) + 1) * Real.log ((n : ℝ) + 2)
          ≤ a * ((n : ℝ) + 1) * (3 * L) :=
        mul_le_mul_of_nonneg_left hlogn hn1'
      linarith
    have hsplit : a * v / (3 * L) = Real.sqrt (a * (t : ℝ) / L) / 3 := by
      rw [← havL]; field_simp
    rw [hsplit] at hquot
    have hmul := mul_le_mul_of_nonneg_left hquot hc₁.le
    have e1 : c₁ * (Real.sqrt (a * (t : ℝ) / L) / 3)
        = c₁ / 3 * Real.sqrt (a * (t : ℝ) / L) := by ring
    have e2 : c₁ * (a * ((n : ℝ) + 1) / Real.log ((n : ℝ) + 2))
        = c₁ * a * (((n : ℝ) + 1) / Real.log ((n : ℝ) + 2)) := by ring
    rw [e1, e2] at hmul
    linarith
  nlinarith [hb, hterm1, hterm2, hC₁]

/-- `e^{-y} ≤ k!/y^k`: the tail of the exponential series in the form the
summation of Step 3 uses. -/
theorem exp_neg_le_div_pow {y : ℝ} (hy : 0 < y) (k : ℕ) :
    Real.exp (-y) ≤ (Nat.factorial k : ℝ) / y ^ k := by
  have h1 : y ^ k / (Nat.factorial k : ℝ) ≤ Real.exp y := Real.pow_div_factorial_le_exp (x := y) hy.le k
  have hk : (0 : ℝ) < (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.factorial_pos k
  rw [le_div_iff₀ (by positivity : (0:ℝ) < y ^ k), Real.exp_neg, inv_mul_eq_div,
    div_le_iff₀ (Real.exp_pos y)]
  rw [div_le_iff₀ hk] at h1
  linarith

theorem exists_tsum_rpow_le {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-p)) ∧
      ∑' n : ℕ, ((n : ℝ) + 1) ^ (-p) ≤ C := by
  obtain ⟨C, hC, hle⟩ := exists_sum_rpow_le hp
  have hnn : ∀ n : ℕ, (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (-p) := fun n =>
    Real.rpow_nonneg (by positivity) _
  have hrange : ∀ n : ℕ, ∑ i ∈ Finset.range n, ((i : ℝ) + 1) ^ (-p) ≤ C := by
    intro n
    cases n with
    | zero => simpa using hC.le
    | succ m => exact hle m
  exact ⟨C, hC, summable_of_sum_range_le hnn hrange, Real.tsum_le_of_sum_range_le hnn hrange⟩


theorem exists_tsum_inv_sq_le : ∃ C : ℝ, 0 < C ∧
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) ∧
    ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 ≤ C := by
  obtain ⟨C, hC, hle⟩ := exists_sum_rpow_le (p := (2:ℝ)) (by norm_num)
  have hconv : ∀ n : ℕ, ((n : ℝ) + 1) ^ (-(2:ℝ)) = 1 / ((n : ℝ) + 1) ^ 2 := by
    intro n
    rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ (n : ℝ) + 1),
      show (2:ℝ) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
  have hnn : ∀ n : ℕ, (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) ^ 2 := fun n => by positivity
  have hrange : ∀ n : ℕ, ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) ^ 2 ≤ C := by
    intro n
    cases n with
    | zero => simpa using hC.le
    | succ m =>
        have h := hle m
        simp only [hconv] at h
        exact h
  exact ⟨C, hC, summable_of_sum_range_le hnn hrange, Real.tsum_le_of_sum_range_le hnn hrange⟩

theorem sqrt_pow_four {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ^ 4 = x ^ 2 := by
  have h := Real.sq_sqrt hx
  have h4 : Real.sqrt x ^ 4 = (Real.sqrt x ^ 2) ^ 2 := by ring
  rw [h4, h]

theorem exp_neg_three_lambda_le {a : ℝ} (ha : 0 < a) (_ha1 : a ≤ 1) :
    Real.exp (-(3 * Real.log (Real.exp 1 / a))) ≤ a ^ 3 := by
  have hea : (0 : ℝ) < Real.exp 1 / a := by positivity
  have h3 : Real.exp (3 * Real.log (Real.exp 1 / a)) = (Real.exp 1 / a) ^ 3 := by
    rw [show (3:ℝ) = ((3:ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hea]
  rw [Real.exp_neg, h3, div_pow, inv_div]
  have he : (1:ℝ) ≤ Real.exp 1 ^ 3 := one_le_pow₀ (Real.one_le_exp (by norm_num))
  rw [div_le_iff₀ (by positivity)]
  nlinarith [pow_nonneg ha.le 3, he]


/-- **Step 3 of `prop:resolvent` in dimension three and above**
(`parking.tex:2708-2712`).  Beyond the threshold `T = C a^{-1} Λ²` the resolvent
is summable with sum at most one: every term past the threshold carries the
factor `e^{-βΛ}`, which is a power of `a`, and what is left is summable against
`(t+1)^{-2}`. -/
theorem exists_resolvent_tail_high (hd : 3 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ a : ℝ, 0 < a → a ≤ 1 → ∀ t : ℕ, 1 ≤ t →
        rangeExp d a t ≤ C * Real.exp (-(c * Real.sqrt (a * (t : ℝ))))) ∧
      ∀ a : ℝ, 0 < a → a ≤ 1 →
        Summable (fun t : ℕ => if resolventThreshold d C a < (t : ℝ)
            then rangeExp d a t else 0) ∧
          ∑' t : ℕ, (if resolventThreshold d C a < (t : ℝ)
            then rangeExp d a t else 0) ≤ 1 := by
  obtain ⟨c₀, C₀, hc₀, hC₀, hpt⟩ := exists_rangeExp_bound_high hd
  obtain ⟨C₁, hC₁, hsum1, htsum1⟩ := exists_tsum_inv_sq_le
  set M : ℝ := 1536 * C₀ * C₁ / c₀ ^ 4 with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  set β : ℝ := 4 + |Real.log M| with hβdef
  have hβ3 : 3 ≤ β := by
    have : 0 ≤ |Real.log M| := abs_nonneg _
    rw [hβdef]; linarith
  have hβpos : 0 < β := by linarith
  set C : ℝ := max C₀ ((2 * β / c₀) ^ 2) with hCdef
  have hCpos : 0 < C := lt_of_lt_of_le hC₀ (le_max_left _ _)
  have hCge : C₀ ≤ C := le_max_left _ _
  have hsqC : 2 * β / c₀ ≤ Real.sqrt C := by
    have h1 : Real.sqrt ((2 * β / c₀) ^ 2) ≤ Real.sqrt C :=
      Real.sqrt_le_sqrt (le_max_right _ _)
    rwa [Real.sqrt_sq (by positivity)] at h1
  have hβC : β ≤ c₀ * Real.sqrt C / 2 := by
    rw [div_le_iff₀ hc₀] at hsqC
    linarith
  refine ⟨c₀, C, hc₀, hCpos, ?_, ?_⟩
  · intro a ha ha1 t ht
    refine (hpt a ha ha1 t ht).trans ?_
    have := Real.exp_pos (-(c₀ * Real.sqrt (a * (t : ℝ))))
    nlinarith [hCge, this]
  intro a ha ha1
  set L : ℝ := Real.log (Real.exp 1 / a) with hLdef
  have hea : (0 : ℝ) < Real.exp 1 / a := by positivity
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hea, le_div_iff₀ ha]
    nlinarith [Real.exp_pos 1]
  have hLpos : (0 : ℝ) < L := by linarith
  have hTeq : resolventThreshold d C a = C * (a⁻¹ * L ^ 2) := by
    simp only [resolventThreshold, if_neg (by omega : d ≠ 1),
      if_neg (by omega : d ≠ 2), hLdef]
  have hTpos : (0 : ℝ) < resolventThreshold d C a := by
    rw [hTeq]; positivity
  set A : ℝ := 1536 * C₀ * Real.exp (-(β * L)) / (c₀ ^ 4 * a ^ 2) with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hmaj : ∀ t : ℕ, (if resolventThreshold d C a < (t : ℝ)
      then rangeExp d a t else 0) ≤ A * (1 / ((t : ℝ) + 1) ^ 2) := by
    intro t
    by_cases hT : resolventThreshold d C a < (t : ℝ)
    · rw [if_pos hT]
      have ht1 : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with rfl | hpos
        · exfalso
          simp only [Nat.cast_zero] at hT
          linarith
        · exact hpos
      have htR : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
      have hatpos : (0 : ℝ) < a * (t : ℝ) := by positivity
      have hsqrtpos : (0 : ℝ) < Real.sqrt (a * (t : ℝ)) := Real.sqrt_pos.mpr hatpos
      have haT : a * resolventThreshold d C a = C * L ^ 2 := by
        rw [hTeq]; field_simp
      have hsqT : Real.sqrt C * L ≤ Real.sqrt (a * (t : ℝ)) := by
        have h1 : a * resolventThreshold d C a ≤ a * (t : ℝ) :=
          mul_le_mul_of_nonneg_left hT.le ha.le
        have h2 := Real.sqrt_le_sqrt h1
        rw [haT, Real.sqrt_mul hCpos.le, Real.sqrt_sq hLpos.le] at h2
        exact h2
      have hexp1 : Real.exp (-(c₀ * Real.sqrt (a * (t : ℝ)) / 2))
          ≤ Real.exp (-(β * L)) := by
        refine Real.exp_le_exp.mpr ?_
        have h3 : β * L ≤ c₀ * Real.sqrt C / 2 * L :=
          mul_le_mul_of_nonneg_right hβC hLpos.le
        have h4 : c₀ * Real.sqrt C / 2 * L ≤ c₀ * Real.sqrt (a * (t : ℝ)) / 2 := by
          have h8 := mul_le_mul_of_nonneg_left hsqT (by positivity : (0:ℝ) ≤ c₀ / 2)
          linarith [h8]
        linarith
      have hexp2 : Real.exp (-(c₀ * Real.sqrt (a * (t : ℝ)) / 2))
          ≤ 384 / (c₀ ^ 4 * (a * (t : ℝ)) ^ 2) := by
        have h5 := exp_neg_le_div_pow
          (y := c₀ * Real.sqrt (a * (t : ℝ)) / 2) (by positivity) 4
        have h6 : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
        have h7 : (c₀ * Real.sqrt (a * (t : ℝ)) / 2) ^ 4
            = c₀ ^ 4 * (a * (t : ℝ)) ^ 2 / 16 := by
          have hs := sqrt_pow_four hatpos.le
          calc (c₀ * Real.sqrt (a * (t : ℝ)) / 2) ^ 4
              = c₀ ^ 4 * Real.sqrt (a * (t : ℝ)) ^ 4 / 16 := by ring
            _ = c₀ ^ 4 * (a * (t : ℝ)) ^ 2 / 16 := by rw [hs]
        rw [h6, h7] at h5
        calc Real.exp (-(c₀ * Real.sqrt (a * (t : ℝ)) / 2))
            ≤ 24 / (c₀ ^ 4 * (a * (t : ℝ)) ^ 2 / 16) := h5
          _ = 384 / (c₀ ^ 4 * (a * (t : ℝ)) ^ 2) := by
              field_simp
              ring
      have hsplit : Real.exp (-(c₀ * Real.sqrt (a * (t : ℝ))))
          = Real.exp (-(c₀ * Real.sqrt (a * (t : ℝ)) / 2))
            * Real.exp (-(c₀ * Real.sqrt (a * (t : ℝ)) / 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hprod : Real.exp (-(c₀ * Real.sqrt (a * (t : ℝ))))
          ≤ Real.exp (-(β * L)) * (384 / (c₀ ^ 4 * (a * (t : ℝ)) ^ 2)) := by
        rw [hsplit]
        exact mul_le_mul hexp1 hexp2 (Real.exp_pos _).le (Real.exp_pos _).le
      have hstep : rangeExp d a t
          ≤ C₀ * (Real.exp (-(β * L)) * (384 / (c₀ ^ 4 * (a * (t : ℝ)) ^ 2))) := by
        refine (hpt a ha ha1 t ht1).trans ?_
        exact mul_le_mul_of_nonneg_left hprod hC₀.le
      refine hstep.trans ?_
      rw [hAdef]
      have hsq : ((t : ℝ) + 1) ^ 2 ≤ 4 * (t : ℝ) ^ 2 := by nlinarith [htR]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < c₀ ^ 4 * a ^ 2)]
      have hE : (0 : ℝ) < Real.exp (-(β * L)) := Real.exp_pos _
      have hexpand : C₀ * (Real.exp (-(β * L)) * (384 / (c₀ ^ 4 * (a * (t : ℝ)) ^ 2)))
          * (c₀ ^ 4 * a ^ 2)
          = 384 * C₀ * Real.exp (-(β * L)) / (t : ℝ) ^ 2 := by
        field_simp
      rw [hexpand]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (t : ℝ) ^ 2)]
      have hone : 1536 * C₀ * Real.exp (-(β * L)) * (1 / ((t : ℝ) + 1) ^ 2) * (t : ℝ) ^ 2
          = 1536 * C₀ * Real.exp (-(β * L)) * ((t : ℝ) ^ 2 / ((t : ℝ) + 1) ^ 2) := by
        ring
      rw [hone]
      have hfrac : (1 : ℝ) / 4 ≤ (t : ℝ) ^ 2 / ((t : ℝ) + 1) ^ 2 := by
        rw [le_div_iff₀ (by positivity : (0:ℝ) < ((t : ℝ) + 1) ^ 2)]
        linarith [hsq]
      have hfin := mul_le_mul_of_nonneg_left hfrac
        (by positivity : (0:ℝ) ≤ 1536 * C₀ * Real.exp (-(β * L)))
      linarith [hfin]
    · rw [if_neg hT]
      positivity
  have hmajsum : Summable (fun t : ℕ => A * (1 / ((t : ℝ) + 1) ^ 2)) := hsum1.mul_left A
  have hnn : ∀ t : ℕ, (0 : ℝ) ≤ (if resolventThreshold d C a < (t : ℝ)
      then rangeExp d a t else 0) := by
    intro t
    by_cases hT : resolventThreshold d C a < (t : ℝ)
    · rw [if_pos hT]
      rw [rangeExp]
      exact integral_nonneg fun p => (Real.exp_pos _).le
    · rw [if_neg hT]
  have hsummable : Summable (fun t : ℕ => if resolventThreshold d C a < (t : ℝ)
      then rangeExp d a t else 0) :=
    hmajsum.of_nonneg_of_le hnn hmaj
  refine ⟨hsummable, ?_⟩
  have hle1 : ∑' t : ℕ, (if resolventThreshold d C a < (t : ℝ)
      then rangeExp d a t else 0) ≤ ∑' t : ℕ, A * (1 / ((t : ℝ) + 1) ^ 2) :=
    hsummable.tsum_le_tsum hmaj hmajsum
  have heq : ∑' t : ℕ, A * (1 / ((t : ℝ) + 1) ^ 2)
      = A * ∑' t : ℕ, 1 / ((t : ℝ) + 1) ^ 2 := tsum_mul_left
  rw [heq] at hle1
  have hAC : A * C₁ ≤ 1 := by
    have hexp3 : Real.exp (-(β * L)) ≤ a ^ 3 * Real.exp (-(β - 3)) := by
      have hsp : -(β * L) = -(3 * L) + -((β - 3) * L) := by ring
      rw [hsp, Real.exp_add]
      have h1 : Real.exp (-(3 * L)) ≤ a ^ 3 := by
        rw [hLdef]; exact exp_neg_three_lambda_le ha ha1
      have h2 : Real.exp (-((β - 3) * L)) ≤ Real.exp (-(β - 3)) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith [hβ3, hL1]
      exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
    have hMexp : M * Real.exp (-(β - 3)) ≤ 1 := by
      have hlog : Real.log M ≤ β - 3 := by
        have : Real.log M ≤ |Real.log M| := le_abs_self _
        rw [hβdef]; linarith
      have h1 : M ≤ Real.exp (β - 3) := by
        rw [← Real.exp_log hMpos]
        exact Real.exp_le_exp.mpr hlog
      have h3 : (0 : ℝ) < Real.exp (-(β - 3)) := Real.exp_pos _
      have h4 := mul_le_mul_of_nonneg_right h1 h3.le
      have h5 : Real.exp (β - 3) * Real.exp (-(β - 3)) = 1 := by
        rw [← Real.exp_add]
        simp
      linarith [h4, h5]
    have hA3 : A * C₁ ≤ M * Real.exp (-(β - 3)) * a := by
      have hkey : A * C₁ = (1536 * C₀ * C₁ / (c₀ ^ 4 * a ^ 2)) * Real.exp (-(β * L)) := by
        rw [hAdef]; ring
      have hkey2 : M * Real.exp (-(β - 3)) * a
          = (1536 * C₀ * C₁ / (c₀ ^ 4 * a ^ 2)) * (a ^ 3 * Real.exp (-(β - 3))) := by
        rw [hM]; field_simp
      rw [hkey, hkey2]
      exact mul_le_mul_of_nonneg_left hexp3
        (by positivity : (0:ℝ) ≤ 1536 * C₀ * C₁ / (c₀ ^ 4 * a ^ 2))
    have hfin : M * Real.exp (-(β - 3)) * a ≤ M * Real.exp (-(β - 3)) * 1 :=
      mul_le_mul_of_nonneg_left ha1 (by positivity)
    linarith [hA3, hfin, hMexp]
  calc ∑' t : ℕ, (if resolventThreshold d C a < (t : ℝ)
        then rangeExp d a t else 0)
      ≤ A * ∑' t : ℕ, 1 / ((t : ℝ) + 1) ^ 2 := hle1
    _ ≤ A * C₁ := mul_le_mul_of_nonneg_left htsum1 hApos.le
    _ ≤ 1 := hAC

theorem exp_neg_nat_lambda_le {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Real.exp (-((k : ℝ) * Real.log (Real.exp 1 / a))) ≤ a ^ k := by
  have hea : (0 : ℝ) < Real.exp 1 / a := by positivity
  have h3 : Real.exp ((k : ℝ) * Real.log (Real.exp 1 / a)) = (Real.exp 1 / a) ^ k := by
    rw [Real.exp_nat_mul, Real.exp_log hea]
  rw [Real.exp_neg, h3, div_pow, inv_div]
  have he : (1:ℝ) ≤ Real.exp 1 ^ k := one_le_pow₀ (Real.one_le_exp (by norm_num))
  rw [div_le_iff₀ (by positivity)]
  nlinarith [pow_nonneg ha.le k, he]

theorem rpow_cube_eq {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (a ^ ((2 : ℝ) / 3) * t ^ ((1 : ℝ) / 3)) ^ 3 = a ^ 2 * t := by
  rw [mul_pow, ← Real.rpow_natCast (a ^ ((2:ℝ)/3)) 3, ← Real.rpow_natCast (t ^ ((1:ℝ)/3)) 3,
    ← Real.rpow_mul ha, ← Real.rpow_mul ht]
  norm_num


/-- **Step 3 of `prop:resolvent` in dimension one** (`parking.tex:2713-2714`):
the substitution `s = v³ a^{-2}` of the paper is the comparison of the horizon
with the cube of the rate. -/
theorem exists_resolvent_tail_one (hd : d = 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ a : ℝ, 0 < a → a ≤ 1 → ∀ t : ℕ, 1 ≤ t →
        rangeExp d a t
          ≤ C * Real.exp (-(c * a ^ ((2 : ℝ) / 3) * (t : ℝ) ^ ((1 : ℝ) / 3)))) ∧
      ∀ a : ℝ, 0 < a → a ≤ 1 →
        Summable (fun t : ℕ => if resolventThreshold d C a < (t : ℝ)
            then rangeExp d a t else 0) ∧
          ∑' t : ℕ, (if resolventThreshold d C a < (t : ℝ)
            then rangeExp d a t else 0) ≤ 1 := by
  obtain ⟨c₀, C₀, hc₀, hC₀, hpt⟩ := exists_rangeExp_bound_one hd
  obtain ⟨C₁, hC₁, hsum1, htsum1⟩ := exists_tsum_inv_sq_le
  set M : ℝ := 184320 * C₀ * C₁ / c₀ ^ 6 with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  set β : ℝ := 6 + |Real.log M| with hβdef
  have hβ5 : 5 ≤ β := by
    have : 0 ≤ |Real.log M| := abs_nonneg _
    rw [hβdef]; linarith
  have hβpos : 0 < β := by linarith
  set C : ℝ := max C₀ ((2 * β / c₀) ^ 3) with hCdef
  have hCpos : 0 < C := lt_of_lt_of_le hC₀ (le_max_left _ _)
  have hCge : C₀ ≤ C := le_max_left _ _
  have hCge3 : (2 * β / c₀) ^ 3 ≤ C := le_max_right _ _
  refine ⟨c₀, C, hc₀, hCpos, ?_, ?_⟩
  · intro a ha ha1 t ht
    refine (hpt a ha ha1 t ht).trans ?_
    have := Real.exp_pos (-(c₀ * a ^ ((2 : ℝ) / 3) * (t : ℝ) ^ ((1 : ℝ) / 3)))
    nlinarith [hCge, this]
  intro a ha ha1
  set L : ℝ := Real.log (Real.exp 1 / a) with hLdef
  have hea : (0 : ℝ) < Real.exp 1 / a := by positivity
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hea, le_div_iff₀ ha]
    nlinarith [Real.exp_pos 1]
  have hLpos : (0 : ℝ) < L := by linarith
  have hTeq : resolventThreshold d C a = C * (a ^ (-(2 : ℝ)) * L ^ 3) := by
    simp only [resolventThreshold, if_pos hd, hLdef]
  have hTpos : (0 : ℝ) < resolventThreshold d C a := by
    rw [hTeq]
    have : (0:ℝ) < a ^ (-(2:ℝ)) := Real.rpow_pos_of_pos ha _
    positivity
  set A : ℝ := 184320 * C₀ * Real.exp (-(β * L)) / (c₀ ^ 6 * a ^ 4) with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  have haT : a ^ 2 * resolventThreshold d C a = C * L ^ 3 := by
    rw [hTeq, Real.rpow_neg ha.le, show (2:ℝ) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have hmaj : ∀ t : ℕ, (if resolventThreshold d C a < (t : ℝ)
      then rangeExp d a t else 0) ≤ A * (1 / ((t : ℝ) + 1) ^ 2) := by
    intro t
    by_cases hT : resolventThreshold d C a < (t : ℝ)
    · rw [if_pos hT]
      have ht1 : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with rfl | hpos
        · exfalso
          simp only [Nat.cast_zero] at hT
          linarith
        · exact hpos
      have htR : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
      have htpos : (0 : ℝ) < (t : ℝ) := by linarith
      have hRpos : (0 : ℝ) < a ^ ((2:ℝ)/3) * (t : ℝ) ^ ((1:ℝ)/3) := by
        have h1 : (0:ℝ) < a ^ ((2:ℝ)/3) := Real.rpow_pos_of_pos ha _
        have h2 : (0:ℝ) < (t : ℝ) ^ ((1:ℝ)/3) := Real.rpow_pos_of_pos htpos _
        positivity
      have hcube : ((2 * β / c₀) * L) ^ 3
          ≤ (a ^ ((2:ℝ)/3) * (t : ℝ) ^ ((1:ℝ)/3)) ^ 3 := by
        rw [rpow_cube_eq ha.le htpos.le]
        have h1 : a ^ 2 * resolventThreshold d C a ≤ a ^ 2 * (t : ℝ) :=
          mul_le_mul_of_nonneg_left hT.le (by positivity)
        rw [haT] at h1
        have h3 : ((2 * β / c₀) * L) ^ 3 = (2 * β / c₀) ^ 3 * L ^ 3 := by ring
        have h4 : (2 * β / c₀) ^ 3 * L ^ 3 ≤ C * L ^ 3 :=
          mul_le_mul_of_nonneg_right hCge3 (by positivity)
        rw [h3]
        linarith
      have hRge : (2 * β / c₀) * L ≤ a ^ ((2:ℝ)/3) * (t : ℝ) ^ ((1:ℝ)/3) :=
        le_of_pow_le_pow_left₀ (by norm_num) hRpos.le hcube
      have hβR : β * L ≤ c₀ * (a ^ ((2:ℝ)/3) * (t : ℝ) ^ ((1:ℝ)/3)) / 2 := by
        have h4 := mul_le_mul_of_nonneg_left hRge (by positivity : (0:ℝ) ≤ c₀ / 2)
        have h5 : c₀ / 2 * (2 * β / c₀ * L) = β * L := by field_simp
        rw [h5] at h4
        linarith
      have hexp1 : Real.exp (-(c₀ * (a ^ ((2:ℝ)/3) * (t : ℝ) ^ ((1:ℝ)/3)) / 2))
          ≤ Real.exp (-(β * L)) := Real.exp_le_exp.mpr (by linarith)
      have hexp2 : Real.exp (-(c₀ * (a ^ ((2:ℝ)/3) * (t : ℝ) ^ ((1:ℝ)/3)) / 2))
          ≤ 46080 / (c₀ ^ 6 * (a ^ 2 * (t : ℝ)) ^ 2) := by
        have h5 := exp_neg_le_div_pow
          (y := c₀ * (a ^ ((2:ℝ)/3) * (t : ℝ) ^ ((1:ℝ)/3)) / 2) (by positivity) 6
        have h6 : (Nat.factorial 6 : ℝ) = 720 := by norm_num [Nat.factorial]
        have hs : (a ^ ((2:ℝ)/3) * (t : ℝ) ^ ((1:ℝ)/3)) ^ 3 = a ^ 2 * (t : ℝ) :=
          rpow_cube_eq ha.le htpos.le
        have h7 : (c₀ * (a ^ ((2:ℝ)/3) * (t : ℝ) ^ ((1:ℝ)/3)) / 2) ^ 6
            = c₀ ^ 6 * (a ^ 2 * (t : ℝ)) ^ 2 / 64 := by
          calc (c₀ * (a ^ ((2:ℝ)/3) * (t : ℝ) ^ ((1:ℝ)/3)) / 2) ^ 6
              = c₀ ^ 6 * ((a ^ ((2:ℝ)/3) * (t : ℝ) ^ ((1:ℝ)/3)) ^ 3) ^ 2 / 64 := by ring
            _ = c₀ ^ 6 * (a ^ 2 * (t : ℝ)) ^ 2 / 64 := by rw [hs]
        rw [h6, h7] at h5
        calc Real.exp (-(c₀ * (a ^ ((2:ℝ)/3) * (t : ℝ) ^ ((1:ℝ)/3)) / 2))
            ≤ 720 / (c₀ ^ 6 * (a ^ 2 * (t : ℝ)) ^ 2 / 64) := h5
          _ = 46080 / (c₀ ^ 6 * (a ^ 2 * (t : ℝ)) ^ 2) := by
              field_simp
              ring
      have hsplit : Real.exp (-(c₀ * (a ^ ((2:ℝ)/3) * (t : ℝ) ^ ((1:ℝ)/3))))
          = Real.exp (-(c₀ * (a ^ ((2:ℝ)/3) * (t : ℝ) ^ ((1:ℝ)/3)) / 2))
            * Real.exp (-(c₀ * (a ^ ((2:ℝ)/3) * (t : ℝ) ^ ((1:ℝ)/3)) / 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hprod : Real.exp (-(c₀ * (a ^ ((2:ℝ)/3) * (t : ℝ) ^ ((1:ℝ)/3))))
          ≤ Real.exp (-(β * L)) * (46080 / (c₀ ^ 6 * (a ^ 2 * (t : ℝ)) ^ 2)) := by
        rw [hsplit]
        exact mul_le_mul hexp1 hexp2 (Real.exp_pos _).le (Real.exp_pos _).le
      have hptt : rangeExp d a t
          ≤ C₀ * Real.exp (-(c₀ * (a ^ ((2:ℝ)/3) * (t : ℝ) ^ ((1:ℝ)/3)))) := by
        have h := hpt a ha ha1 t ht1
        rwa [show c₀ * a ^ ((2:ℝ)/3) * (t : ℝ) ^ ((1:ℝ)/3)
            = c₀ * (a ^ ((2:ℝ)/3) * (t : ℝ) ^ ((1:ℝ)/3)) from by ring] at h
      have hstep : rangeExp d a t
          ≤ C₀ * (Real.exp (-(β * L)) * (46080 / (c₀ ^ 6 * (a ^ 2 * (t : ℝ)) ^ 2))) :=
        hptt.trans (mul_le_mul_of_nonneg_left hprod hC₀.le)
      refine hstep.trans ?_
      rw [hAdef]
      have hsq : ((t : ℝ) + 1) ^ 2 ≤ 4 * (t : ℝ) ^ 2 := by nlinarith [htR]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < c₀ ^ 6 * a ^ 4)]
      have hE : (0 : ℝ) < Real.exp (-(β * L)) := Real.exp_pos _
      have hexpand : C₀ * (Real.exp (-(β * L)) * (46080 / (c₀ ^ 6 * (a ^ 2 * (t : ℝ)) ^ 2)))
          * (c₀ ^ 6 * a ^ 4)
          = 46080 * C₀ * Real.exp (-(β * L)) / (t : ℝ) ^ 2 := by
        field_simp
      rw [hexpand, div_le_iff₀ (by positivity : (0:ℝ) < (t : ℝ) ^ 2)]
      have hone : 184320 * C₀ * Real.exp (-(β * L)) * (1 / ((t : ℝ) + 1) ^ 2) * (t : ℝ) ^ 2
          = 184320 * C₀ * Real.exp (-(β * L)) * ((t : ℝ) ^ 2 / ((t : ℝ) + 1) ^ 2) := by
        ring
      rw [hone]
      have hfrac : (1 : ℝ) / 4 ≤ (t : ℝ) ^ 2 / ((t : ℝ) + 1) ^ 2 := by
        rw [le_div_iff₀ (by positivity : (0:ℝ) < ((t : ℝ) + 1) ^ 2)]
        linarith [hsq]
      have hfin := mul_le_mul_of_nonneg_left hfrac
        (by positivity : (0:ℝ) ≤ 184320 * C₀ * Real.exp (-(β * L)))
      linarith [hfin]
    · rw [if_neg hT]
      positivity
  have hmajsum : Summable (fun t : ℕ => A * (1 / ((t : ℝ) + 1) ^ 2)) := hsum1.mul_left A
  have hnn : ∀ t : ℕ, (0 : ℝ) ≤ (if resolventThreshold d C a < (t : ℝ)
      then rangeExp d a t else 0) := by
    intro t
    by_cases hT : resolventThreshold d C a < (t : ℝ)
    · rw [if_pos hT, rangeExp]
      exact integral_nonneg fun p => (Real.exp_pos _).le
    · rw [if_neg hT]
  have hsummable : Summable (fun t : ℕ => if resolventThreshold d C a < (t : ℝ)
      then rangeExp d a t else 0) :=
    hmajsum.of_nonneg_of_le hnn hmaj
  refine ⟨hsummable, ?_⟩
  have hle1 : ∑' t : ℕ, (if resolventThreshold d C a < (t : ℝ)
      then rangeExp d a t else 0) ≤ ∑' t : ℕ, A * (1 / ((t : ℝ) + 1) ^ 2) :=
    hsummable.tsum_le_tsum hmaj hmajsum
  have heq : ∑' t : ℕ, A * (1 / ((t : ℝ) + 1) ^ 2)
      = A * ∑' t : ℕ, 1 / ((t : ℝ) + 1) ^ 2 := tsum_mul_left
  rw [heq] at hle1
  have hAC : A * C₁ ≤ 1 := by
    have hexp3 : Real.exp (-(β * L)) ≤ a ^ 5 * Real.exp (-(β - 5)) := by
      have hsp : -(β * L) = -((5 : ℝ) * L) + -((β - 5) * L) := by ring
      rw [hsp, Real.exp_add]
      have h1 : Real.exp (-((5 : ℝ) * L)) ≤ a ^ 5 := by
        have := exp_neg_nat_lambda_le ha 5
        rw [hLdef]
        simpa using this
      have h2 : Real.exp (-((β - 5) * L)) ≤ Real.exp (-(β - 5)) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith [hβ5, hL1]
      exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
    have hMexp : M * Real.exp (-(β - 5)) ≤ 1 := by
      have hlog : Real.log M ≤ β - 5 := by
        have : Real.log M ≤ |Real.log M| := le_abs_self _
        rw [hβdef]; linarith
      have h1 : M ≤ Real.exp (β - 5) := by
        rw [← Real.exp_log hMpos]
        exact Real.exp_le_exp.mpr hlog
      have h3 : (0 : ℝ) < Real.exp (-(β - 5)) := Real.exp_pos _
      have h4 := mul_le_mul_of_nonneg_right h1 h3.le
      have h5 : Real.exp (β - 5) * Real.exp (-(β - 5)) = 1 := by
        rw [← Real.exp_add]
        simp
      linarith [h4, h5]
    have hA3 : A * C₁ ≤ M * Real.exp (-(β - 5)) * a := by
      have hkey : A * C₁ = (184320 * C₀ * C₁ / (c₀ ^ 6 * a ^ 4)) * Real.exp (-(β * L)) := by
        rw [hAdef]; ring
      have hkey2 : M * Real.exp (-(β - 5)) * a
          = (184320 * C₀ * C₁ / (c₀ ^ 6 * a ^ 4)) * (a ^ 5 * Real.exp (-(β - 5))) := by
        rw [hM]; field_simp
      rw [hkey, hkey2]
      exact mul_le_mul_of_nonneg_left hexp3
        (by positivity : (0:ℝ) ≤ 184320 * C₀ * C₁ / (c₀ ^ 6 * a ^ 4))
    have hfin : M * Real.exp (-(β - 5)) * a ≤ M * Real.exp (-(β - 5)) * 1 :=
      mul_le_mul_of_nonneg_left ha1 (by positivity)
    linarith [hA3, hfin, hMexp]
  calc ∑' t : ℕ, (if resolventThreshold d C a < (t : ℝ)
        then rangeExp d a t else 0)
      ≤ A * ∑' t : ℕ, 1 / ((t : ℝ) + 1) ^ 2 := hle1
    _ ≤ A * C₁ := mul_le_mul_of_nonneg_left htsum1 hApos.le
    _ ≤ 1 := hAC

theorem log_le_four_sqrt {t : ℝ} (ht : 1 ≤ t) : Real.log (t + 2) ≤ 4 * Real.sqrt t := by
  have ht0 : (0:ℝ) < t := by linarith
  have h2 : (0:ℝ) < t + 2 := by linarith
  have hlog : Real.log (t + 2) ≤ 2 * Real.sqrt (t + 2) := by
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr h2)
    rw [Real.log_sqrt h2.le] at h
    linarith
  have hsq : Real.sqrt (t + 2) ≤ 2 * Real.sqrt t := by
    have h4 : t + 2 ≤ 4 * t := by linarith
    have h5 := Real.sqrt_le_sqrt h4
    rwa [show (4:ℝ) * t = 2 ^ 2 * t by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)] at h5
  linarith

theorem sqrt_exp (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  have h : Real.exp x = Real.exp (x / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
    ring
  rw [h, Real.sqrt_sq (Real.exp_pos _).le]

theorem exp_ge_sq_half {x : ℝ} (hx : 0 ≤ x) : x ^ 2 / 2 ≤ Real.exp x := by
  have h := Real.quadratic_le_exp_of_nonneg hx
  linarith

theorem eq_exp_one_mul_exp_neg_log {a : ℝ} (ha : 0 < a) :
    a = Real.exp 1 * Real.exp (-(Real.log (Real.exp 1 / a))) := by
  have hea : (0:ℝ) < Real.exp 1 / a := by positivity
  rw [Real.exp_neg, Real.exp_log hea]
  field_simp


set_option maxHeartbeats 1000000 in
/-- **Step 3 of `prop:resolvent` in dimension two** (`parking.tex:2715-2722`).
The paper splits the tail into dyadic blocks; the same effect is obtained here by
splitting on whether `log(t+2)` exceeds `p Λ`.  Below that threshold the horizon
`T = C a^{-1} Λ³` already forces the rate to exceed `κ Λ`; above it the time is
larger than `e^{pΛ}`, and `log(t+2) ≤ 4√t` makes the rate exceed `κ Λ` again. -/
theorem exists_resolvent_tail_two (hd : d = 2) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ a : ℝ, 0 < a → a ≤ 1 → ∀ t : ℕ, 1 ≤ t → Real.exp 1 / a ≤ (t : ℝ) →
        rangeExp d a t
          ≤ C * Real.exp (-(c * Real.sqrt (a * (t : ℝ) / Real.log ((t : ℝ) + 2))))) ∧
      ∀ a : ℝ, 0 < a → a ≤ 1 →
        Summable (fun t : ℕ => if resolventThreshold d C a < (t : ℝ)
            then rangeExp d a t else 0) ∧
          ∑' t : ℕ, (if resolventThreshold d C a < (t : ℝ)
            then rangeExp d a t else 0) ≤ 1 := by
  obtain ⟨c₀, C₀, hc₀, hC₀, hpt⟩ := exists_rangeExp_bound_two hd
  obtain ⟨C₁, hC₁, hsum1, htsum1⟩ := exists_tsum_inv_sq_le
  set M : ℝ := 10569646080 * C₀ * C₁ / c₀ ^ 8 with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  set β : ℝ := 6 + |Real.log M| with hβdef
  have hβ5 : 5 ≤ β := by
    have : 0 ≤ |Real.log M| := abs_nonneg _
    rw [hβdef]; linarith
  have hβpos : 0 < β := by linarith
  set κ : ℝ := 2 * β / c₀ + 1 with hκdef
  have hκ1 : 1 ≤ κ := by rw [hκdef]; have : 0 < 2 * β / c₀ := by positivity
                         linarith
  have hκβ : 2 * β / c₀ ≤ κ := by rw [hκdef]; linarith
  set p : ℝ := 2 + 6 * κ with hpdef
  have hp2 : (2 : ℝ) ≤ p := by rw [hpdef]; nlinarith [hκ1]
  set C : ℝ := max (max C₀ (Real.exp 1)) (κ ^ 2 * p) with hCdef
  have hCC₀ : C₀ ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCe : Real.exp 1 ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCκp : κ ^ 2 * p ≤ C := le_max_right _ _
  have hCpos : 0 < C := lt_of_lt_of_le hC₀ hCC₀
  refine ⟨c₀, C, hc₀, hCpos, ?_, ?_⟩
  · intro a ha ha1 t ht hte
    refine (hpt a ha ha1 t ht hte).trans ?_
    have := Real.exp_pos (-(c₀ * Real.sqrt (a * (t : ℝ) / Real.log ((t : ℝ) + 2))))
    nlinarith [hCC₀, this]
  intro a ha ha1
  set L : ℝ := Real.log (Real.exp 1 / a) with hLdef
  have hea : (0 : ℝ) < Real.exp 1 / a := by positivity
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hea, le_div_iff₀ ha]
    nlinarith [Real.exp_pos 1]
  have hLpos : (0 : ℝ) < L := by linarith
  have hTeq : resolventThreshold d C a = C * (a⁻¹ * L ^ 3) := by
    simp only [resolventThreshold, if_neg (by omega : d ≠ 1), if_pos hd, hLdef]
  have hTpos : (0 : ℝ) < resolventThreshold d C a := by
    rw [hTeq]; positivity
  have haT : a * resolventThreshold d C a = C * L ^ 3 := by
    rw [hTeq]; field_simp
  set A : ℝ := 10569646080 * C₀ * Real.exp (-(β * L)) / (c₀ ^ 8 * a ^ 4) with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hmaj : ∀ t : ℕ, (if resolventThreshold d C a < (t : ℝ)
      then rangeExp d a t else 0) ≤ A * (1 / ((t : ℝ) + 1) ^ 2) := by
    intro t
    by_cases hT : resolventThreshold d C a < (t : ℝ)
    · rw [if_pos hT]
      have ht1 : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with rfl | hpos
        · exfalso
          simp only [Nat.cast_zero] at hT
          linarith
        · exact hpos
      have htR : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
      have htpos : (0 : ℝ) < (t : ℝ) := by linarith
      have hLtpos : (0 : ℝ) < Real.log ((t : ℝ) + 2) := Real.log_pos (by linarith)
      -- the horizon exceeds `e/a`, so the pointwise bound applies
      have hte : Real.exp 1 / a ≤ (t : ℝ) := by
        have h1 : Real.exp 1 / a ≤ resolventThreshold d C a := by
          rw [hTeq]
          rw [div_le_iff₀ ha]
          have h2 : Real.exp 1 ≤ C := hCe
          have h3 : (1:ℝ) ≤ L ^ 3 := one_le_pow₀ hL1
          have h4 : C * (a⁻¹ * L ^ 3) * a = C * L ^ 3 := by field_simp
          rw [h4]
          nlinarith [h2, h3, hCpos]
        linarith
      -- the key lower bound on the rate
      have hat : C * L ^ 3 < a * (t : ℝ) := by
        have := mul_lt_mul_of_pos_left hT ha
        rwa [haT] at this
      have hkey : κ ^ 2 * L ^ 2 * Real.log ((t : ℝ) + 2) ≤ a * (t : ℝ) := by
        by_cases hcase : Real.log ((t : ℝ) + 2) ≤ p * L
        · have h1 : κ ^ 2 * L ^ 2 * Real.log ((t : ℝ) + 2) ≤ κ ^ 2 * L ^ 2 * (p * L) :=
            mul_le_mul_of_nonneg_left hcase (by positivity)
          have h2 : κ ^ 2 * L ^ 2 * (p * L) = κ ^ 2 * p * L ^ 3 := by ring
          have h3 : κ ^ 2 * p * L ^ 3 ≤ C * L ^ 3 :=
            mul_le_mul_of_nonneg_right hCκp (by positivity)
          linarith
        · rw [not_le] at hcase
          have hexplt : Real.exp (p * L) < (t : ℝ) + 2 := by
            rw [← Real.lt_log_iff_exp_lt (by linarith : (0:ℝ) < (t : ℝ) + 2)]
            exact hcase
          have hpL2 : (2 : ℝ) ≤ p * L := by nlinarith [hp2, hL1]
          have hexp4 : (4 : ℝ) ≤ Real.exp (p * L) := by
            have h1 : Real.exp 2 ≤ Real.exp (p * L) := Real.exp_le_exp.mpr hpL2
            have h2 : (4:ℝ) ≤ Real.exp 2 := by
              have h9 := Real.exp_one_gt_d9
              have h10 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
                rw [← Real.exp_add]; norm_num
              nlinarith [h9, h10, Real.exp_pos 1]
            linarith
          have ht2 : Real.exp (p * L) / 2 ≤ (t : ℝ) := by linarith
          have hsqrtt : Real.exp (p * L / 2) / Real.sqrt 2 ≤ Real.sqrt (t : ℝ) := by
            have h1 := Real.sqrt_le_sqrt ht2
            rwa [Real.sqrt_div' (Real.exp (p * L)) (by norm_num : (0:ℝ) ≤ 2), sqrt_exp] at h1
          have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
            have h1 : Real.sqrt 2 ≤ Real.sqrt ((3 / 2 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
            rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3 / 2)] at h1
          have hs2pos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
          have hstep : Real.exp (p * L / 2) / (3 / 2) ≤ Real.sqrt (t : ℝ) := by
            refine le_trans ?_ hsqrtt
            exact div_le_div_of_nonneg_left (Real.exp_pos _).le hs2pos hs2
          have haexp : a * Real.exp (p * L / 2) = Real.exp 1 * Real.exp (3 * κ * L) := by
            nth_rewrite 1 [eq_exp_one_mul_exp_neg_log ha]
            rw [← hLdef, mul_assoc, ← Real.exp_add]
            congr 2
            rw [hpdef]
            ring
          have hq : (3 * κ * L) ^ 2 / 2 ≤ Real.exp (3 * κ * L) :=
            exp_ge_sq_half (by positivity)
          have hasqrt : 4 * (κ ^ 2 * L ^ 2) ≤ a * Real.sqrt (t : ℝ) := by
            have h1 : a * (Real.exp (p * L / 2) / (3 / 2)) ≤ a * Real.sqrt (t : ℝ) :=
              mul_le_mul_of_nonneg_left hstep ha.le
            have h2 : a * (Real.exp (p * L / 2) / (3 / 2))
                = Real.exp 1 * Real.exp (3 * κ * L) / (3 / 2) := by
              rw [← haexp]; ring
            rw [h2] at h1
            have h3 : (27 / 10 : ℝ) ≤ Real.exp 1 := by nlinarith [Real.exp_one_gt_d9]
            have h4 : (0:ℝ) ≤ (3 * κ * L) ^ 2 / 2 := by positivity
            have hA : (27 / 10 : ℝ) * ((3 * κ * L) ^ 2 / 2)
                ≤ Real.exp 1 * Real.exp (3 * κ * L) := by
              have hc : (27 / 10 : ℝ) * ((3 * κ * L) ^ 2 / 2)
                  ≤ Real.exp 1 * ((3 * κ * L) ^ 2 / 2) :=
                mul_le_mul_of_nonneg_right h3 h4
              have hdd : Real.exp 1 * ((3 * κ * L) ^ 2 / 2)
                  ≤ Real.exp 1 * Real.exp (3 * κ * L) :=
                mul_le_mul_of_nonneg_left hq (Real.exp_pos 1).le
              linarith
            have hx : (0:ℝ) ≤ κ ^ 2 * L ^ 2 := by positivity
            have hB : 4 * (κ ^ 2 * L ^ 2) ≤ (27 / 10 : ℝ) * ((3 * κ * L) ^ 2 / 2) / (3 / 2) := by
              nlinarith [hx]
            linarith [h1, hA, hB]
          have hLt4 : Real.log ((t : ℝ) + 2) ≤ 4 * Real.sqrt (t : ℝ) := log_le_four_sqrt htR
          have hsq : Real.sqrt (t : ℝ) * Real.sqrt (t : ℝ) = (t : ℝ) :=
            Real.mul_self_sqrt htpos.le
          have h5 : κ ^ 2 * L ^ 2 * Real.log ((t : ℝ) + 2)
              ≤ κ ^ 2 * L ^ 2 * (4 * Real.sqrt (t : ℝ)) :=
            mul_le_mul_of_nonneg_left hLt4 (by positivity)
          have h6 : (κ ^ 2 * L ^ 2 * 4) * Real.sqrt (t : ℝ)
              ≤ (a * Real.sqrt (t : ℝ)) * Real.sqrt (t : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith [hasqrt]) (Real.sqrt_nonneg _)
          have h7 : (a * Real.sqrt (t : ℝ)) * Real.sqrt (t : ℝ) = a * (t : ℝ) := by
            rw [mul_assoc, hsq]
          linarith
      -- the rate is at least `κ L`
      have hratepos : (0 : ℝ) ≤ a * (t : ℝ) / Real.log ((t : ℝ) + 2) := by positivity
      have hrate1 : κ * L ≤ Real.sqrt (a * (t : ℝ) / Real.log ((t : ℝ) + 2)) := by
        have h1 : (κ * L) ^ 2 ≤ a * (t : ℝ) / Real.log ((t : ℝ) + 2) := by
          rw [le_div_iff₀ hLtpos]
          have : (κ * L) ^ 2 = κ ^ 2 * L ^ 2 := by ring
          rw [this]
          exact hkey
        have h2 := Real.sqrt_le_sqrt h1
        rwa [Real.sqrt_sq (by positivity)] at h2
      -- the rate is at least `√(a √t)/2`
      have hrate2 : Real.sqrt (a * Real.sqrt (t : ℝ)) / 2
          ≤ Real.sqrt (a * (t : ℝ) / Real.log ((t : ℝ) + 2)) := by
        have hLt4 : Real.log ((t : ℝ) + 2) ≤ 4 * Real.sqrt (t : ℝ) := log_le_four_sqrt htR
        have hsq : Real.sqrt (t : ℝ) * Real.sqrt (t : ℝ) = (t : ℝ) :=
          Real.mul_self_sqrt htpos.le
        have hspos : (0 : ℝ) < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr htpos
        have h1 : a * Real.sqrt (t : ℝ) / 4 ≤ a * (t : ℝ) / Real.log ((t : ℝ) + 2) := by
          rw [div_le_div_iff₀ (by norm_num) hLtpos]
          have h2 : a * Real.sqrt (t : ℝ) * Real.log ((t : ℝ) + 2)
              ≤ a * Real.sqrt (t : ℝ) * (4 * Real.sqrt (t : ℝ)) :=
            mul_le_mul_of_nonneg_left hLt4 (by positivity)
          have h3 : a * Real.sqrt (t : ℝ) * (4 * Real.sqrt (t : ℝ)) = a * (t : ℝ) * 4 := by
            rw [show a * Real.sqrt (t : ℝ) * (4 * Real.sqrt (t : ℝ))
              = 4 * a * (Real.sqrt (t : ℝ) * Real.sqrt (t : ℝ)) by ring, hsq]
            ring
          linarith
        have h4 := Real.sqrt_le_sqrt h1
        rwa [Real.sqrt_div' (a * Real.sqrt (t : ℝ)) (by norm_num : (0:ℝ) ≤ 4),
          show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)] at h4
      set R : ℝ := Real.sqrt (a * (t : ℝ) / Real.log ((t : ℝ) + 2)) with hRdef
      set w : ℝ := Real.sqrt (a * Real.sqrt (t : ℝ)) with hwdef
      have hwpos : (0 : ℝ) < w := by
        rw [hwdef]
        refine Real.sqrt_pos.mpr ?_
        have : (0:ℝ) < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr htpos
        positivity
      have hw8 : w ^ 8 = a ^ 4 * (t : ℝ) ^ 2 := by
        have hw2 : w ^ 2 = a * Real.sqrt (t : ℝ) := by
          rw [hwdef]
          exact Real.sq_sqrt (by positivity)
        have hs4 : Real.sqrt (t : ℝ) ^ 4 = (t : ℝ) ^ 2 := sqrt_pow_four htpos.le
        calc w ^ 8 = (w ^ 2) ^ 4 := by ring
          _ = (a * Real.sqrt (t : ℝ)) ^ 4 := by rw [hw2]
          _ = a ^ 4 * Real.sqrt (t : ℝ) ^ 4 := by ring
          _ = a ^ 4 * (t : ℝ) ^ 2 := by rw [hs4]
      have hexp1 : Real.exp (-(c₀ * R / 2)) ≤ Real.exp (-(β * L)) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : 2 * β / c₀ * L ≤ κ * L := mul_le_mul_of_nonneg_right hκβ hLpos.le
        have h2 : κ * L ≤ R := hrate1
        have h3 : c₀ / 2 * (2 * β / c₀ * L) = β * L := by field_simp
        have h4 := mul_le_mul_of_nonneg_left (le_trans h1 h2) (by positivity : (0:ℝ) ≤ c₀ / 2)
        rw [h3] at h4
        linarith
      have hexp2 : Real.exp (-(c₀ * R / 2)) ≤ 2642411520 / (c₀ ^ 8 * (a ^ 4 * (t : ℝ) ^ 2)) := by
        have hy : (0 : ℝ) < c₀ * w / 4 := by positivity
        have h5 := exp_neg_le_div_pow (y := c₀ * w / 4) hy 8
        have h6 : (Nat.factorial 8 : ℝ) = 40320 := by norm_num [Nat.factorial]
        have h7 : (c₀ * w / 4) ^ 8 = c₀ ^ 8 * (a ^ 4 * (t : ℝ) ^ 2) / 65536 := by
          calc (c₀ * w / 4) ^ 8 = c₀ ^ 8 * w ^ 8 / 65536 := by ring
            _ = c₀ ^ 8 * (a ^ 4 * (t : ℝ) ^ 2) / 65536 := by rw [hw8]
        rw [h6, h7] at h5
        have h8 : Real.exp (-(c₀ * R / 2)) ≤ Real.exp (-(c₀ * w / 4)) := by
          refine Real.exp_le_exp.mpr ?_
          have h9 := mul_le_mul_of_nonneg_left hrate2 (by positivity : (0:ℝ) ≤ c₀)
          have h10 : c₀ * (w / 2) = c₀ * w / 2 := by ring
          linarith [h9, h10]
        have heq2 : (40320:ℝ) / (c₀ ^ 8 * (a ^ 4 * (t : ℝ) ^ 2) / 65536)
            = 2642411520 / (c₀ ^ 8 * (a ^ 4 * (t : ℝ) ^ 2)) := by
          rw [div_div_eq_mul_div]
          ring
        exact h8.trans (h5.trans (le_of_eq heq2))
      have hsplit : Real.exp (-(c₀ * R)) = Real.exp (-(c₀ * R / 2)) * Real.exp (-(c₀ * R / 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hprod : Real.exp (-(c₀ * R))
          ≤ Real.exp (-(β * L)) * (2642411520 / (c₀ ^ 8 * (a ^ 4 * (t : ℝ) ^ 2))) := by
        rw [hsplit]
        exact mul_le_mul hexp1 hexp2 (Real.exp_pos _).le (Real.exp_pos _).le
      have hstep : rangeExp d a t
          ≤ C₀ * (Real.exp (-(β * L)) * (2642411520 / (c₀ ^ 8 * (a ^ 4 * (t : ℝ) ^ 2)))) :=
        (hpt a ha ha1 t ht1 hte).trans (mul_le_mul_of_nonneg_left hprod hC₀.le)
      refine hstep.trans ?_
      rw [hAdef]
      have hsqq : ((t : ℝ) + 1) ^ 2 ≤ 4 * (t : ℝ) ^ 2 := by nlinarith [htR]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < c₀ ^ 8 * a ^ 4)]
      have hE : (0 : ℝ) < Real.exp (-(β * L)) := Real.exp_pos _
      have hexpand : C₀ * (Real.exp (-(β * L)) * (2642411520 / (c₀ ^ 8 * (a ^ 4 * (t : ℝ) ^ 2))))
          * (c₀ ^ 8 * a ^ 4)
          = 2642411520 * C₀ * Real.exp (-(β * L)) / (t : ℝ) ^ 2 := by
        field_simp
      rw [hexpand, div_le_iff₀ (by positivity : (0:ℝ) < (t : ℝ) ^ 2)]
      have hone : 10569646080 * C₀ * Real.exp (-(β * L)) * (1 / ((t : ℝ) + 1) ^ 2) * (t : ℝ) ^ 2
          = 10569646080 * C₀ * Real.exp (-(β * L)) * ((t : ℝ) ^ 2 / ((t : ℝ) + 1) ^ 2) := by
        ring
      rw [hone]
      have hfrac : (1 : ℝ) / 4 ≤ (t : ℝ) ^ 2 / ((t : ℝ) + 1) ^ 2 := by
        rw [le_div_iff₀ (by positivity : (0:ℝ) < ((t : ℝ) + 1) ^ 2)]
        linarith [hsqq]
      have hfin := mul_le_mul_of_nonneg_left hfrac
        (by positivity : (0:ℝ) ≤ 10569646080 * C₀ * Real.exp (-(β * L)))
      linarith [hfin]
    · rw [if_neg hT]
      positivity
  have hmajsum : Summable (fun t : ℕ => A * (1 / ((t : ℝ) + 1) ^ 2)) := hsum1.mul_left A
  have hnn : ∀ t : ℕ, (0 : ℝ) ≤ (if resolventThreshold d C a < (t : ℝ)
      then rangeExp d a t else 0) := by
    intro t
    by_cases hT : resolventThreshold d C a < (t : ℝ)
    · rw [if_pos hT, rangeExp]
      exact integral_nonneg fun p => (Real.exp_pos _).le
    · rw [if_neg hT]
  have hsummable : Summable (fun t : ℕ => if resolventThreshold d C a < (t : ℝ)
      then rangeExp d a t else 0) :=
    hmajsum.of_nonneg_of_le hnn hmaj
  refine ⟨hsummable, ?_⟩
  have hle1 : ∑' t : ℕ, (if resolventThreshold d C a < (t : ℝ)
      then rangeExp d a t else 0) ≤ ∑' t : ℕ, A * (1 / ((t : ℝ) + 1) ^ 2) :=
    hsummable.tsum_le_tsum hmaj hmajsum
  have heq : ∑' t : ℕ, A * (1 / ((t : ℝ) + 1) ^ 2)
      = A * ∑' t : ℕ, 1 / ((t : ℝ) + 1) ^ 2 := tsum_mul_left
  rw [heq] at hle1
  have hAC : A * C₁ ≤ 1 := by
    have hexp3 : Real.exp (-(β * L)) ≤ a ^ 5 * Real.exp (-(β - 5)) := by
      have hsp : -(β * L) = -((5 : ℝ) * L) + -((β - 5) * L) := by ring
      rw [hsp, Real.exp_add]
      have h1 : Real.exp (-((5 : ℝ) * L)) ≤ a ^ 5 := by
        have h := exp_neg_nat_lambda_le ha 5
        rw [hLdef]
        simpa using h
      have h2 : Real.exp (-((β - 5) * L)) ≤ Real.exp (-(β - 5)) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith [hβ5, hL1]
      exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
    have hMexp : M * Real.exp (-(β - 5)) ≤ 1 := by
      have hlog : Real.log M ≤ β - 5 := by
        have : Real.log M ≤ |Real.log M| := le_abs_self _
        rw [hβdef]; linarith
      have h1 : M ≤ Real.exp (β - 5) := by
        rw [← Real.exp_log hMpos]
        exact Real.exp_le_exp.mpr hlog
      have h3 : (0 : ℝ) < Real.exp (-(β - 5)) := Real.exp_pos _
      have h4 := mul_le_mul_of_nonneg_right h1 h3.le
      have h5 : Real.exp (β - 5) * Real.exp (-(β - 5)) = 1 := by
        rw [← Real.exp_add]
        simp
      linarith [h4, h5]
    have hA3 : A * C₁ ≤ M * Real.exp (-(β - 5)) * a := by
      have hkey : A * C₁
          = (10569646080 * C₀ * C₁ / (c₀ ^ 8 * a ^ 4)) * Real.exp (-(β * L)) := by
        rw [hAdef]; ring
      have hkey2 : M * Real.exp (-(β - 5)) * a
          = (10569646080 * C₀ * C₁ / (c₀ ^ 8 * a ^ 4)) * (a ^ 5 * Real.exp (-(β - 5))) := by
        rw [hM]; field_simp
      rw [hkey, hkey2]
      exact mul_le_mul_of_nonneg_left hexp3
        (by positivity : (0:ℝ) ≤ 10569646080 * C₀ * C₁ / (c₀ ^ 8 * a ^ 4))
    have hfin : M * Real.exp (-(β - 5)) * a ≤ M * Real.exp (-(β - 5)) * 1 :=
      mul_le_mul_of_nonneg_left ha1 (by positivity)
    linarith [hA3, hfin, hMexp]
  calc ∑' t : ℕ, (if resolventThreshold d C a < (t : ℝ)
        then rangeExp d a t else 0)
      ≤ A * ∑' t : ℕ, 1 / ((t : ℝ) + 1) ^ 2 := hle1
    _ ≤ A * C₁ := mul_le_mul_of_nonneg_left htsum1 hApos.le
    _ ≤ 1 := hAC

end Parking

end
