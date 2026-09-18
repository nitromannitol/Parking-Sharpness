/-
Step 1 of the proof of `lem:critical-density` (`parking.tex:1250-1279`): the
resampled configuration.

The paper writes: "Let `γ > 0` be the expected absolute difference between two
independent variables with the law of `η(0)`.  Fix `ε` with `0 ≤ ε ≤ γ`.
Independently at each site, replace `η(x)` by an independent copy with
probability `ε/γ`.  The expected absolute change at each site is `ε`, and the
resampled configuration has the same law as `η`. ...  The change at each site is
symmetric, so its positive and negative parts have mean `ε/2`."

Every assertion in that paragraph is about ONE site, lifted to the lattice by
independence.  The one-site object is the joint law of the pair `(η(x), η̃(x))`:

    resampleOne ν p = (1 - p) • (ν pushed along the diagonal) + p • (ν ⊗ ν),

a probability measure on `ℤ × ℤ` when `p ≤ 1`.  Its two marginals are `ν`, which
is "the resampled configuration has the same law as `η`"; it is invariant under
the swap, which is "the change at each site is symmetric"; the mean absolute
difference under it is `p γ`, which is the paper's `ε` at `p = ε/γ`; and the
positive part then has mean `p γ / 2`.

The lattice statements are these read through the coordinatewise pushforward of
an independent family, `LatticeProb.iidLaw_map_pi`, and through
`Measure.infinitePi_map_eval` for one site.

What is NOT here is the coupled DYNAMICS: the matching of `A_t(x) ∧ Ã_t(x)`
active particles at each site, the labels with priorities, and the freshness
argument of Step 2.  `CriticalQuadratic.lean` records exactly what those owe the
rest of the proof.
-/
import Parking.Support.CriticalQuadratic
import LatticeProb.Prob.MapPi

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Parking

open LatticeProb

/-! ### The one-site joint law -/

/-- The joint law of a value and its resampling: with probability `p` the second
coordinate is an independent draw, and otherwise it is the first coordinate. -/
def resampleOne (ν : Measure ℤ) (p : ℝ≥0∞) : Measure (ℤ × ℤ) :=
  (1 - p) • (ν.map fun k => (k, k)) + p • (ν.prod ν)

/-- The mean absolute difference between two independent copies, the paper's
`γ`. -/
def gammaOf (ν : Measure ℤ) : ℝ := ∫ q : ℤ × ℤ, |(q.2 : ℝ) - (q.1 : ℝ)| ∂(ν.prod ν)

theorem measurable_diagInt : Measurable (fun k : ℤ => (k, k)) :=
  measurable_id.prodMk measurable_id

theorem measurable_absDiff : Measurable (fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|) := by
  fun_prop

theorem resampleOne_isProbability (ν : Measure ℤ) [IsProbabilityMeasure ν] {p : ℝ≥0∞}
    (hp : p ≤ 1) : IsProbabilityMeasure (resampleOne ν p) := by
  constructor
  rw [resampleOne]
  simp only [Measure.coe_add, Pi.add_apply, Measure.smul_apply,
    Measure.map_apply measurable_diagInt MeasurableSet.univ, Set.preimage_univ, measure_univ,
    smul_eq_mul, mul_one]
  exact tsub_add_cancel_of_le hp

/-- **The resampled value has the law of the original.**  The paper's "the
resampled configuration has the same law as `η`", at one site. -/
theorem resampleOne_map_snd (ν : Measure ℤ) [IsProbabilityMeasure ν] {p : ℝ≥0∞}
    (hp : p ≤ 1) : (resampleOne ν p).map Prod.snd = ν := by
  rw [resampleOne, Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul]
  have h1 : (ν.map fun k : ℤ => (k, k)).map Prod.snd = ν := by
    rw [Measure.map_map measurable_snd measurable_diagInt]
    exact Measure.map_id
  have h2 : (ν.prod ν).map Prod.snd = ν := Measure.snd_prod
  rw [h1, h2, ← add_smul, tsub_add_cancel_of_le hp, one_smul]

theorem resampleOne_map_fst (ν : Measure ℤ) [IsProbabilityMeasure ν] {p : ℝ≥0∞}
    (hp : p ≤ 1) : (resampleOne ν p).map Prod.fst = ν := by
  rw [resampleOne, Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul]
  have h1 : (ν.map fun k : ℤ => (k, k)).map Prod.fst = ν := by
    rw [Measure.map_map measurable_fst measurable_diagInt]
    exact Measure.map_id
  have h2 : (ν.prod ν).map Prod.fst = ν := Measure.fst_prod
  rw [h1, h2, ← add_smul, tsub_add_cancel_of_le hp, one_smul]

/-- **The change at each site is symmetric.**  Neither the diagonal part nor the
independent part distinguishes the two coordinates. -/
theorem resampleOne_map_swap (ν : Measure ℤ) (p : ℝ≥0∞) :
    (resampleOne ν p).map Prod.swap = resampleOne ν p := by
  rw [resampleOne, Measure.map_add _ _ measurable_swap, Measure.map_smul, Measure.map_smul]
  have h1 : (ν.map fun k : ℤ => (k, k)).map Prod.swap = ν.map fun k : ℤ => (k, k) := by
    rw [Measure.map_map measurable_swap measurable_diagInt]
    rfl
  have h2 : (ν.prod ν).map Prod.swap = ν.prod ν := Measure.prod_swap
  rw [h1, h2]

/-! ### The size of the change -/

theorem integrable_absDiff_resampleOne (ν : Measure ℤ) [IsProbabilityMeasure ν] {p : ℝ≥0∞}
    (hp : p ≤ 1) (hint : Integrable (fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|) (ν.prod ν)) :
    Integrable (fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|) (resampleOne ν p) := by
  have hp1 : (1 - p) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hp
  have hI1 : Integrable (fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|)
      ((1 - p) • (ν.map fun k : ℤ => (k, k))) := by
    refine Integrable.smul_measure ?_ hp1
    rw [integrable_map_measure measurable_absDiff.aestronglyMeasurable
      measurable_diagInt.aemeasurable]
    have hcomp : ((fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|) ∘ fun k : ℤ => (k, k))
        = fun _ : ℤ => (0 : ℝ) := by
      funext k; simp
    rw [hcomp]
    exact integrable_zero ℤ ℝ ν
  have hI2 : Integrable (fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|) (p • (ν.prod ν)) :=
    hint.smul_measure hpt
  rw [resampleOne]
  exact hI1.add_measure hI2

/-- **The expected absolute change at each site is `p γ`.**  At `p = ε/γ` this is
the paper's `ε`. -/
theorem integral_absDiff_resampleOne (ν : Measure ℤ) [IsProbabilityMeasure ν] {p : ℝ≥0∞}
    (hp : p ≤ 1) (hint : Integrable (fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|) (ν.prod ν)) :
    ∫ q : ℤ × ℤ, |(q.2 : ℝ) - (q.1 : ℝ)| ∂(resampleOne ν p) = p.toReal * gammaOf ν := by
  have hp1 : (1 - p) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hp
  have hzero : ∫ q : ℤ × ℤ, |(q.2 : ℝ) - (q.1 : ℝ)|
      ∂((1 - p) • (ν.map fun k : ℤ => (k, k))) = 0 := by
    rw [integral_smul_measure,
      integral_map measurable_diagInt.aemeasurable measurable_absDiff.aestronglyMeasurable]
    simp
  have hI1 : Integrable (fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|)
      ((1 - p) • (ν.map fun k : ℤ => (k, k))) := by
    refine Integrable.smul_measure ?_ hp1
    rw [integrable_map_measure measurable_absDiff.aestronglyMeasurable
      measurable_diagInt.aemeasurable]
    have hcomp : ((fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|) ∘ fun k : ℤ => (k, k))
        = fun _ : ℤ => (0 : ℝ) := by
      funext k; simp
    rw [hcomp]
    exact integrable_zero ℤ ℝ ν
  have hI2 : Integrable (fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|) (p • (ν.prod ν)) :=
    hint.smul_measure hpt
  rw [resampleOne, integral_add_measure hI1 hI2, hzero, zero_add, integral_smul_measure,
    gammaOf, smul_eq_mul]

/-- **The positive part of the change has mean `p γ / 2`.**  The paper's "the
change at each site is symmetric, so its positive and negative parts have mean
`ε/2`".  The two parts have the same mean because the joint law is invariant
under the swap, and they add up to the absolute change. -/
theorem integral_posPart_resampleOne (ν : Measure ℤ) [IsProbabilityMeasure ν] {p : ℝ≥0∞}
    (hp : p ≤ 1) (hint : Integrable (fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|) (ν.prod ν)) :
    ∫ q : ℤ × ℤ, max ((q.2 : ℝ) - (q.1 : ℝ)) 0 ∂(resampleOne ν p)
      = p.toReal * gammaOf ν / 2 := by
  set μ := resampleOne ν p with hμ
  have hI : Integrable (fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|) μ :=
    integrable_absDiff_resampleOne ν hp hint
  have hposm : Measurable (fun q : ℤ × ℤ => max ((q.2 : ℝ) - (q.1 : ℝ)) 0) := by fun_prop
  have hnegm : Measurable (fun q : ℤ × ℤ => max ((q.1 : ℝ) - (q.2 : ℝ)) 0) := by fun_prop
  have hposI : Integrable (fun q : ℤ × ℤ => max ((q.2 : ℝ) - (q.1 : ℝ)) 0) μ := by
    refine hI.mono' hposm.aestronglyMeasurable (Filter.Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hnegI : Integrable (fun q : ℤ × ℤ => max ((q.1 : ℝ) - (q.2 : ℝ)) 0) μ := by
    refine hI.mono' hnegm.aestronglyMeasurable (Filter.Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (abs_nonneg _)
    rw [← abs_neg]
    simpa using le_abs_self (-((q.2 : ℝ) - (q.1 : ℝ)))
  have hswap : ∫ q : ℤ × ℤ, max ((q.2 : ℝ) - (q.1 : ℝ)) 0 ∂μ
      = ∫ q : ℤ × ℤ, max ((q.1 : ℝ) - (q.2 : ℝ)) 0 ∂μ := by
    conv_lhs => rw [hμ, ← resampleOne_map_swap ν p]
    rw [integral_map measurable_swap.aemeasurable hposm.aestronglyMeasurable]
    rfl
  have hsum : ∫ q : ℤ × ℤ, max ((q.2 : ℝ) - (q.1 : ℝ)) 0 ∂μ
      + ∫ q : ℤ × ℤ, max ((q.1 : ℝ) - (q.2 : ℝ)) 0 ∂μ = p.toReal * gammaOf ν := by
    rw [← integral_add hposI hnegI, ← integral_absDiff_resampleOne ν hp hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only []
    show max ((q.2 : ℝ) - (q.1 : ℝ)) 0 + max ((q.1 : ℝ) - (q.2 : ℝ)) 0
      = |(q.2 : ℝ) - (q.1 : ℝ)|
    rcases le_total ((q.1 : ℝ)) ((q.2 : ℝ)) with h | h
    · have h1 : max ((q.2 : ℝ) - (q.1 : ℝ)) 0 = (q.2 : ℝ) - (q.1 : ℝ) :=
        max_eq_left (by linarith)
      have h2 : max ((q.1 : ℝ) - (q.2 : ℝ)) 0 = 0 := max_eq_right (by linarith)
      have h3 : |(q.2 : ℝ) - (q.1 : ℝ)| = (q.2 : ℝ) - (q.1 : ℝ) := abs_of_nonneg (by linarith)
      rw [h1, h2, h3]; ring
    · have h1 : max ((q.2 : ℝ) - (q.1 : ℝ)) 0 = 0 := max_eq_right (by linarith)
      have h2 : max ((q.1 : ℝ) - (q.2 : ℝ)) 0 = (q.1 : ℝ) - (q.2 : ℝ) :=
        max_eq_left (by linarith)
      have h3 : |(q.2 : ℝ) - (q.1 : ℝ)| = -((q.2 : ℝ) - (q.1 : ℝ)) := abs_of_nonpos (by linarith)
      rw [h1, h2, h3]; ring
  rw [hswap] at hsum ⊢
  linarith


/-! ### `γ` is finite and positive -/

/-- A first moment for the one-site law makes the absolute difference integrable
under the product, so `gammaOf` is an honest integral. -/
theorem integrable_absDiff_prod (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) :
    Integrable (fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|) (ν.prod ν) := by
  have h1 : Integrable (fun q : ℤ × ℤ => |(q.1 : ℝ)|) (ν.prod ν) := Integrable.comp_fst hint ν
  have h2 : Integrable (fun q : ℤ × ℤ => |(q.2 : ℝ)|) (ν.prod ν) := Integrable.comp_snd hint ν
  refine (h1.add h2).mono' measurable_absDiff.aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
  show |(q.2 : ℝ) - (q.1 : ℝ)| ≤ |(q.1 : ℝ)| + |(q.2 : ℝ)|
  have h := abs_sub ((q.2 : ℝ)) ((q.1 : ℝ))
  linarith [h]

/-- Some value carries positive mass, since the law is a probability measure on a
countable space. -/
theorem exists_atom (ν : Measure ℤ) [IsProbabilityMeasure ν] : ∃ a : ℤ, 0 < ν {a} := by
  by_contra hc
  simp only [not_exists, not_lt] at hc
  have hz : ∀ a : ℤ, ν {a} = 0 := fun a => le_antisymm (hc a) (zero_le)
  have huniv : ν (Set.univ : Set ℤ) = 0 := by
    have hcov : (Set.univ : Set ℤ) = ⋃ a : ℤ, ({a} : Set ℤ) := by
      ext k; simp
    rw [hcov, measure_iUnion_null_iff]
    exact hz
  rw [measure_univ] at huniv
  exact one_ne_zero huniv

/-- **`γ > 0` for a nonconstant law.**  Two distinct values carry positive mass,
and the pair of them contributes at least the product of those masses. -/
theorem gammaOf_pos (ν : Measure ℤ) [IsProbabilityMeasure ν] (hnc : ∀ k : ℤ, ν {k} ≠ 1)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) : 0 < gammaOf ν := by
  classical
  obtain ⟨a, ha⟩ := exists_atom ν
  -- a second value with positive mass
  have hlt : ν {a} < 1 := lt_of_le_of_ne prob_le_one (hnc a)
  have hcompl : 0 < ν ({a}ᶜ : Set ℤ) := by
    rw [measure_compl (measurableSet_singleton a) (measure_ne_top ν _), measure_univ]
    exact tsub_pos_of_lt hlt
  have hb : ∃ b : ℤ, b ≠ a ∧ 0 < ν {b} := by
    by_contra hc
    simp only [not_exists, not_and, not_lt] at hc
    have hz : ∀ b : {b : ℤ // b ≠ a}, ν {(b : ℤ)} = 0 := by
      intro b
      exact le_antisymm (hc (b : ℤ) b.2) (zero_le)
    have hcov : ({a}ᶜ : Set ℤ) = ⋃ b : {b : ℤ // b ≠ a}, ({(b : ℤ)} : Set ℤ) := by
      ext k
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion, Subtype.exists]
      constructor
      · intro hk; exact ⟨k, hk, rfl⟩
      · rintro ⟨b, hb, rfl⟩; exact hb
    have hnull : ν ({a}ᶜ : Set ℤ) = 0 := by
      rw [hcov, measure_iUnion_null_iff]
      exact hz
    rw [hnull] at hcompl
    exact lt_irrefl 0 hcompl
  obtain ⟨b, hba, hbpos⟩ := hb
  set S : Set (ℤ × ℤ) := ({a} : Set ℤ) ×ˢ ({b} : Set ℤ) with hS
  have hSmeas : MeasurableSet S :=
    (measurableSet_singleton a).prod (measurableSet_singleton b)
  have hSmass : (ν.prod ν) S = ν {a} * ν {b} := Measure.prod_prod _ _
  have hI : Integrable (fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|) (ν.prod ν) :=
    integrable_absDiff_prod ν hint
  have hone : ∀ q ∈ S, (1 : ℝ) ≤ |(q.2 : ℝ) - (q.1 : ℝ)| := by
    intro q hq
    rw [hS, Set.mem_prod, Set.mem_singleton_iff, Set.mem_singleton_iff] at hq
    obtain ⟨h1, h2⟩ := hq
    rw [h1, h2]
    have hne : b - a ≠ 0 := sub_ne_zero_of_ne hba
    have : (1 : ℤ) ≤ |b - a| := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [abs_of_neg hlt]; omega
      · rw [abs_of_pos hgt]; omega
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|b - a| : ℤ) : ℝ) := by exact_mod_cast this
      _ = |(b : ℝ) - (a : ℝ)| := by push_cast [Int.cast_abs]; ring_nf
  have hlow : (ν.prod ν).real S • (1 : ℝ)
      ≤ ∫ q in S, |(q.2 : ℝ) - (q.1 : ℝ)| ∂(ν.prod ν) :=
    setIntegral_ge_of_const_le hSmeas (measure_ne_top _ _) hone hI.integrableOn
  have hup : ∫ q in S, |(q.2 : ℝ) - (q.1 : ℝ)| ∂(ν.prod ν)
      ≤ gammaOf ν :=
    setIntegral_le_integral hI (Filter.Eventually.of_forall fun q => abs_nonneg _)
  have hpos : 0 < (ν.prod ν).real S := by
    rw [Measure.real, hSmass]
    refine ENNReal.toReal_pos ?_ (by finiteness)
    exact mul_ne_zero (ne_of_gt ha) (ne_of_gt hbpos)
  simp only [smul_eq_mul, mul_one] at hlow
  linarith

/-! ### The lattice -/

/-- The joint law of the configuration and its resampling: independent across
sites, with the one-site joint law at each. -/
def resampleLaw (d : ℕ) (ν : Measure ℤ) (p : ℝ≥0∞) : Measure (Site d → ℤ × ℤ) :=
  LatticeProb.iidLaw d (resampleOne ν p)

variable {d : ℕ}

/-- The original configuration read off the coupled one is i.i.d. with law `ν`. -/
theorem resampleLaw_map_fst (ν : Measure ℤ) [IsProbabilityMeasure ν] {p : ℝ≥0∞} (hp : p ≤ 1) :
    (resampleLaw d ν p).map (fun c : Site d → ℤ × ℤ => fun i => (c i).1)
      = LatticeProb.iidLaw d ν := by
  haveI := resampleOne_isProbability ν hp
  rw [resampleLaw, LatticeProb.iidLaw_map_pi d (resampleOne ν p) measurable_fst,
    resampleOne_map_fst ν hp]

/-- **The resampled configuration has the law of the original.** -/
theorem resampleLaw_map_snd (ν : Measure ℤ) [IsProbabilityMeasure ν] {p : ℝ≥0∞} (hp : p ≤ 1) :
    (resampleLaw d ν p).map (fun c : Site d → ℤ × ℤ => fun i => (c i).2)
      = LatticeProb.iidLaw d ν := by
  haveI := resampleOne_isProbability ν hp
  rw [resampleLaw, LatticeProb.iidLaw_map_pi d (resampleOne ν p) measurable_snd,
    resampleOne_map_snd ν hp]

/-- One site of the coupled configuration carries the one-site joint law. -/
theorem resampleLaw_map_eval (ν : Measure ℤ) [IsProbabilityMeasure ν] {p : ℝ≥0∞} (hp : p ≤ 1)
    (x : Site d) :
    (resampleLaw d ν p).map (fun c : Site d → ℤ × ℤ => c x) = resampleOne ν p := by
  haveI := resampleOne_isProbability ν hp
  rw [resampleLaw, LatticeProb.iidLaw]
  exact Measure.infinitePi_map_eval _ x

end Parking

end
