/-
The convex comparison of `Parking/Support/UFinite.lean` extended from the odometer to
every convex nondecreasing Lipschitz function of it, and in particular to the hinges
`t ↦ (t - c)⁺`.

Step 1 of `lem:mean-horizon` (`parking.tex:2780-2800`) needs the `r`-th moment of the
odometer, not its mean, and `η ↦ u η n x ^ r` is convex but not Lipschitz, so
`Parking.convex_lipschitz_integral_le_finite_pi` does not apply to it.  The hinges do
apply, and for a nonnegative quantity they carry the whole moment: for an integer
`k ≥ 2`,

    t ^ k = ∫_0^∞ k (k-1) c ^ (k-2) (t - c)⁺ dc    (t ≥ 0),

so a comparison of `∫ (u - c)⁺` at every level `c` integrates to a comparison of
`∫ u ^ k`.  The comparison at each level is `integral_hinge_u_iid_le`, the
representation of the moment is `lintegral_pow_u_iid_eq`, and the two combine in
`lintegral_pow_u_iid_le`, stated in `ℝ≥0∞` so that no integrability of the moment is
assumed, with the Bochner form `integral_pow_u_iid_le` alongside it.
-/
import Parking.Support.UFinite
import Parking.Support.ConvexOrder
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
open scoped NNReal
variable {d : ℕ}

theorem convexOn_hinge (c : ℝ) : ConvexOn ℝ Set.univ (fun t : ℝ => max (t - c) 0) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hc : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
  have h1 : a * x + b * y - c = a * (x - c) + b * (y - c) := by linarith [hc]
  rw [h1]
  refine max_le ?_ ?_
  · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
  · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))

theorem monotone_hinge (c : ℝ) : Monotone (fun t : ℝ => max (t - c) 0) :=
  fun _ _ h => max_le_max (by linarith) le_rfl

theorem lipschitzWith_hinge (c : ℝ) : LipschitzWith 1 (fun t : ℝ => max (t - c) 0) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  have h := abs_max_sub_max_le_abs (x - c) (y - c) 0
  simpa only [sub_sub_sub_cancel_right] using h

theorem convexOn_comp_of_monotone {ι : Type*} {F : (ι → ℝ) → ℝ}
    (hF : ConvexOn ℝ Set.univ F) {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ Set.univ Φ) (hmono : Monotone Φ) :
    ConvexOn ℝ Set.univ (fun x => Φ (F x)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have h1 : F (a • x + b • y) ≤ a * F x + b * F y := by
    have h := hF.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    simpa only [smul_eq_mul] using h
  have h2 : Φ (a * F x + b * F y) ≤ a * Φ (F x) + b * Φ (F y) := by
    have h := hΦ.2 (Set.mem_univ (F x)) (Set.mem_univ (F y)) ha hb hab
    simpa only [smul_eq_mul] using h
  calc Φ (F (a • x + b • y)) ≤ Φ (a * F x + b * F y) := hmono h1
    _ ≤ a * Φ (F x) + b * Φ (F y) := h2
    _ = a • Φ (F x) + b • Φ (F y) := by simp only [smul_eq_mul]

/-- The integral of a function of the odometer over its finite set of input sites. -/
theorem integral_comp_u_iid_eq_pi (hd : 1 ≤ d) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {Φ : ℝ → ℝ} {L : ℝ≥0} (hΦL : LipschitzWith L Φ) (n : ℕ) (x : Site d) :
    ∫ η, Φ (u η n x) ∂(iidLaw d μ) =
      ∫ η : (boxFinset x n) → ℝ, Φ (u (extendField (boxFinset x n) η) n x)
        ∂(Measure.pi (fun _ => μ)) := by
  have hm : Measurable ((boxFinset x n).restrict : (Site d → ℝ) → ((boxFinset x n) → ℝ)) :=
    measurable_pi_lambda _ fun y => measurable_pi_apply (y : Site d)
  have hF : Measurable fun η : (boxFinset x n) → ℝ => Φ (u (extendField (boxFinset x n) η) n x) :=
    (hΦL.comp (lipschitzWith_u_extendField hd (boxFinset x n) n x)).continuous.measurable
  rw [← iidLaw_map_restrict d μ (boxFinset x n),
    integral_map hm.aemeasurable hF.aestronglyMeasurable]
  refine integral_congr_ae (ae_of_all _ fun η => ?_)
  show Φ (u η n x) = Φ (u (extendField (boxFinset x n) ((boxFinset x n).restrict η)) n x)
  rw [u_extendField_restrict η n x]

/-- **The one-site convex comparison bounds every convex nondecreasing Lipschitz
function of the odometer.**  This is `Parking.integral_u_iid_le` with `u` replaced by
`Φ ∘ u`; the composite is convex because `Φ` is convex and nondecreasing and `u` is
convex in the field, and Lipschitz because both factors are. -/
theorem integral_comp_u_iid_le (hd : 1 ≤ d) {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (id : ℝ → ℝ) μ) (hν : Integrable (id : ℝ → ℝ) ν)
    (hcomp : ∀ (f : ℝ → ℝ) (K : ℝ≥0), ConvexOn ℝ Set.univ f → LipschitzWith K f →
      ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν)
    {Φ : ℝ → ℝ} {L : ℝ≥0} (hΦconv : ConvexOn ℝ Set.univ Φ) (hΦmono : Monotone Φ)
    (hΦL : LipschitzWith L Φ) (n : ℕ) (x : Site d) :
    ∫ η, Φ (u η n x) ∂(iidLaw d μ) ≤ ∫ η, Φ (u η n x) ∂(iidLaw d ν) := by
  rw [integral_comp_u_iid_eq_pi hd μ hΦL, integral_comp_u_iid_eq_pi hd ν hΦL]
  exact convex_lipschitz_integral_le_finite_pi hμ hν hcomp
    (convexOn_comp_of_monotone (convexOn_u_extendField hd _ n x) hΦconv hΦmono)
    (hΦL.comp (lipschitzWith_u_extendField hd _ n x))

/-- **The hinge comparison for the odometer.**  For every level `c`, the expected
overshoot of the odometer above `c` is larger under the dominating one-site law. -/
theorem integral_hinge_u_iid_le (hd : 1 ≤ d) {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (id : ℝ → ℝ) μ) (hν : Integrable (id : ℝ → ℝ) ν)
    (hcomp : ∀ (f : ℝ → ℝ) (K : ℝ≥0), ConvexOn ℝ Set.univ f → LipschitzWith K f →
      ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν) (c : ℝ) (n : ℕ) (x : Site d) :
    ∫ η, max (u η n x - c) 0 ∂(iidLaw d μ) ≤ ∫ η, max (u η n x - c) 0 ∂(iidLaw d ν) :=
  integral_comp_u_iid_le hd hμ hν hcomp (convexOn_hinge c) (monotone_hinge c)
    (lipschitzWith_hinge c) n x

/-! ### The hinge representation of a power -/

theorem intervalIntegral_hinge_pow (m : ℕ) (t : ℝ) :
    ∫ c in (0:ℝ)..t, (((m : ℝ) + 2) * ((m : ℝ) + 1) * c ^ m) * (t - c) = t ^ (m + 2) := by
  have hc1 : IntervalIntegrable (fun c : ℝ => ((m : ℝ) + 2) * ((m : ℝ) + 1) * t * c ^ m)
      MeasureTheory.volume 0 t := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hc2 : IntervalIntegrable (fun c : ℝ => ((m : ℝ) + 2) * ((m : ℝ) + 1) * c ^ (m + 1))
      MeasureTheory.volume 0 t := (by fun_prop : Continuous _).intervalIntegrable _ _
  have h1 : ∫ c in (0:ℝ)..t, c ^ m = t ^ (m + 1) / ((m : ℝ) + 1) := by
    rw [integral_pow]
    simp
  have h2 : ∫ c in (0:ℝ)..t, c ^ (m + 1) = t ^ (m + 2) / ((m : ℝ) + 2) := by
    rw [integral_pow]
    push_cast
    ring_nf
  have hexp : ∀ c : ℝ, (((m : ℝ) + 2) * ((m : ℝ) + 1) * c ^ m) * (t - c)
      = ((m : ℝ) + 2) * ((m : ℝ) + 1) * t * c ^ m
        - ((m : ℝ) + 2) * ((m : ℝ) + 1) * c ^ (m + 1) := by
    intro c
    ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_sub hc1 hc2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, h1, h2]
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
  field_simp
  ring


theorem setIntegral_hinge_pow (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ c in Set.Ioi (0:ℝ), (((m : ℝ) + 2) * ((m : ℝ) + 1) * c ^ m) * max (t - c) 0
      = t ^ (m + 2) := by
  have hzero : ∀ᵐ c ∂(MeasureTheory.volume : Measure ℝ),
      c ∈ Set.Ioi (0:ℝ) \ Set.Ioc (0:ℝ) t →
        (((m : ℝ) + 2) * ((m : ℝ) + 1) * c ^ m) * max (t - c) 0 = 0 := by
    filter_upwards with c hc
    have hct : t < c := by
      rcases hc with ⟨hc0, hc1⟩
      by_contra hcon
      exact hc1 ⟨hc0, not_lt.mp hcon⟩
    rw [max_eq_right (by linarith), mul_zero]
  rw [MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
      measurableSet_Ioi.nullMeasurableSet Set.Ioc_subset_Ioi_self hzero,
    ← intervalIntegral.integral_of_le ht]
  rw [intervalIntegral.integral_congr (g := fun c : ℝ =>
      (((m : ℝ) + 2) * ((m : ℝ) + 1) * c ^ m) * (t - c)) ?_]
  · exact intervalIntegral_hinge_pow m t
  · intro c hc
    rw [Set.uIcc_of_le ht] at hc
    have hc2 : c ≤ t := hc.2
    show ((m : ℝ) + 2) * ((m : ℝ) + 1) * c ^ m * max (t - c) 0
        = ((m : ℝ) + 2) * ((m : ℝ) + 1) * c ^ m * (t - c)
    rw [max_eq_left (by linarith)]

/-! ### The moment comparison -/

theorem integrableOn_hinge_weight (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun c : ℝ => (((m : ℝ) + 2) * ((m : ℝ) + 1) * c ^ m) * max (t - c) 0)
      (Set.Ioi (0:ℝ)) := by
  have hcont : Continuous fun c : ℝ =>
      (((m : ℝ) + 2) * ((m : ℝ) + 1) * c ^ m) * max (t - c) 0 := by fun_prop
  have h1 : IntegrableOn (fun c : ℝ => (((m : ℝ) + 2) * ((m : ℝ) + 1) * c ^ m) * max (t - c) 0)
      (Set.Ioc (0:ℝ) t) := hcont.integrableOn_Ioc
  have h2 : IntegrableOn (fun c : ℝ => (((m : ℝ) + 2) * ((m : ℝ) + 1) * c ^ m) * max (t - c) 0)
      (Set.Ioi t) := by
    refine (integrable_zero ℝ ℝ _).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with c hc
    have hct : t < c := hc
    rw [max_eq_right (by linarith), mul_zero]
    rfl
  rw [← Set.Ioc_union_Ioi_eq_Ioi ht]
  exact h1.union h2

theorem hinge_weight_nonneg (m : ℕ) {c t : ℝ} (hc : 0 ≤ c) :
    0 ≤ (((m : ℝ) + 2) * ((m : ℝ) + 1) * c ^ m) * max (t - c) 0 := by
  have h1 : 0 ≤ ((m : ℝ) + 2) * ((m : ℝ) + 1) * c ^ m := by positivity
  exact mul_nonneg h1 (le_max_right _ _)


theorem u_nonneg {d : ℕ} (η : Site d → ℝ) (n : ℕ) (x : Site d) : 0 ≤ u η n x := by
  cases n with
  | zero => exact le_refl 0
  | succ n => exact le_max_left 0 _

theorem integrable_hinge_u_iid {d : ℕ} (hd : 1 ≤ d) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (id : ℝ → ℝ) μ) (c : ℝ) (n : ℕ) (x : Site d) :
    Integrable (fun η => max (u η n x - c) 0) (LatticeProb.iidLaw d μ) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d μ) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : Site d => μ))
  have hu := integrable_u_iid hd μ hμ n x
  refine (hu.abs.add (integrable_const |c|)).mono' ?_
    (Filter.Eventually.of_forall fun η => ?_)
  · exact (lipschitzWith_hinge c).continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    rcases le_or_gt (u η n x - c) 0 with h | h
    · rw [max_eq_right h]
      exact add_nonneg (abs_nonneg _) (abs_nonneg _)
    · rw [max_eq_left h.le]
      have h1 : u η n x - c ≤ |u η n x| + |c| := by
        have := le_abs_self (u η n x)
        have := neg_abs_le c
        linarith
      exact h1


/-- **The `(m+2)`-th moment of the odometer as an integral of its hinges.** -/
theorem lintegral_pow_u_iid_eq {d : ℕ} (hd : 1 ≤ d) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (id : ℝ → ℝ) μ) (m n : ℕ) (x : Site d) :
    ∫⁻ η, ENNReal.ofReal (u η n x ^ (m + 2)) ∂(LatticeProb.iidLaw d μ)
      = ∫⁻ c in Set.Ioi (0:ℝ),
          ENNReal.ofReal (((m : ℝ) + 2) * ((m : ℝ) + 1) * c ^ m)
            * ENNReal.ofReal (∫ η, max (u η n x - c) 0 ∂(LatticeProb.iidLaw d μ)) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d μ) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : Site d => μ))
  have hmu : Measurable fun η : Site d → ℝ => u η n x := measurable_u_eval n x
  have hjoint : Measurable fun p : (Site d → ℝ) × ℝ =>
      ENNReal.ofReal ((((m : ℝ) + 2) * ((m : ℝ) + 1) * p.2 ^ m) * max (u p.1 n x - p.2) 0) := by
    refine ENNReal.measurable_ofReal.comp (Measurable.mul ?_ ?_)
    · have h2 : Measurable fun p : (Site d → ℝ) × ℝ => p.2 := measurable_snd
      have h3 : Measurable fun p : (Site d → ℝ) × ℝ =>
          (((m : ℝ) + 2) * ((m : ℝ) + 1)) * p.2 ^ m := (h2.pow_const m).const_mul _
      exact h3
    · exact ((hmu.comp measurable_fst).sub measurable_snd).max measurable_const
  have hstep1 : ∀ η : Site d → ℝ,
      ENNReal.ofReal (u η n x ^ (m + 2))
        = ∫⁻ c in Set.Ioi (0:ℝ),
            ENNReal.ofReal ((((m : ℝ) + 2) * ((m : ℝ) + 1) * c ^ m) * max (u η n x - c) 0) := by
    intro η
    rw [← setIntegral_hinge_pow m (u_nonneg η n x),
      ofReal_integral_eq_lintegral_ofReal (integrableOn_hinge_weight m (u_nonneg η n x))]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with c hc
    exact hinge_weight_nonneg m (le_of_lt hc)
  simp_rw [hstep1]
  rw [lintegral_lintegral_swap hjoint.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun c hc => ?_)
  have hc0 : (0:ℝ) ≤ c := le_of_lt hc
  have hw0 : (0:ℝ) ≤ ((m : ℝ) + 2) * ((m : ℝ) + 1) * c ^ m := by positivity
  have hsplit : ∀ η : Site d → ℝ,
      ENNReal.ofReal ((((m : ℝ) + 2) * ((m : ℝ) + 1) * c ^ m) * max (u η n x - c) 0)
        = ENNReal.ofReal (((m : ℝ) + 2) * ((m : ℝ) + 1) * c ^ m)
            * ENNReal.ofReal (max (u η n x - c) 0) := fun η => ENNReal.ofReal_mul hw0
  simp_rw [hsplit]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ofReal_integral_eq_lintegral_ofReal (integrable_hinge_u_iid hd μ hμ c n x)
      (Filter.Eventually.of_forall fun η => le_max_right _ _)]


/-- **The one-site convex comparison bounds every moment of the odometer.**  The moment
is not a Lipschitz function of the field, so the comparison is applied at each hinge and
integrated over the level. -/
theorem lintegral_pow_u_iid_le {d : ℕ} (hd : 1 ≤ d) {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (id : ℝ → ℝ) μ) (hν : Integrable (id : ℝ → ℝ) ν)
    (hcomp : ∀ (f : ℝ → ℝ) (K : ℝ≥0), ConvexOn ℝ Set.univ f → LipschitzWith K f →
      ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν) (m n : ℕ) (x : Site d) :
    ∫⁻ η, ENNReal.ofReal (u η n x ^ (m + 2)) ∂(LatticeProb.iidLaw d μ)
      ≤ ∫⁻ η, ENNReal.ofReal (u η n x ^ (m + 2)) ∂(LatticeProb.iidLaw d ν) := by
  rw [lintegral_pow_u_iid_eq hd μ hμ m n x, lintegral_pow_u_iid_eq hd ν hν m n x]
  refine lintegral_mono fun c => ?_
  have hle := ENNReal.ofReal_le_ofReal (integral_hinge_u_iid_le hd hμ hν hcomp c n x)
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- The Bochner form of the moment comparison, when the dominating side is integrable. -/
theorem integral_pow_u_iid_le {d : ℕ} (hd : 1 ≤ d) {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (id : ℝ → ℝ) μ) (hν : Integrable (id : ℝ → ℝ) ν)
    (hcomp : ∀ (f : ℝ → ℝ) (K : ℝ≥0), ConvexOn ℝ Set.univ f → LipschitzWith K f →
      ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν) (m n : ℕ) (x : Site d)
    (hIν : Integrable (fun η => u η n x ^ (m + 2)) (LatticeProb.iidLaw d ν)) :
    ∫ η, u η n x ^ (m + 2) ∂(LatticeProb.iidLaw d μ)
      ≤ ∫ η, u η n x ^ (m + 2) ∂(LatticeProb.iidLaw d ν) := by
  have hnn : ∀ η : Site d → ℝ, 0 ≤ u η n x ^ (m + 2) := fun η => pow_nonneg (u_nonneg η n x) _
  have hmeas : Measurable fun η : Site d → ℝ => u η n x ^ (m + 2) :=
    (measurable_u_eval n x).pow_const _
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
      hmeas.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
      hmeas.aestronglyMeasurable]
  exact ENNReal.toReal_mono (MeasureTheory.Integrable.lintegral_lt_top hIν).ne
    (lintegral_pow_u_iid_le hd hμ hν hcomp m n x)

end Parking

end
