/-
The tilted product law on finitely many sites has the exponential density.

Step 3 of `lem:product` (`parking.tex:2409-2412`) reads "the tilted law has
density proportional to `∏ e^{λ η(x_i)}` on these coordinates".  On the whole
lattice the tilted and untilted i.i.d. laws are mutually singular, so the
density is an identity of integrals of observables of the tilted sites alone:
for such an observable `G`,

  `(∫ e^{sk} dν)^{|N|} ∫ G d(iidLaw (tiltLaw ν s)) = ∫ G(a) e^{s ∑_{x ∈ N} a x} d(iidLaw ν)`.

It is proved by revealing one count at a time, the untilted reveal on the right
and the tilted reveal on the left, with `Parking.integral_tiltLaw` turning the
one-site tilted integral into a normalized weighted integral.  The
integrability needed to reveal a count propagates through the induction by
Fubini, which is why the two integrability hypotheses are carried rather than a
bound: the observables the derivative needs are unbounded.

`prod_coords` is the accompanying product rule for the i.i.d. law: a product of
one-site functions is integrable with the product of the one-site integrals.
It supplies the exponential moment of `∑_{x ∈ N} η(x)`.
-/
import Parking.Support.CountFiltration
import Parking.Support.Tilt
import Parking.Support.ProductFactor

open MeasureTheory

noncomputable section

namespace Parking

/-- Revealing one coordinate of a product law, for an integrable observable.
This is `Parking.integral_coordinate_sections` with the bound replaced by
integrability. -/
theorem integral_coordinate_sections_int {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [DecidableEq ι] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Π i, X i) → ℝ) (hf : Measurable f) (hi : Integrable f (Measure.infinitePi μ))
    (j : ι) :
    (∫ ω, f ω ∂(Measure.infinitePi μ)) =
      ∫ ω, ∫ a, f (Function.update ω j a) ∂(μ j) ∂(Measure.infinitePi μ) := by
  let P := Measure.infinitePi μ
  let T : (Π i, X i) × X j → Π i, X i := fun q => Function.update q.1 j q.2
  have hT : MeasurePreserving T (P.prod (μ j)) P :=
    LatticeProb.measurePreserving_update_infinitePi μ j
  have hcomp : Integrable (fun q => f (T q)) (P.prod (μ j)) := hT.integrable_comp_of_integrable hi
  have he := integral_map (μ := P.prod (μ j)) (φ := T) (f := f) hT.measurable.aemeasurable
    (by rw [hT.map_eq]; exact hf.aestronglyMeasurable)
  rw [hT.map_eq] at he
  exact he.trans (integral_prod _ hcomp)

/-- Revealing one count of the i.i.d. field, for an integrable observable. -/
theorem integral_reveal_int {d : ℕ} {μ : Measure ℤ} [IsProbabilityMeasure μ]
    {G : (Site d → ℤ) → ℝ} (hGm : Measurable G) (hGi : Integrable G (LatticeProb.iidLaw d μ))
    (x₀ : Site d) :
    ∫ a, G a ∂(LatticeProb.iidLaw d μ)
      = ∫ a, (∫ k, G (Function.update a x₀ k) ∂μ) ∂(LatticeProb.iidLaw d μ) :=
  integral_coordinate_sections_int (fun _ : Site d => μ) G hGm hGi x₀

/-- Updating the count at a site outside `N` splits a sum over `insert x₀ N`. -/
theorem sum_update_insert {d : ℕ} (x₀ : Site d) (N : Finset (Site d)) (hx : x₀ ∉ N)
    (a : Site d → ℤ) (k : ℤ) :
    ∑ x ∈ insert x₀ N, (((Function.update a x₀ k) x : ℤ) : ℝ)
      = (k : ℝ) + ∑ x ∈ N, ((a x : ℤ) : ℝ) := by
  rw [Finset.sum_insert hx, Function.update_self]
  congr 1
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [Function.update_of_ne (by rintro rfl; exact hx hy)]

/-- The same for a product of one-site functions. -/
theorem prod_update_insert {d : ℕ} (w : Site d → ℤ → ℝ) (x₀ : Site d)
    (N : Finset (Site d)) (hx : x₀ ∉ N) (a : Site d → ℤ) (k : ℤ) :
    ∏ y ∈ insert x₀ N, w y (Function.update a x₀ k y)
      = w x₀ k * ∏ y ∈ N, w y (a y) := by
  rw [Finset.prod_insert hx, Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun y hy => ?_
  rw [Function.update_of_ne (by rintro rfl; exact hx hy)]

theorem measurable_prod_coords {d : ℕ} (w : Site d → ℤ → ℝ) (N : Finset (Site d)) :
    Measurable (fun a : Site d → ℤ => ∏ y ∈ N, w y (a y)) :=
  Finset.measurable_prod _ fun y _ =>
    (measurable_int_fun (w y)).comp (measurable_pi_apply y)

/-- **The product rule for the i.i.d. law.**  A product of one-site functions
over a finite set of sites is integrable and its mean is the product of the
one-site means. -/
theorem prod_coords {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (w : Site d → ℤ → ℝ) (hwi : ∀ y, Integrable (w y) ν) (N : Finset (Site d)) :
    Integrable (fun a : Site d → ℤ => ∏ y ∈ N, w y (a y)) (LatticeProb.iidLaw d ν)
    ∧ ∫ a, ∏ y ∈ N, w y (a y) ∂(LatticeProb.iidLaw d ν) = ∏ y ∈ N, ∫ k, w y k ∂ν := by
  classical
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  induction N using Finset.induction_on with
  | empty => simp
  | @insert x₀ N hx ih =>
      obtain ⟨ihI, ihV⟩ := ih
      have hu : MeasurePreserving (fun q : (Site d → ℤ) × ℤ => Function.update q.1 x₀ q.2)
          ((LatticeProb.iidLaw d ν).prod ν) (LatticeProb.iidLaw d ν) :=
        LatticeProb.measurePreserving_update_infinitePi (fun _ : Site d => ν) x₀
      have hcomp : (fun q : (Site d → ℤ) × ℤ =>
            ∏ y ∈ insert x₀ N, w y (Function.update q.1 x₀ q.2 y))
          = fun q : (Site d → ℤ) × ℤ => (∏ y ∈ N, w y (q.1 y)) * w x₀ q.2 := by
        funext q
        rw [prod_update_insert w x₀ N hx q.1 q.2]
        ring
      have hprodint : Integrable
          (fun q : (Site d → ℤ) × ℤ => (∏ y ∈ N, w y (q.1 y)) * w x₀ q.2)
          ((LatticeProb.iidLaw d ν).prod ν) := ihI.mul_prod (hwi x₀)
      have hmeas : Measurable (fun a : Site d → ℤ => ∏ y ∈ insert x₀ N, w y (a y)) :=
        measurable_prod_coords w (insert x₀ N)
      have hI : Integrable (fun a : Site d → ℤ => ∏ y ∈ insert x₀ N, w y (a y))
          (LatticeProb.iidLaw d ν) := by
        refine (hu.integrable_comp hmeas.aestronglyMeasurable).mp ?_
        show Integrable (fun q : (Site d → ℤ) × ℤ =>
          ∏ y ∈ insert x₀ N, w y (Function.update q.1 x₀ q.2 y)) _
        rw [hcomp]
        exact hprodint
      refine ⟨hI, ?_⟩
      have he := integral_map (μ := (LatticeProb.iidLaw d ν).prod ν)
        (φ := fun q : (Site d → ℤ) × ℤ => Function.update q.1 x₀ q.2)
        (f := fun a : Site d → ℤ => ∏ y ∈ insert x₀ N, w y (a y))
        hu.measurable.aemeasurable (by rw [hu.map_eq]; exact hmeas.aestronglyMeasurable)
      rw [hu.map_eq] at he
      rw [he]
      show ∫ q : (Site d → ℤ) × ℤ,
          ∏ y ∈ insert x₀ N, w y (Function.update q.1 x₀ q.2 y)
          ∂((LatticeProb.iidLaw d ν).prod ν) = _
      rw [hcomp, integral_prod_mul (fun a : Site d → ℤ => ∏ y ∈ N, w y (a y)) (w x₀), ihV,
        Finset.prod_insert hx]
      ring

/-- **The tilted product law has the exponential density on the tilted sites.**
This is the density of `parking.tex:2409-2412`, in the form of an identity of
integrals of observables of the counts at the tilted sites. -/
theorem integral_iidLaw_tilt {d : ℕ} {ν : Measure ℤ} [IsProbabilityMeasure ν] {s : ℝ}
    (hexps : Integrable (fun k : ℤ => Real.exp (s * k)) ν) (N : Finset (Site d)) :
    ∀ {G : (Site d → ℤ) → ℝ}, Measurable G → DependsOnCounts N G →
      Integrable G (LatticeProb.iidLaw d (tiltLaw ν s)) →
      Integrable (fun a => G a * Real.exp (s * ∑ x ∈ N, ((a x : ℤ) : ℝ)))
        (LatticeProb.iidLaw d ν) →
      (∫ k, Real.exp (s * k) ∂ν) ^ N.card * ∫ a, G a ∂(LatticeProb.iidLaw d (tiltLaw ν s))
        = ∫ a, G a * Real.exp (s * ∑ x ∈ N, ((a x : ℤ) : ℝ)) ∂(LatticeProb.iidLaw d ν) := by
  classical
  have hZpos : 0 < ∫ k, Real.exp (s * k) ∂ν := integral_exp_pos hexps
  have hZne : (∫ k, Real.exp (s * k) ∂ν) ≠ 0 := ne_of_gt hZpos
  haveI := tiltLaw_isProbability hexps
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d (tiltLaw ν s)) := by
    unfold LatticeProb.iidLaw; infer_instance
  induction N using Finset.induction_on with
  | empty =>
      intro G hGm hGN hGi hGi'
      have hconst : ∀ a : Site d → ℤ, G a = G (fun _ => (0 : ℤ)) := fun a =>
        hGN a (fun _ => (0 : ℤ)) (by simp)
      simp only [Finset.card_empty, pow_zero, one_mul, Finset.sum_empty, mul_zero,
        Real.exp_zero, mul_one]
      rw [integral_congr_ae (Filter.Eventually.of_forall hconst),
        integral_congr_ae (Filter.Eventually.of_forall hconst)]
      simp
  | @insert x₀ N hx ih =>
      intro G hGm hGN hGi hGi'
      have hmsum : ∀ M : Finset (Site d),
          Measurable (fun a : Site d → ℤ => ∑ x ∈ M, ((a x : ℤ) : ℝ)) := fun M =>
        Finset.measurable_sum _ fun y _ =>
          (measurable_int_fun (fun k : ℤ => (k : ℝ))).comp (measurable_pi_apply y)
      have hmexp : ∀ M : Finset (Site d),
          Measurable (fun a : Site d → ℤ => Real.exp (s * ∑ x ∈ M, ((a x : ℤ) : ℝ))) := fun M =>
        Real.measurable_exp.comp (measurable_const.mul (hmsum M))
      set H : (Site d → ℤ) → ℝ := avgAt (tiltLaw ν s) x₀ G with hHdef
      have h1 : ∀ a : Site d → ℤ,
          H a = (∫ k, Real.exp (s * k) ∂ν)⁻¹ *
            ∫ k, Real.exp (s * k) * G (Function.update a x₀ k) ∂ν := by
        intro a
        rw [hHdef]
        exact integral_tiltLaw s _ hexps
      have hHm : Measurable H := measurable_avgAt hGm x₀
      have hHN : DependsOnCounts N H := avgAt_dependsOnCounts hGN
      have huT : MeasurePreserving (fun q : (Site d → ℤ) × ℤ => Function.update q.1 x₀ q.2)
          ((LatticeProb.iidLaw d (tiltLaw ν s)).prod (tiltLaw ν s))
          (LatticeProb.iidLaw d (tiltLaw ν s)) :=
        LatticeProb.measurePreserving_update_infinitePi (fun _ : Site d => tiltLaw ν s) x₀
      have hu0 : MeasurePreserving (fun q : (Site d → ℤ) × ℤ => Function.update q.1 x₀ q.2)
          ((LatticeProb.iidLaw d ν).prod ν) (LatticeProb.iidLaw d ν) :=
        LatticeProb.measurePreserving_update_infinitePi (fun _ : Site d => ν) x₀
      have hHi : Integrable H (LatticeProb.iidLaw d (tiltLaw ν s)) :=
        (huT.integrable_comp_of_integrable hGi).integral_prod_left
      have hkey : ∀ a : Site d → ℤ,
          (∫ k, G (Function.update a x₀ k) *
            Real.exp (s * ∑ x ∈ insert x₀ N, (((Function.update a x₀ k) x : ℤ) : ℝ)) ∂ν)
          = ((∫ k, Real.exp (s * k) ∂ν) * H a) *
              Real.exp (s * ∑ x ∈ N, ((a x : ℤ) : ℝ)) := by
        intro a
        have hin : ∀ k : ℤ, G (Function.update a x₀ k) *
            Real.exp (s * ∑ x ∈ insert x₀ N, (((Function.update a x₀ k) x : ℤ) : ℝ))
            = (Real.exp (s * k) * G (Function.update a x₀ k)) *
              Real.exp (s * ∑ x ∈ N, ((a x : ℤ) : ℝ)) := by
          intro k
          rw [sum_update_insert x₀ N hx a k, mul_add, Real.exp_add]
          ring
        rw [integral_congr_ae (Filter.Eventually.of_forall hin), integral_mul_const, h1 a]
        field_simp
      have hHi' : Integrable
          (fun a => H a * Real.exp (s * ∑ x ∈ N, ((a x : ℤ) : ℝ))) (LatticeProb.iidLaw d ν) := by
        have hc := (hu0.integrable_comp_of_integrable hGi').integral_prod_left
        have hc2 : Integrable (fun a => ((∫ k, Real.exp (s * k) ∂ν) * H a) *
            Real.exp (s * ∑ x ∈ N, ((a x : ℤ) : ℝ))) (LatticeProb.iidLaw d ν) :=
          hc.congr (Filter.Eventually.of_forall hkey)
        have hc3 := hc2.const_mul (∫ k, Real.exp (s * k) ∂ν)⁻¹
        refine hc3.congr (Filter.Eventually.of_forall fun a => ?_)
        field_simp
      have hIH := ih hHm hHN hHi hHi'
      have hrevealT : ∫ a, G a ∂(LatticeProb.iidLaw d (tiltLaw ν s))
          = ∫ a, H a ∂(LatticeProb.iidLaw d (tiltLaw ν s)) :=
        integral_reveal_int hGm hGi x₀
      have hreveal0 : ∫ a, G a * Real.exp (s * ∑ x ∈ insert x₀ N, ((a x : ℤ) : ℝ))
            ∂(LatticeProb.iidLaw d ν)
          = ∫ a, (∫ k, G (Function.update a x₀ k) *
              Real.exp (s * ∑ x ∈ insert x₀ N, (((Function.update a x₀ k) x : ℤ) : ℝ)) ∂ν)
            ∂(LatticeProb.iidLaw d ν) :=
        integral_reveal_int (hGm.mul (hmexp (insert x₀ N))) hGi' x₀
      rw [Finset.card_insert_of_notMem hx, hrevealT, hreveal0,
        integral_congr_ae (Filter.Eventually.of_forall hkey)]
      have hpull : ∫ a, ((∫ k, Real.exp (s * k) ∂ν) * H a) *
            Real.exp (s * ∑ x ∈ N, ((a x : ℤ) : ℝ)) ∂(LatticeProb.iidLaw d ν)
          = (∫ k, Real.exp (s * k) ∂ν) *
            ∫ a, H a * Real.exp (s * ∑ x ∈ N, ((a x : ℤ) : ℝ)) ∂(LatticeProb.iidLaw d ν) := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun a => by ring)
      rw [hpull, ← hIH, pow_succ]
      ring

end Parking

end
