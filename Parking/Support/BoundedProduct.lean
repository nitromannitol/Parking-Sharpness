import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory
variable {X : Type*} [MeasurableSpace X]

/-- Consing a coordinate onto a finite tuple is measurable. -/
theorem measurable_cons_tuple {n : ℕ} :
    Measurable (fun p : X × (Fin n → X) => (Fin.cons p.1 p.2 : Fin (n + 1) → X)) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_fst
  · exact (measurable_pi_apply j).comp measurable_snd

/-- The integral over a finite product with its first coordinate split off. -/
theorem integral_pi_cons_tuple (μ : Measure X) [IsProbabilityMeasure μ] {n : ℕ}
    (f : (Fin (n + 1) → X) → ℝ) (hf : Integrable f (Measure.pi (fun _ => μ))) :
    ∫ w, f w ∂(Measure.pi (fun _ : Fin (n + 1) => μ)) =
      ∫ a, ∫ w, f (Fin.cons a w) ∂(Measure.pi (fun _ : Fin n => μ)) ∂μ := by
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
  have hprod : Integrable (fun z : X × (Fin n → X) => f (Fin.cons z.1 z.2))
      (μ.prod (Measure.pi (fun _ : Fin n => μ))) := by
    simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq, Function.comp_def]
      using he.integrable_comp_of_integrable hf
  calc
    _ = ∫ z : X × (Fin n → X), f (Fin.cons z.1 z.2)
        ∂(μ.prod (Measure.pi (fun _ : Fin n => μ))) := by
      rw [← he.integral_comp']
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq]
    _ = _ := integral_prod _ hprod

/-- Every centered bounded observable has an integrable exponential. -/
theorem integrable_exp_centered_bounded {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀ ω, |f ω| ≤ B) (t m : ℝ) :
    Integrable (fun ω => Real.exp (t * (f ω - m))) μ := by
  apply integrable_exp_mul_of_mem_Icc (a := -B - m) (b := B - m) (hf.sub_const m).aemeasurable
  exact ae_of_all _ fun ω => ⟨by linarith [(abs_le.mp (hB ω)).1], by linarith [(abs_le.mp (hB ω)).2]⟩

/-- Bounded coordinate oscillations give a Gaussian moment-generating bound on a finite product. -/
theorem mgf_bounded_differences (μ : Measure X) [IsProbabilityMeasure μ]
    (n : ℕ) (f : (Fin n → X) → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀ ω, |f ω| ≤ B) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hosc : ∀ ω i a, |f ω - f (Function.update ω i a)| ≤ c i) (t : ℝ) :
    ∫ ω, Real.exp (t * (f ω - ∫ w, f w ∂(Measure.pi (fun _ : Fin n => μ))))
      ∂(Measure.pi (fun _ : Fin n => μ)) ≤ Real.exp ((∑ i, c i ^ 2) * t ^ 2 / 2) := by
  classical
  haveI : Nonempty X := nonempty_of_isProbabilityMeasure μ
  induction n with
  | zero =>
      have he : f = fun _ => f (fun i => Fin.elim0 i) :=
        funext fun ω => congrArg f (Subsingleton.elim _ _)
      rw [he]
      simp
  | succ n ih =>
      let P := Measure.pi (fun _ : Fin n => μ)
      let F : X → ℝ := fun a => ∫ w, f (Fin.cons a w) ∂P
      let m := ∫ w, f w ∂(Measure.pi (fun _ : Fin (n + 1) => μ))
      have hfm : Measurable (fun q : X × (Fin n → X) => f (Fin.cons q.1 q.2)) := hf.comp measurable_cons_tuple
      have hFi (a : X) : Integrable (fun w : Fin n → X => f (Fin.cons a w)) P :=
        Integrable.of_bound (hfm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable B
          (ae_of_all _ fun w => by simpa only [Real.norm_eq_abs] using hB (Fin.cons a w))
      have hFm : Measurable F := hfm.stronglyMeasurable.integral_prod_right'.measurable
      have hFB (a : X) : |F a| ≤ B := by
        have h := norm_integral_le_of_norm_le_const (μ := P) (f := fun w : Fin n → X => f (Fin.cons a w))
          (ae_of_all _ fun w => by simpa only [Real.norm_eq_abs] using hB (Fin.cons a w))
        simpa only [F, probReal_univ, mul_one, Real.norm_eq_abs] using h
      have hfi : Integrable f (Measure.pi (fun _ : Fin (n + 1) => μ)) :=
        Integrable.of_bound hf.aestronglyMeasurable B
          (ae_of_all _ fun w => by simpa only [Real.norm_eq_abs] using hB w)
      have hm : m = ∫ a, F a ∂μ := integral_pi_cons_tuple μ f hfi
      have hFc (a b : X) : |F a - F b| ≤ c 0 := by
        change |(∫ w, f (Fin.cons a w) ∂P) - ∫ w, f (Fin.cons b w) ∂P| ≤ _
        rw [← integral_sub (hFi a) (hFi b)]
        have hb (w : Fin n → X) : |f (Fin.cons a w) - f (Fin.cons b w)| ≤ c 0 := by
          have he : Function.update (Fin.cons a w : Fin (n + 1) → X) 0 b = Fin.cons b w := by
            funext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          simpa only [he] using hosc (Fin.cons a w) 0 b
        have h := norm_integral_le_of_norm_le_const (μ := P)
          (f := fun w : Fin n → X => f (Fin.cons a w) - f (Fin.cons b w))
          (ae_of_all _ fun w => by simpa only [Real.norm_eq_abs] using hb w)
        simpa only [probReal_univ, mul_one, Real.norm_eq_abs] using h
      have htail (a : X) :
          (∫ w, Real.exp (t * (f (Fin.cons a w) - F a)) ∂P) ≤
            Real.exp ((∑ i : Fin n, c i.succ ^ 2) * t ^ 2 / 2) := by
        apply ih _ (hfm.comp (measurable_const.prodMk measurable_id))
          (fun w => hB (Fin.cons a w)) (fun i => c i.succ) (fun i => hc i.succ) ?_
        intro w i b
        change |f (Fin.cons a w) - f (Fin.cons a (Function.update w i b))| ≤ c i.succ
        have he : Function.update (Fin.cons a w : Fin (n + 1) → X) i.succ b = Fin.cons a (Function.update w i b) := by
          funext j
          refine Fin.cases ?_ (fun k => ?_) j
          · rw [Function.update_of_ne (Fin.succ_ne_zero i).symm]
            rfl
          · by_cases hki : k = i <;> simp [hki]
        simpa only [he] using hosc (Fin.cons a w) i.succ b
      let a₀ : X := Classical.arbitrary X
      have hsg := hasSubgaussianMGF_of_mem_Icc (μ := μ) hFm.aemeasurable
        (a := F a₀ - c 0) (b := F a₀ + c 0)
        (ae_of_all _ fun a => by obtain ⟨h1, h2⟩ := abs_le.mp (hFc a a₀); exact ⟨by linarith, by linarith⟩)
      have houter : ∫ a, Real.exp (t * (F a - m)) ∂μ ≤ Real.exp ((c 0) ^ 2 * t ^ 2 / 2) := by
        have h := hsg.mgf_le t
        have he : (F a₀ + c 0) - (F a₀ - c 0) = 2 * c 0 := by ring
        rw [he] at h
        simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm,
          Real.norm_eq_abs] at h
        rw [abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hc 0))] at h
        rw [show 2 * c 0 / 2 = c 0 by ring] at h
        simpa only [mgf, hm] using h
      have hei := integrable_exp_centered_bounded (Measure.pi (fun _ : Fin (n + 1) => μ)) f hf B hB t m
      have hpi : Integrable (fun q : X × (Fin n → X) => Real.exp (t * (f (Fin.cons q.1 q.2) - m)))
          (μ.prod P) := Integrable.of_bound
            ((hfm.sub_const m).const_mul t).exp.aestronglyMeasurable
            (Real.exp (|t| * (B + |m|))) (ae_of_all _ fun q => by
              rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
              apply Real.exp_le_exp.mpr
              calc t * (f (Fin.cons q.1 q.2) - m) ≤ |t| * |f (Fin.cons q.1 q.2) - m| := by
                    simpa only [abs_mul] using le_abs_self (t * (f (Fin.cons q.1 q.2) - m))
                _ ≤ |t| * (B + |m|) := mul_le_mul_of_nonneg_left
                    ((abs_sub _ _).trans (add_le_add (hB _) le_rfl)) (abs_nonneg _))
      rw [integral_pi_cons_tuple μ _ hei]
      calc
        _ ≤ ∫ a, Real.exp (t * (F a - m)) *
            Real.exp ((∑ i : Fin n, c i.succ ^ 2) * t ^ 2 / 2) ∂μ := by
          apply integral_mono hpi.integral_prod_left
            ((integrable_exp_centered_bounded μ F hFm B hFB t m).mul_const _)
          intro a
          dsimp only
          have he : (fun w => Real.exp (t * (f (Fin.cons a w) - m))) =
              fun w => Real.exp (t * (F a - m)) * Real.exp (t * (f (Fin.cons a w) - F a)) := by
            funext w
            rw [← Real.exp_add]
            congr 1
            ring
          rw [he, integral_const_mul]
          exact mul_le_mul_of_nonneg_left (htail a) (Real.exp_pos _).le
        _ = (∫ a, Real.exp (t * (F a - m)) ∂μ) *
            Real.exp ((∑ i : Fin n, c i.succ ^ 2) * t ^ 2 / 2) := integral_mul_const _ _
        _ ≤ Real.exp ((c 0) ^ 2 * t ^ 2 / 2) *
            Real.exp ((∑ i : Fin n, c i.succ ^ 2) * t ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right houter (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add, Fin.sum_univ_succ]; congr 1; ring
end Parking
