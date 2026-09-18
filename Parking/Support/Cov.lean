/-
The covariance of two functions of one coordinate, and Step 1 of the proof of
`lem:product` (`parking.tex:2359-2374`).

The paper's Step 1 is the coupling identity: if `Y₁` is an independent copy of
`Y`, then

    2 |Cov(f(Y), z(Y))| = |E (f(Y) - f(Y₁))(z(Y) - z(Y₁))|
                        ≤ E |f(Y) - f(Y₁)| |Y - Y₁| = 2 Cov(f(Y), Y),

where the inequality is the one-Lipschitz property of `z` and the last equality
is the monotonicity of `f`, which makes `f(Y) - f(Y₁)` and `Y - Y₁` share a
sign.  Nothing in it is about the parking model, so it is proved here for a
general probability measure on `ℤ`.
-/
import Parking.Support.Range
import Parking.Support.Measurability

noncomputable section

namespace Parking

open MeasureTheory

/-- `Cov(f, g)` under a probability measure. -/
def cov {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) : ℝ :=
  (∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ

/-! ### The coupling identity -/

section Coupling

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `2 Cov(f, g) = E (f(X) - f(X'))(g(X) - g(X'))` for an independent copy. -/
theorem two_mul_cov_eq {f g : Ω → ℝ}
    (h11 : Integrable (fun p : Ω × Ω => f p.1 * g p.1) (μ.prod μ))
    (h12 : Integrable (fun p : Ω × Ω => f p.1 * g p.2) (μ.prod μ))
    (h21 : Integrable (fun p : Ω × Ω => f p.2 * g p.1) (μ.prod μ))
    (h22 : Integrable (fun p : Ω × Ω => f p.2 * g p.2) (μ.prod μ)) :
    2 * cov μ f g
      = ∫ p, (f p.1 - f p.2) * (g p.1 - g p.2) ∂(μ.prod μ) := by
  have hexp : ∀ p : Ω × Ω, (f p.1 - f p.2) * (g p.1 - g p.2)
      = f p.1 * g p.1 - f p.1 * g p.2 - f p.2 * g p.1 + f p.2 * g p.2 := by
    intro p; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp)]
  have hF2 : Integrable (fun p : Ω × Ω => f p.1 * g p.1 - f p.1 * g p.2) (μ.prod μ) :=
    h11.sub h12
  have hF3 : Integrable
      (fun p : Ω × Ω => f p.1 * g p.1 - f p.1 * g p.2 - f p.2 * g p.1) (μ.prod μ) :=
    hF2.sub h21
  rw [integral_add hF3 h22, integral_sub hF2 h21, integral_sub h11 h12]
  have e11 : ∫ p, f p.1 * g p.1 ∂(μ.prod μ) = ∫ ω, f ω * g ω ∂μ := by
    rw [integral_prod _ h11]
    simp
  have e22 : ∫ p, f p.2 * g p.2 ∂(μ.prod μ) = ∫ ω, f ω * g ω ∂μ := by
    rw [integral_prod _ h22]
    simp
  have e12 : ∫ p, f p.1 * g p.2 ∂(μ.prod μ) = (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ := by
    rw [integral_prod _ h12]
    simp only [integral_const_mul, integral_mul_const]
  have e21 : ∫ p, f p.2 * g p.1 ∂(μ.prod μ) = (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ := by
    rw [integral_prod _ h21]
    simp only [integral_mul_const, integral_const_mul]
  rw [e11, e12, e21, e22, cov]
  ring

end Coupling

/-! ### Elementary sign facts -/

theorem abs_mul_abs_of_same_sign {A B : ℝ}
    (h : (0 ≤ A ∧ 0 ≤ B) ∨ (A ≤ 0 ∧ B ≤ 0)) : |A| * |B| = A * B := by
  rcases h with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · rw [abs_of_nonneg hA, abs_of_nonneg hB]
  · rw [abs_of_nonpos hA, abs_of_nonpos hB]; ring

theorem same_sign_of_monotone {f : ℤ → ℝ} (hf : Monotone f) (a b : ℤ) :
    (0 ≤ f a - f b ∧ 0 ≤ (a : ℝ) - (b : ℝ)) ∨
      (f a - f b ≤ 0 ∧ (a : ℝ) - (b : ℝ) ≤ 0) := by
  rcases le_total b a with h | h
  · refine Or.inl ⟨by linarith [hf h], ?_⟩
    have : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast h
    linarith
  · refine Or.inr ⟨by linarith [hf h], ?_⟩
    have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast h
    linarith

/-! ### Step 1 of `lem:product`, for one coordinate -/

section OneSite

variable {ν : Measure ℤ} [IsProbabilityMeasure ν]

theorem measurable_int_fun (f : ℤ → ℝ) : Measurable f := measurable_from_countable' f

omit [IsProbabilityMeasure ν] in
theorem integrable_cast (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) :
    Integrable (fun k : ℤ => (k : ℝ)) ν := by
  refine Integrable.mono' hint (measurable_int_fun _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => ?_)
  rw [Real.norm_eq_abs]

theorem integrable_of_lipschitz {z : ℤ → ℝ}
    (hzlip : ∀ a b : ℤ, |z a - z b| ≤ |(a : ℝ) - (b : ℝ)|)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) : Integrable z ν := by
  refine Integrable.mono' (hint.add (integrable_const |z 0|))
    (measurable_int_fun _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs]
  have h := hzlip k 0
  simp only [Int.cast_zero, sub_zero] at h
  have h2 : |z k| ≤ |z k - z 0| + |z 0| := by
    have := abs_add_le (z k - z 0) (z 0)
    simpa using this
  linarith

omit [IsProbabilityMeasure ν] in
theorem integrable_bdd_mul {f w : ℤ → ℝ} (hfbdd : ∀ k : ℤ, |f k| ≤ 1)
    (hw : Integrable w ν) : Integrable (fun k : ℤ => f k * w k) ν := by
  refine Integrable.mono' hw.abs (measurable_int_fun _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := hfbdd k
  have h2 : (0 : ℝ) ≤ |w k| := abs_nonneg _
  nlinarith

/-- **Step 1 of `lem:product`.**  For a bounded nondecreasing `f` and a
one-Lipschitz `z`, the covariance of `f` and `z` is at most the covariance of
`f` with the coordinate itself. -/
theorem abs_cov_le_cov_cast {f z : ℤ → ℝ} (hfmono : Monotone f)
    (hfbdd : ∀ k : ℤ, |f k| ≤ 1)
    (hzlip : ∀ a b : ℤ, |z a - z b| ≤ |(a : ℝ) - (b : ℝ)|)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) :
    |cov ν f z| ≤ cov ν f (fun k : ℤ => (k : ℝ)) := by
  have hcast : Integrable (fun k : ℤ => (k : ℝ)) ν := integrable_cast hint
  have hz : Integrable z ν := integrable_of_lipschitz hzlip hint
  have hf : Integrable f ν := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (measurable_int_fun _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => ?_)
    rw [Real.norm_eq_abs]; exact hfbdd k
  have hfz : Integrable (fun k : ℤ => f k * z k) ν := integrable_bdd_mul hfbdd hz
  have hfc : Integrable (fun k : ℤ => f k * (k : ℝ)) ν := integrable_bdd_mul hfbdd hcast
  -- the eight product integrabilities
  have p11 : Integrable (fun p : ℤ × ℤ => f p.1 * z p.1) (ν.prod ν) := hfz.comp_fst ν
  have p22 : Integrable (fun p : ℤ × ℤ => f p.2 * z p.2) (ν.prod ν) := hfz.comp_snd ν
  have p12 : Integrable (fun p : ℤ × ℤ => f p.1 * z p.2) (ν.prod ν) := hf.mul_prod hz
  have p21 : Integrable (fun p : ℤ × ℤ => f p.2 * z p.1) (ν.prod ν) := by
    refine Integrable.congr (hz.mul_prod hf) (Filter.Eventually.of_forall fun p => ?_)
    exact mul_comm _ _
  have q11 : Integrable (fun p : ℤ × ℤ => f p.1 * (p.1 : ℝ)) (ν.prod ν) := hfc.comp_fst ν
  have q22 : Integrable (fun p : ℤ × ℤ => f p.2 * (p.2 : ℝ)) (ν.prod ν) := hfc.comp_snd ν
  have q12 : Integrable (fun p : ℤ × ℤ => f p.1 * (p.2 : ℝ)) (ν.prod ν) := hf.mul_prod hcast
  have q21 : Integrable (fun p : ℤ × ℤ => f p.2 * (p.1 : ℝ)) (ν.prod ν) := by
    refine Integrable.congr (hcast.mul_prod hf) (Filter.Eventually.of_forall fun p => ?_)
    exact mul_comm _ _
  have hzeq := two_mul_cov_eq (μ := ν) (f := f) (g := z) p11 p12 p21 p22
  have hceq := two_mul_cov_eq (μ := ν) (f := f) (g := fun k : ℤ => (k : ℝ)) q11 q12 q21 q22
  -- the two integrands
  have hZint : Integrable
      (fun p : ℤ × ℤ => (f p.1 - f p.2) * (z p.1 - z p.2)) (ν.prod ν) := by
    refine Integrable.congr (((p11.sub p12).sub p21).add p22)
      (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hCint : Integrable
      (fun p : ℤ × ℤ => (f p.1 - f p.2) * ((p.1 : ℝ) - (p.2 : ℝ))) (ν.prod ν) := by
    refine Integrable.congr (((q11.sub q12).sub q21).add q22)
      (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hpt : ∀ p : ℤ × ℤ,
      |(f p.1 - f p.2) * (z p.1 - z p.2)|
        ≤ (f p.1 - f p.2) * ((p.1 : ℝ) - (p.2 : ℝ)) := by
    intro p
    have hsign := same_sign_of_monotone hfmono p.1 p.2
    have hkey : |f p.1 - f p.2| * |(p.1 : ℝ) - (p.2 : ℝ)|
        = (f p.1 - f p.2) * ((p.1 : ℝ) - (p.2 : ℝ)) := abs_mul_abs_of_same_sign hsign
    rw [abs_mul, ← hkey]
    exact mul_le_mul_of_nonneg_left (hzlip p.1 p.2) (abs_nonneg _)
  have hchain : |∫ p, (f p.1 - f p.2) * (z p.1 - z p.2) ∂(ν.prod ν)|
      ≤ ∫ p, (f p.1 - f p.2) * ((p.1 : ℝ) - (p.2 : ℝ)) ∂(ν.prod ν) := by
    refine le_trans (abs_integral_le_integral_abs) ?_
    exact integral_mono hZint.abs hCint hpt
  rw [← hzeq, ← hceq, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at hchain
  linarith

end OneSite

end Parking

end
