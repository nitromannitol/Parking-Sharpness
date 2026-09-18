/-
The independence across sites used in Step 3 of `lem:critical-density`
(`parking.tex:1325-1328`): "All unmatched particles or holes created at one site
have the same sign, and the collections created at distinct sites are
independent.  For each pair of distinct sites, the expected number of
opposite-sign pairs is `ε²/2`."

The signed change at a site is `Δ(x) = η̃(x) - η(x)`, and the labels created there
are its positive part when it is positive and its negative part when it is
negative, which is what "all have the same sign" means: at one site only one of
the two parts is nonzero.  The expected number of opposite-sign pairs across two
distinct sites is therefore

    E[Δ(0)⁺] E[Δ(z)⁻] + E[Δ(0)⁻] E[Δ(z)⁺] = 2 (ε/2)² = ε²/2,

the factorization being the independence of two distinct coordinates of an
i.i.d. field (`LatticeProb.integral_mul_eval`) and each factor being `ε/2` by the
symmetry of the one-site joint law (`Parking.integral_posPart_resampleOne`).
-/
import Parking.Support.Resample
import LatticeProb.Prob.CoordIntegral

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- The positive part of the change at a site: the labels created there when the
resampling raises the count. -/
def dPos (c : Site d → ℤ × ℤ) (x : Site d) : ℝ := max (((c x).2 : ℝ) - ((c x).1 : ℝ)) 0

/-- The negative part of the change at a site. -/
def dNeg (c : Site d → ℤ × ℤ) (x : Site d) : ℝ := max (((c x).1 : ℝ) - ((c x).2 : ℝ)) 0

theorem measurable_dPos (x : Site d) : Measurable (fun c : Site d → ℤ × ℤ => dPos c x) := by
  unfold dPos; fun_prop

theorem measurable_dNeg (x : Site d) : Measurable (fun c : Site d → ℤ × ℤ => dNeg c x) := by
  unfold dNeg; fun_prop

/-- At one site only one of the two parts is nonzero: all the labels created at a
site have the same sign. -/
theorem dPos_mul_dNeg (c : Site d → ℤ × ℤ) (x : Site d) : dPos c x * dNeg c x = 0 := by
  unfold dPos dNeg
  rcases le_total (((c x).1 : ℝ)) (((c x).2 : ℝ)) with h | h
  · rw [max_eq_right (by linarith : ((c x).1 : ℝ) - ((c x).2 : ℝ) ≤ 0), mul_zero]
  · rw [max_eq_right (by linarith : ((c x).2 : ℝ) - ((c x).1 : ℝ) ≤ 0), zero_mul]

/-! ### The mean of one part -/

theorem integral_dPos (ν : Measure ℤ) [IsProbabilityMeasure ν] {p : ℝ≥0∞} (hp : p ≤ 1)
    (hint : Integrable (fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|) (ν.prod ν)) (x : Site d) :
    ∫ c, dPos c x ∂(resampleLaw d ν p) = p.toReal * gammaOf ν / 2 := by
  haveI := resampleOne_isProbability ν hp
  have hmap : (resampleLaw d ν p).map (fun c : Site d → ℤ × ℤ => c x) = resampleOne ν p :=
    resampleLaw_map_eval ν hp x
  have hpm : Measurable (fun q : ℤ × ℤ => max ((q.2 : ℝ) - (q.1 : ℝ)) 0) := by fun_prop
  have h := integral_map (μ := resampleLaw d ν p) (φ := fun c : Site d → ℤ × ℤ => c x)
    (f := fun q : ℤ × ℤ => max ((q.2 : ℝ) - (q.1 : ℝ)) 0)
    (measurable_pi_apply x).aemeasurable hpm.aestronglyMeasurable
  rw [hmap] at h
  rw [show (fun c : Site d → ℤ × ℤ => dPos c x)
      = fun c : Site d → ℤ × ℤ => max (((c x).2 : ℝ) - ((c x).1 : ℝ)) 0 from rfl, ← h]
  exact integral_posPart_resampleOne ν hp hint

theorem integral_dNeg (ν : Measure ℤ) [IsProbabilityMeasure ν] {p : ℝ≥0∞} (hp : p ≤ 1)
    (hint : Integrable (fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|) (ν.prod ν)) (x : Site d) :
    ∫ c, dNeg c x ∂(resampleLaw d ν p) = p.toReal * gammaOf ν / 2 := by
  haveI := resampleOne_isProbability ν hp
  have hmap : (resampleLaw d ν p).map (fun c : Site d → ℤ × ℤ => c x) = resampleOne ν p :=
    resampleLaw_map_eval ν hp x
  have hpm : Measurable (fun q : ℤ × ℤ => max ((q.1 : ℝ) - (q.2 : ℝ)) 0) := by fun_prop
  have h := integral_map (μ := resampleLaw d ν p) (φ := fun c : Site d → ℤ × ℤ => c x)
    (f := fun q : ℤ × ℤ => max ((q.1 : ℝ) - (q.2 : ℝ)) 0)
    (measurable_pi_apply x).aemeasurable hpm.aestronglyMeasurable
  rw [hmap] at h
  rw [show (fun c : Site d → ℤ × ℤ => dNeg c x)
      = fun c : Site d → ℤ × ℤ => max (((c x).1 : ℝ) - ((c x).2 : ℝ)) 0 from rfl, ← h]
  have hswap : ∫ q : ℤ × ℤ, max ((q.1 : ℝ) - (q.2 : ℝ)) 0 ∂(resampleOne ν p)
      = ∫ q : ℤ × ℤ, max ((q.2 : ℝ) - (q.1 : ℝ)) 0 ∂(resampleOne ν p) := by
    conv_lhs => rw [← resampleOne_map_swap ν p]
    rw [integral_map measurable_swap.aemeasurable hpm.aestronglyMeasurable]
    rfl
  rw [hswap]
  exact integral_posPart_resampleOne ν hp hint


/-! ### The labels created at the origin, and the range of `ε` -/

/-- **The expected number of labels created at a site is the expected absolute
change there.**  Only one of the two parts is nonzero, and they add up to the
absolute change. -/
theorem integral_labels (ν : Measure ℤ) [IsProbabilityMeasure ν] {p : ℝ≥0∞} (hp : p ≤ 1)
    (hint : Integrable (fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|) (ν.prod ν)) (x : Site d) :
    ∫ c, (dPos c x + dNeg c x) ∂(resampleLaw d ν p) = p.toReal * gammaOf ν := by
  haveI := resampleOne_isProbability ν hp
  have hmap : (resampleLaw d ν p).map (fun c : Site d → ℤ × ℤ => c x) = resampleOne ν p :=
    resampleLaw_map_eval ν hp x
  have hsum : ∀ c : Site d → ℤ × ℤ,
      dPos c x + dNeg c x = |((c x).2 : ℝ) - ((c x).1 : ℝ)| := by
    intro c
    unfold dPos dNeg
    rcases le_total (((c x).1 : ℝ)) (((c x).2 : ℝ)) with h | h
    · have h1 : max (((c x).2 : ℝ) - ((c x).1 : ℝ)) 0 = ((c x).2 : ℝ) - ((c x).1 : ℝ) :=
        max_eq_left (by linarith)
      have h2 : max (((c x).1 : ℝ) - ((c x).2 : ℝ)) 0 = 0 := max_eq_right (by linarith)
      have h3 : |((c x).2 : ℝ) - ((c x).1 : ℝ)| = ((c x).2 : ℝ) - ((c x).1 : ℝ) :=
        abs_of_nonneg (by linarith)
      rw [h1, h2, h3]; ring
    · have h1 : max (((c x).2 : ℝ) - ((c x).1 : ℝ)) 0 = 0 := max_eq_right (by linarith)
      have h2 : max (((c x).1 : ℝ) - ((c x).2 : ℝ)) 0 = ((c x).1 : ℝ) - ((c x).2 : ℝ) :=
        max_eq_left (by linarith)
      have h3 : |((c x).2 : ℝ) - ((c x).1 : ℝ)| = -(((c x).2 : ℝ) - ((c x).1 : ℝ)) :=
        abs_of_nonpos (by linarith)
      rw [h1, h2, h3]; ring
  have h := integral_map (μ := resampleLaw d ν p) (φ := fun c : Site d → ℤ × ℤ => c x)
    (f := fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|)
    (measurable_pi_apply x).aemeasurable measurable_absDiff.aestronglyMeasurable
  rw [hmap] at h
  calc ∫ c, (dPos c x + dNeg c x) ∂(resampleLaw d ν p)
      = ∫ c : Site d → ℤ × ℤ, |((c x).2 : ℝ) - ((c x).1 : ℝ)| ∂(resampleLaw d ν p) :=
        integral_congr_ae (Filter.Eventually.of_forall hsum)
    _ = ∫ q : ℤ × ℤ, |(q.2 : ℝ) - (q.1 : ℝ)| ∂(resampleOne ν p) := h.symm
    _ = p.toReal * gammaOf ν := integral_absDiff_resampleOne ν hp hint

/-- **Every `ε` in `[0, γ]` is realized by a resampling probability.**  The
paper's `ε/γ`. -/
theorem exists_resample_prob (ν : Measure ℤ) {ε : ℝ} (hγ : 0 < gammaOf ν) (hε : 0 ≤ ε)
    (hεγ : ε ≤ gammaOf ν) :
    ENNReal.ofReal (ε / gammaOf ν) ≤ 1 ∧
      (ENNReal.ofReal (ε / gammaOf ν)).toReal * gammaOf ν = ε := by
  constructor
  · rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((div_le_one hγ).mpr hεγ)
  · rw [ENNReal.toReal_ofReal (by positivity)]
    field_simp

/-! ### Two distinct sites -/

/-- **Opposite-sign pairs across two distinct sites.**  The two coordinates of an
i.i.d. field are independent, so the mean of the product is the product of the
means, and each factor is `ε/2`. -/
theorem integral_dNeg_mul_dPos (ν : Measure ℤ) [IsProbabilityMeasure ν] {p : ℝ≥0∞} (hp : p ≤ 1)
    (hint : Integrable (fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|) (ν.prod ν))
    {z : Site d} (hz : z ≠ 0) :
    ∫ c, dNeg c z * dPos c 0 ∂(resampleLaw d ν p)
      = (p.toReal * gammaOf ν / 2) * (p.toReal * gammaOf ν / 2) := by
  classical
  haveI := resampleOne_isProbability ν hp
  have hinv : ∀ c : Site d → ℤ × ℤ,
      dNeg (Function.update c (0 : Site d) ((0 : ℤ), (0 : ℤ))) z = dNeg c z := by
    intro c
    unfold dNeg
    rw [Function.update_of_ne hz]
  have hfac := LatticeProb.integral_mul_eval (μ := fun _ : Site d => resampleOne ν p)
    (0 : Site d) ((0 : ℤ), (0 : ℤ)) (fun c : Site d → ℤ × ℤ => dNeg c z) (measurable_dNeg z)
    hinv (fun q : ℤ × ℤ => max ((q.2 : ℝ) - (q.1 : ℝ)) 0) (by fun_prop)
  rw [show (Measure.infinitePi fun _ : Site d => resampleOne ν p) = resampleLaw d ν p from rfl]
    at hfac
  rw [show (fun c : Site d → ℤ × ℤ => dNeg c z * dPos c 0)
      = fun c : Site d → ℤ × ℤ => dNeg c z * max (((c 0).2 : ℝ) - ((c 0).1 : ℝ)) 0 from rfl,
    hfac, integral_dNeg ν hp hint z]
  congr 1
  exact integral_posPart_resampleOne ν hp hint

theorem integral_dPos_mul_dNeg (ν : Measure ℤ) [IsProbabilityMeasure ν] {p : ℝ≥0∞} (hp : p ≤ 1)
    (hint : Integrable (fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|) (ν.prod ν))
    {z : Site d} (hz : z ≠ 0) :
    ∫ c, dPos c z * dNeg c 0 ∂(resampleLaw d ν p)
      = (p.toReal * gammaOf ν / 2) * (p.toReal * gammaOf ν / 2) := by
  classical
  haveI := resampleOne_isProbability ν hp
  have hinv : ∀ c : Site d → ℤ × ℤ,
      dPos (Function.update c (0 : Site d) ((0 : ℤ), (0 : ℤ))) z = dPos c z := by
    intro c
    unfold dPos
    rw [Function.update_of_ne hz]
  have hfac := LatticeProb.integral_mul_eval (μ := fun _ : Site d => resampleOne ν p)
    (0 : Site d) ((0 : ℤ), (0 : ℤ)) (fun c : Site d → ℤ × ℤ => dPos c z) (measurable_dPos z)
    hinv (fun q : ℤ × ℤ => max ((q.1 : ℝ) - (q.2 : ℝ)) 0) (by fun_prop)
  rw [show (Measure.infinitePi fun _ : Site d => resampleOne ν p) = resampleLaw d ν p from rfl]
    at hfac
  rw [show (fun c : Site d → ℤ × ℤ => dPos c z * dNeg c 0)
      = fun c : Site d → ℤ × ℤ => dPos c z * max (((c 0).1 : ℝ) - ((c 0).2 : ℝ)) 0 from rfl,
    hfac, integral_dPos ν hp hint z]
  congr 1
  have hpm : Measurable (fun q : ℤ × ℤ => max ((q.1 : ℝ) - (q.2 : ℝ)) 0) := by fun_prop
  have hswap : ∫ q : ℤ × ℤ, max ((q.1 : ℝ) - (q.2 : ℝ)) 0 ∂(resampleOne ν p)
      = ∫ q : ℤ × ℤ, max ((q.2 : ℝ) - (q.1 : ℝ)) 0 ∂(resampleOne ν p) := by
    conv_lhs => rw [← resampleOne_map_swap ν p]
    rw [integral_map measurable_swap.aemeasurable hpm.aestronglyMeasurable]
    rfl
  rw [hswap]
  exact integral_posPart_resampleOne ν hp hint

end Parking

end
