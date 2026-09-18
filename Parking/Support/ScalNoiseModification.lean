/-
The jointly continuous modification of the space-time noise field of the
directed scaling limit (`parking.tex:3192-3203`).

The field `Z_T(s,x)` of `Parking/Support/ContOrientedLimit.lean` is defined
pointwise, as the coercion of an `L²` element to a function, separately for each
space-time point `(s,x)`.  The paper's Step 1 uses it as a jointly continuous
field, which is what the multi-parameter Kolmogorov-Chentsov theorem supplies:
the increment of the field is a white-noise integral, so its second moment is
the squared `L²` distance of the two test functions, and the Kolmogorov
condition is a statement about the heat kernel.

This module records the two steps that do not depend on the increment bound:
the second moment of an increment of the field, and the passage from the
Kolmogorov condition to a modification whose sample paths are continuous.
-/
import Parking.Support.ContOrientedLimit
import LatticeProb.Prob.ChentsovPiModification

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

namespace Parking

/-- **The second moment of an increment of the noise field** is `v` times the
squared `L²` distance of the two test functions.  The field is linear in the
test function, so the increment is the white-noise integral of the difference,
and the white noise is an isometry. -/
theorem integral_contZ_sub_sq {v : ℝ} (hv : 0 ≤ v) (T s x s' x' : ℝ) :
    (∫ ω, (contZ v T s x ω - contZ v T s' x' ω) ^ 2 ∂contNoiseLaw)
      = v * ∫ p : ℝ × ℝ, (contNoiseTest T s x p - contNoiseTest T s' x' p) ^ 2 := by
  have hf : MemLp (contNoiseTest T s x) 2 (volume : Measure (ℝ × ℝ)) := memLp_contNoiseTest T s x
  have hg : MemLp (contNoiseTest T s' x') 2 (volume : Measure (ℝ × ℝ)) :=
    memLp_contNoiseTest T s' x'
  have hfg : MemLp (contNoiseTest T s x - contNoiseTest T s' x') 2 (volume : Measure (ℝ × ℝ)) :=
    hf.sub hg
  have hdiff : (fun ω => contZ v T s x ω - contZ v T s' x' ω)
      =ᵐ[contNoiseLaw] fun ω => Real.sqrt v *
        LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ))
          (contNoiseTest T s x - contNoiseTest T s' x') ω := by
    filter_upwards [LatticeProb.whiteNoiseOf_add (volume : Measure (ℝ × ℝ)) hf hg.neg,
      LatticeProb.whiteNoiseOf_smul (volume : Measure (ℝ × ℝ)) (-1) hg] with ω h1 h2
    have h2' : LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ))
        (-contNoiseTest T s' x') ω
        = -LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) (contNoiseTest T s' x') ω := by
      have := h2
      simpa using this
    have h1' : LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ))
        (contNoiseTest T s x - contNoiseTest T s' x') ω
        = LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) (contNoiseTest T s x) ω
          - LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) (contNoiseTest T s' x') ω := by
      rw [sub_eq_add_neg, h1, h2']
      ring
    simp only [contZ]
    rw [h1']
    ring
  have hsq : (fun ω => (contZ v T s x ω - contZ v T s' x' ω) ^ 2)
      =ᵐ[contNoiseLaw] fun ω => v * (LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ))
        (contNoiseTest T s x - contNoiseTest T s' x') ω *
        LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ))
        (contNoiseTest T s x - contNoiseTest T s' x') ω) := by
    filter_upwards [hdiff] with ω h
    rw [h, mul_pow, Real.sq_sqrt hv]
    ring
  rw [integral_congr_ae hsq, MeasureTheory.integral_const_mul,
    LatticeProb.integral_whiteNoiseOf_mul (volume : Measure (ℝ × ℝ)) hfg hfg]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  simp only [Pi.sub_apply]
  ring

/-- The noise field as a process indexed by the space-time point `(s,x)`, read
as a point of `Fin 2 → ℝ`. -/
def contZProcess (v T : ℝ) : (Fin 2 → ℝ) → contNoiseSpace → ℝ :=
  fun u => contZ v T (u 0) (u 1)

/-- The pair of two values of the noise field is measurable. -/
theorem measurablePair_contZ (v T : ℝ) (u u' : Fin 2 → ℝ) :
    Measurable fun ω => (contZ v T (u 0) (u 1) ω, contZ v T (u' 0) (u' 1) ω) :=
  (Parking.measurable_contZ v T (u 0) (u 1)).prodMk (Parking.measurable_contZ v T (u' 0) (u' 1))

/-- The Kolmogorov condition for the noise field, assembled from its two
ingredients: the joint measurability of pairs of values and the increment
moment bound. -/
theorem isKolmogorovProcess_contZ {v T p q : ℝ} {M : ℝ≥0}
    (hp : 0 < p) (hq : 0 < q)
    (hmeas : ∀ u v' : Fin 2 → ℝ,
      Measurable fun ω => (contZ v T (u 0) (u 1) ω, contZ v T (v' 0) (v' 1) ω))
    (hcond : ∀ u v' : Fin 2 → ℝ,
      ∫⁻ ω, edist (contZ v T (u 0) (u 1) ω) (contZ v T (v' 0) (v' 1) ω) ^ p ∂contNoiseLaw
        ≤ M * edist u v' ^ q) :
    IsKolmogorovProcess (contZProcess v T) contNoiseLaw p q M := by
  refine ⟨?_, hcond, hp, hq⟩
  intro s t
  exact (hmeas s t).mono le_rfl (le_of_eq (Prod.borelSpace (α := ℝ) (β := ℝ)).measurable_eq.symm)

/-- **The increment of the noise field is square integrable.**  The increment is
a constant multiple of the white-noise integral of the difference of the two
test functions, and a white-noise integral is `L²`. -/
theorem integrable_contZ_sub_sq {v : ℝ} (hv : 0 ≤ v) (T s x s' x' : ℝ) :
    Integrable (fun ω => (contZ v T s x ω - contZ v T s' x' ω) ^ 2) contNoiseLaw := by
  have hf : MemLp (contNoiseTest T s x) 2 (volume : Measure (ℝ × ℝ)) := memLp_contNoiseTest T s x
  have hg : MemLp (contNoiseTest T s' x') 2 (volume : Measure (ℝ × ℝ)) :=
    memLp_contNoiseTest T s' x'
  have hfg : MemLp (contNoiseTest T s x - contNoiseTest T s' x') 2
      (volume : Measure (ℝ × ℝ)) := hf.sub hg
  have hdiff : (fun ω => contZ v T s x ω - contZ v T s' x' ω)
      =ᵐ[contNoiseLaw] fun ω => Real.sqrt v *
        LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ))
          (contNoiseTest T s x - contNoiseTest T s' x') ω := by
    filter_upwards [LatticeProb.whiteNoiseOf_add (volume : Measure (ℝ × ℝ)) hf hg.neg,
      LatticeProb.whiteNoiseOf_smul (volume : Measure (ℝ × ℝ)) (-1) hg] with ω h1 h2
    have h2' : LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ))
        (-contNoiseTest T s' x') ω
        = -LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) (contNoiseTest T s' x') ω := by
      simpa using h2
    have h1' : LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ))
        (contNoiseTest T s x - contNoiseTest T s' x') ω
        = LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) (contNoiseTest T s x) ω
          - LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) (contNoiseTest T s' x') ω := by
      rw [sub_eq_add_neg, h1, h2']
      ring
    simp only [contZ]
    rw [h1']
    ring
  have hsq : (fun ω => (contZ v T s x ω - contZ v T s' x' ω) ^ 2)
      =ᵐ[contNoiseLaw] fun ω => v * (LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ))
        (contNoiseTest T s x - contNoiseTest T s' x') ω *
        LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ))
        (contNoiseTest T s x - contNoiseTest T s' x') ω) := by
    filter_upwards [hdiff] with ω h
    rw [h, mul_pow, Real.sq_sqrt hv]
    ring
  rw [integrable_congr hsq]
  have hm : MemLp (LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ))
      (contNoiseTest T s x - contNoiseTest T s' x')) 2
      (LatticeProb.whiteNoiseLaw (volume : Measure (ℝ × ℝ))) :=
    (LatticeProb.isGaussianProcess_whiteNoiseOf (volume : Measure (ℝ × ℝ))).hasGaussianLaw_eval _
      |>.memLp_two
  exact (hm.integrable_mul hm).const_mul v


/-- **The Kolmogorov condition for the noise field.**  The second-moment
identity `integral_contZ_sub_sq` and the heat-kernel increment bound give the
`L²` increment bound of the multi-parameter Kolmogorov criterion, with the
constant `2 ^ q * v * C` and exponent `q`.  The space-time index has dimension
`2`, so the criterion is applied at `q = 3 > 2`. -/
theorem kolmogorovCondition_contZ {v T q : ℝ} (hv : 0 ≤ v) (hq : 0 < q) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ s x s' x' : ℝ,
      ∫ p : ℝ × ℝ, (contNoiseTest T s x p - contNoiseTest T s' x' p) ^ 2
        ≤ C * (|s - s'| + |x - x'|) ^ q) :
    ∀ u v' : Fin 2 → ℝ,
      ∫⁻ ω, edist (contZ v T (u 0) (u 1) ω) (contZ v T (v' 0) (v' 1) ω) ^ (2 : ℝ)
        ∂contNoiseLaw ≤ ENNReal.ofReal (2 ^ q * v * C) * edist u v' ^ q := by
  intro u v'
  have hpt : ∀ ω : contNoiseSpace, edist (contZ v T (u 0) (u 1) ω) (contZ v T (v' 0) (v' 1) ω) ^ (2 : ℝ)
      = ENNReal.ofReal ((contZ v T (u 0) (u 1) ω - contZ v T (v' 0) (v' 1) ω) ^ 2) := by
    intro ω
    rw [edist_dist, Real.dist_eq]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    rw [sq, ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    rw [← sq, sq_abs]
  have h2 : (∫ ω, (contZ v T (u 0) (u 1) ω - contZ v T (v' 0) (v' 1) ω) ^ 2 ∂contNoiseLaw)
      = v * ∫ p : ℝ × ℝ, (contNoiseTest T (u 0) (u 1) p - contNoiseTest T (v' 0) (v' 1) p) ^ 2 :=
    integral_contZ_sub_sq hv T (u 0) (u 1) (v' 0) (v' 1)
  have hle : (∫ ω, (contZ v T (u 0) (u 1) ω - contZ v T (v' 0) (v' 1) ω) ^ 2 ∂contNoiseLaw)
      ≤ v * (C * (|u 0 - v' 0| + |u 1 - v' 1|) ^ q) := by
    rw [h2]
    exact mul_le_mul_of_nonneg_left (hbound (u 0) (u 1) (v' 0) (v' 1)) hv
  have hlin : (∫⁻ ω, edist (contZ v T (u 0) (u 1) ω) (contZ v T (v' 0) (v' 1) ω) ^ (2 : ℝ)
      ∂contNoiseLaw)
      = ENNReal.ofReal (∫ ω, (contZ v T (u 0) (u 1) ω - contZ v T (v' 0) (v' 1) ω) ^ 2 ∂contNoiseLaw) := by
    rw [ofReal_integral_eq_lintegral_ofReal
      (integrable_contZ_sub_sq hv T (u 0) (u 1) (v' 0) (v' 1))
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
    exact lintegral_congr_ae (Filter.Eventually.of_forall hpt)
  have hed : edist u v' ^ q
      = ENNReal.ofReal ((max |u 0 - v' 0| |u 1 - v' 1|) ^ q) := by
    rw [edist_pi_def, Finset.univ_fin2]
    rw [Finset.sup_insert, Finset.sup_singleton]
    rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq]
    rw [← ENNReal.ofReal_max, ← ENNReal.ofReal_rpow_of_nonneg (le_max_of_le_left (abs_nonneg _)) hq.le]
  have hsum : (|u 0 - v' 0| + |u 1 - v' 1|) ^ q
      ≤ 2 ^ q * (max |u 0 - v' 0| |u 1 - v' 1|) ^ q := by
    set a := |u 0 - v' 0| with ha
    set b := |u 1 - v' 1| with hb
    set m := max a b with hm
    have h1 : a ≤ m := le_max_left a b
    have h2' : b ≤ m := le_max_right a b
    have h0 : (0 : ℝ) ≤ m := le_max_of_le_left (abs_nonneg _)
    have ha0 : 0 ≤ a := abs_nonneg _
    have hb0 : 0 ≤ b := abs_nonneg _
    have hab : a + b ≤ 2 * m := by linarith
    calc (a + b) ^ q ≤ (2 * m) ^ q := Real.rpow_le_rpow (by positivity) hab hq.le
      _ = 2 ^ q * m ^ q := by rw [Real.mul_rpow (by norm_num) h0]
  rw [hlin, hed]
  have hmid : ENNReal.ofReal (∫ ω, (contZ v T (u 0) (u 1) ω - contZ v T (v' 0) (v' 1) ω) ^ 2 ∂contNoiseLaw)
      ≤ ENNReal.ofReal (2 ^ q * v * C * (max |u 0 - v' 0| |u 1 - v' 1|) ^ q) := by
    refine ENNReal.ofReal_le_ofReal ?_
    calc ∫ ω, (contZ v T (u 0) (u 1) ω - contZ v T (v' 0) (v' 1) ω) ^ 2 ∂contNoiseLaw
        ≤ v * (C * (|u 0 - v' 0| + |u 1 - v' 1|) ^ q) := hle
      _ ≤ v * (C * (2 ^ q * (max |u 0 - v' 0| |u 1 - v' 1|) ^ q)) := by
          refine mul_le_mul_of_nonneg_left ?_ hv
          exact mul_le_mul_of_nonneg_left hsum hC
      _ = 2 ^ q * v * C * (max |u 0 - v' 0| |u 1 - v' 1|) ^ q := by ring
  refine le_trans hmid (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity)]

/-- **The jointly continuous modification of the noise field.**  From the
Kolmogorov condition at exponent `q > 2` (the dimension of the space-time
index) the multi-parameter Kolmogorov-Chentsov theorem gives a modification of
`contZ` whose sample paths are continuous on the whole plane. -/
theorem exists_continuous_modification_contZ {v T q : ℝ} (hv : 0 ≤ v) (hq : 2 < q) {C : ℝ}
    (hC : 0 ≤ C)
    (hbound : ∀ s x s' x' : ℝ,
      ∫ p : ℝ × ℝ, (contNoiseTest T s x p - contNoiseTest T s' x' p) ^ 2
        ≤ C * (|s - s'| + |x - x'|) ^ q) :
    ∃ Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ, (∀ z, Measurable (Y z)) ∧
      (∀ z, contZProcess v T z =ᵐ[contNoiseLaw] Y z) ∧
      ∀ᵐ ω ∂contNoiseLaw, Continuous fun z => Y z ω := by
  refine LatticeProb.exists_continuous_modification_pi (p := 2)
    (M := ⟨2 ^ q * v * C, by positivity⟩) ?_ hq
  refine isKolmogorovProcess_contZ (by norm_num) (by linarith)
    (measurablePair_contZ v T) ?_
  intro u v'
  rw [ENNReal.coe_nnreal_eq]
  exact kolmogorovCondition_contZ hv (by linarith) hC hbound u v'

end Parking
