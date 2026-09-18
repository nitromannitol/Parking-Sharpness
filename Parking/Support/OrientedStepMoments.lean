/- Steps 2, 3 and 4 of the proof of `thm:oriented-walk` (`parking.tex:3279-3342`):
the moment inequalities the five-step assembly consumes.

The moment recursion is closed by bounding the `r`-th moment of the divisible
odometer through its mean and the directed concentration estimate, and the
resulting inequalities are exactly the hypotheses `hmom`, `hmom2` and `herr` of
`Parking.oriented_walk_of_steps`.
-/
import Parking.Support.OrientedMomentRecursion
import Parking.Support.OrientedConcentration
import Parking.Support.OrientedTwoMean
import Parking.Support.OrientedLogMean
import Parking.Support.UpperTarget
import Parking.Support.ProductLift

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset

variable {d : ℕ}

/-- The `r`-th moment of the directed divisible odometer at the origin, through
its mean and the directed concentration estimate `eq:oriented-u-concentration`. -/
theorem exists_oriented_uOriented_norm (hd : 2 ≤ d) (hConc : Parking.External.UConcentration)
    (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 2 ≤ r →
      (∫ ω : Data d, |uOriented (confReal ω) n 0| ^ r ∂(orientedLaw d ν)) ^ (1 / r)
        ≤ meanuOriented (orientedLaw d ν) n
          + C * (Real.sqrt (r * orientedKappa d n) + r) := by
  haveI := hν.prob
  have hd1 : 1 ≤ d := by omega
  haveI : IsProbabilityMeasure (orientedLaw d ν) := orientedLaw_isProbability hd1 ν
  obtain ⟨C, hC, hb⟩ := exists_oriented_centered_bound hd hConc ν hν
  refine ⟨C, hC, fun n hn r hr => ?_⟩
  have hr0 : (0 : ℝ) < r := by linarith
  have hr1 : (1 : ℝ) ≤ r := by linarith
  set m : ℝ := meanuOriented (orientedLaw d ν) n with hm
  have hIu : Integrable (fun ω : Data d => |uOriented (confReal ω) n 0| ^ r)
      (orientedLaw d ν) := integrable_oriented_uOriented_rpow hd1 ν hν hr1 n 0
  have hmeasu : Measurable fun ω : Data d => uOriented (confReal ω) n 0 :=
    (measurable_uOriented n 0).comp measurable_confReal
  have hIc : Integrable (fun ω : Data d => |uOriented (confReal ω) n 0 - m| ^ r)
      (orientedLaw d ν) := by
    have hdom : Integrable (fun ω : Data d =>
        ((2 : ℝ) ^ r) * (|uOriented (confReal ω) n 0| ^ r + |m| ^ r)) (orientedLaw d ν) :=
      (hIu.add (integrable_const _)).const_mul _
    refine hdom.mono' ((hmeasu.sub measurable_const).abs.pow_const r).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) r)]
    have h1 : |uOriented (confReal ω) n 0 - m|
        ≤ 2 * max |uOriented (confReal ω) n 0| |m| := by
      have := abs_sub (uOriented (confReal ω) n 0) m
      have h2 : |uOriented (confReal ω) n 0| ≤ max |uOriented (confReal ω) n 0| |m| :=
        le_max_left _ _
      have h3 : |m| ≤ max |uOriented (confReal ω) n 0| |m| := le_max_right _ _
      calc |uOriented (confReal ω) n 0 - m| ≤ |uOriented (confReal ω) n 0| + |m| :=
            abs_sub _ _
        _ ≤ 2 * max |uOriented (confReal ω) n 0| |m| := by linarith
    calc |uOriented (confReal ω) n 0 - m| ^ r
        ≤ (2 * max |uOriented (confReal ω) n 0| |m|) ^ r :=
          Real.rpow_le_rpow (abs_nonneg _) h1 hr0.le
      _ = (2 : ℝ) ^ r * (max |uOriented (confReal ω) n 0| |m|) ^ r :=
          Real.mul_rpow (by norm_num) (le_max_of_le_left (abs_nonneg _))
      _ ≤ (2 : ℝ) ^ r * (|uOriented (confReal ω) n 0| ^ r + |m| ^ r) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) r)
          rcases max_cases |uOriented (confReal ω) n 0| |m| with ⟨he, _⟩ | ⟨he, _⟩
          · rw [he]; linarith [Real.rpow_nonneg (abs_nonneg m) r]
          · rw [he]; linarith [Real.rpow_nonneg (abs_nonneg (uOriented (confReal ω) n 0)) r]
  have hmink := rNorm_add_le (orientedLaw d ν) hr1
    (f := fun ω : Data d => uOriented (confReal ω) n 0 - m) (g := fun _ : Data d => m)
    ((hmeasu.sub measurable_const).aestronglyMeasurable)
    (measurable_const.aestronglyMeasurable) hIc (by
      simp) (by
      refine hIu.congr ?_
      filter_upwards [] with ω
      rw [sub_add_cancel])
  have hm0' : 0 ≤ m := integral_nonneg fun ω => uOriented_nonneg _ n 0
  rw [rNorm_const (orientedLaw d ν) hr0 hm0'] at hmink
  have hsum : rNorm (orientedLaw d ν) r
      (fun ω : Data d => (uOriented (confReal ω) n 0 - m) + m)
      = (∫ ω : Data d, |uOriented (confReal ω) n 0| ^ r ∂(orientedLaw d ν)) ^ (1 / r) := by
    rw [rNorm]
    congr 2
    funext ω
    rw [sub_add_cancel]
  rw [hsum] at hmink
  have hm0 : 0 ≤ m := integral_nonneg fun ω => uOriented_nonneg _ n 0
  have hcb : rNorm (orientedLaw d ν) r (fun ω : Data d => uOriented (confReal ω) n 0 - m)
      ≤ C * (Real.sqrt (r * orientedKappa d n) + r) := hb n hn r hr
  linarith

/-! ### Step 2: the moment inequality at `d = 2` and `r = 8` -/

theorem exists_oriented_hmom2 (hBern : Parking.External.Bernstein)
    (hConc : Parking.External.UConcentration) (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (∫ ω : Data 2, (U ω n 0 : ℝ) ^ (8 : ℝ) ∂(orientedLaw 2 ν)) ^ ((1 : ℝ) / 8) ≤
        C * (n : ℝ) ^ ((1 : ℝ) / 4) +
          C * (n : ℝ) ^ ((1 : ℝ) / 8) *
            ((∫ ω : Data 2, (U ω n 0 : ℝ) ^ (8 : ℝ) ∂(orientedLaw 2 ν)) ^ ((1 : ℝ) / 16)
              + 1) := by
  haveI := hν.prob
  obtain ⟨C₀, hC₀, hrec⟩ := exists_oriented_U_moment_recursion hBern
  obtain ⟨C₁, hC₁, hu⟩ := exists_oriented_uOriented_norm (d := 2) (by norm_num) hConc ν hν
  obtain ⟨θ, hθ, hexp⟩ := hν.expMoment
  have hmom8 : Integrable (fun k : ℤ => |(k : ℝ)| ^ (8 : ℝ)) ν := by
    obtain ⟨K, hK, hbd⟩ := rpow_le_const_mul_exp (by norm_num : (0:ℝ) ≤ (8:ℝ)) hθ
    refine Integrable.mono' (hexp.const_mul K)
      (measurable_from_countable' (fun k : ℤ => |(k : ℝ)| ^ (8 : ℝ))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact hbd _ (abs_nonneg _)
  obtain ⟨C₂, hC₂, hmean⟩ := exists_meanuOriented_two_upper ν hν.mean 8 (by norm_num) hmom8
  refine ⟨C₂ + C₁ * (Real.sqrt 8 + 8) + 16 * C₀, by positivity, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hq4 : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := Real.one_le_rpow hn1 (by norm_num)
  have hq8 : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 8) := Real.one_le_rpow hn1 (by norm_num)
  set A : ℝ := (∫ ω : Data 2, (U ω n 0 : ℝ) ^ (8 : ℝ) ∂(orientedLaw 2 ν)) ^ ((1 : ℝ) / 8) with hA
  have hI0 : (0 : ℝ) ≤ ∫ ω : Data 2, (U ω n 0 : ℝ) ^ (8 : ℝ) ∂(orientedLaw 2 ν) :=
    integral_nonneg fun ω => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hA0 : 0 ≤ A := Real.rpow_nonneg hI0 _
  have hAhalf : A ^ ((1 : ℝ) / 2)
      = (∫ ω : Data 2, (U ω n 0 : ℝ) ^ (8 : ℝ) ∂(orientedLaw 2 ν)) ^ ((1 : ℝ) / 16) := by
    rw [hA, ← Real.rpow_mul hI0]
    norm_num
  -- the divisible moment
  have hkappa : orientedKappa 2 n = (n : ℝ) ^ ((1 : ℝ) / 2) := by
    simp [orientedKappa]
  have hsq : Real.sqrt (8 * orientedKappa 2 n) = Real.sqrt 8 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [hkappa, Real.sqrt_eq_rpow, Real.mul_rpow (by norm_num)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _), ← Real.rpow_mul (Nat.cast_nonneg n),
      ← Real.sqrt_eq_rpow]
    norm_num
  have hDu : (∫ ω : Data 2, |uOriented (confReal ω) n 0| ^ (8 : ℝ) ∂(orientedLaw 2 ν)) ^
      ((1 : ℝ) / 8) ≤ (C₂ + C₁ * (Real.sqrt 8 + 8)) * (n : ℝ) ^ ((1 : ℝ) / 4) := by
    refine (hu n hn 8 (by norm_num)).trans ?_
    rw [hsq]
    have h1 := hmean n hn
    nlinarith [Real.sqrt_nonneg 8, hC₁.le, hq4]
  -- the recursion
  have hstep := hrec 2 (by norm_num) ν hν n 8 (by norm_num)
  -- the prefactor
  have hpre : ((n : ℝ) + 1) ^ ((1 : ℝ) / 8) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 8) := by
    have h2n : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
    have h1 : ((n : ℝ) + 1) ^ ((1 : ℝ) / 8) ≤ (2 * (n : ℝ)) ^ ((1 : ℝ) / 8) :=
      Real.rpow_le_rpow (by linarith) h2n (by norm_num)
    have h2 : (2 * (n : ℝ)) ^ ((1 : ℝ) / 8)
        = (2 : ℝ) ^ ((1 : ℝ) / 8) * (n : ℝ) ^ ((1 : ℝ) / 8) :=
      Real.mul_rpow (by norm_num) (Nat.cast_nonneg n)
    have h3 : (2 : ℝ) ^ ((1 : ℝ) / 8) ≤ 2 := by
      calc (2 : ℝ) ^ ((1 : ℝ) / 8) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have h4 : (0 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 8) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    calc ((n : ℝ) + 1) ^ ((1 : ℝ) / 8) ≤ (2 * (n : ℝ)) ^ ((1 : ℝ) / 8) := h1
      _ = (2 : ℝ) ^ ((1 : ℝ) / 8) * (n : ℝ) ^ ((1 : ℝ) / 8) := h2
      _ ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 8) := mul_le_mul_of_nonneg_right h3 h4
  have hs8 : Real.sqrt 8 ≤ 8 := by
    have : Real.sqrt 8 ≤ Real.sqrt 64 := Real.sqrt_le_sqrt (by norm_num)
    have h64 : Real.sqrt 64 = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [this, h64.le, h64.ge]
  have hmid : C₀ * ((n : ℝ) + 1) ^ ((1 : ℝ) / 8) *
      (Real.sqrt 8 * A ^ ((1 : ℝ) / 2) + 8)
      ≤ 16 * C₀ * (n : ℝ) ^ ((1 : ℝ) / 8) * (A ^ ((1 : ℝ) / 2) + 1) := by
    have hAh0 : 0 ≤ A ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hA0 _
    have hn8 : (0 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 8) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have h1 : Real.sqrt 8 * A ^ ((1 : ℝ) / 2) + 8 ≤ 8 * (A ^ ((1 : ℝ) / 2) + 1) := by
      nlinarith
    have h2 : C₀ * ((n : ℝ) + 1) ^ ((1 : ℝ) / 8) ≤ C₀ * (2 * (n : ℝ) ^ ((1 : ℝ) / 8)) :=
      mul_le_mul_of_nonneg_left hpre hC₀.le
    calc C₀ * ((n : ℝ) + 1) ^ ((1 : ℝ) / 8) * (Real.sqrt 8 * A ^ ((1 : ℝ) / 2) + 8)
        ≤ (C₀ * (2 * (n : ℝ) ^ ((1 : ℝ) / 8))) * (8 * (A ^ ((1 : ℝ) / 2) + 1)) := by
          refine mul_le_mul h2 h1 ?_ ?_
          · nlinarith [Real.sqrt_nonneg (8 : ℝ)]
          · exact mul_nonneg hC₀.le (by linarith)
      _ = 16 * C₀ * (n : ℝ) ^ ((1 : ℝ) / 8) * (A ^ ((1 : ℝ) / 2) + 1) := by ring
  rw [← hAhalf]
  set Du : ℝ := (∫ ω : Data 2, |uOriented (confReal ω) n 0| ^ (8 : ℝ) ∂(orientedLaw 2 ν)) ^
    ((1 : ℝ) / 8) with hDudef
  have hfinal : A ≤ Du + C₀ * ((n : ℝ) + 1) ^ ((1 : ℝ) / 8) *
      (Real.sqrt 8 * A ^ ((1 : ℝ) / 2) + 8) := hstep
  have hAh0 : 0 ≤ A ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hA0 _
  have hn8 : (0 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 8) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hK1 : (C₂ + C₁ * (Real.sqrt 8 + 8)) * (n : ℝ) ^ ((1 : ℝ) / 4)
      ≤ (C₂ + C₁ * (Real.sqrt 8 + 8) + 16 * C₀) * (n : ℝ) ^ ((1 : ℝ) / 4) :=
    mul_le_mul_of_nonneg_right (by nlinarith [hC₀.le])
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hK2 : 16 * C₀ * (n : ℝ) ^ ((1 : ℝ) / 8) * (A ^ ((1 : ℝ) / 2) + 1)
      ≤ (C₂ + C₁ * (Real.sqrt 8 + 8) + 16 * C₀) * (n : ℝ) ^ ((1 : ℝ) / 8) *
        (A ^ ((1 : ℝ) / 2) + 1) := by
    refine mul_le_mul_of_nonneg_right ?_ (by linarith)
    refine mul_le_mul_of_nonneg_right ?_ hn8
    nlinarith [hC₂.le, hC₁.le, Real.sqrt_nonneg (8 : ℝ)]
  linarith

/-! ### Step 4: the moment inequality at `d ≥ 3` and `r = 2 ∨ ⌈log(n+1)⌉` -/

theorem exists_oriented_hmom (hBern : Parking.External.Bernstein)
    (hConc : Parking.External.UConcentration) (d : ℕ) (hd : 3 ≤ d)
    (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (∫ ω : Data d, (U ω n 0 : ℝ) ^ (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ) ∂(orientedLaw d ν)) ^
          ((1 : ℝ) / (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ)) ≤
        C * Real.log ((n : ℝ) + 1) +
          C * (Real.sqrt ((2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ) *
            (∫ ω : Data d, (U ω n 0 : ℝ) ^ (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ)
              ∂(orientedLaw d ν)) ^
              ((1 : ℝ) / (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ))) +
            (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ)) := by
  haveI := hν.prob
  obtain ⟨C₀, hC₀, hrec⟩ := exists_oriented_U_moment_recursion hBern
  obtain ⟨C₁, hC₁, hu⟩ := exists_oriented_uOriented_norm (d := d) (by omega) hConc ν hν
  obtain ⟨θ, hθ, hexp⟩ := hν.expMoment
  have hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν := by
    obtain ⟨K, hK, hbd⟩ := rpow_le_const_mul_exp (by norm_num : (0:ℝ) ≤ (1:ℝ)) hθ
    refine Integrable.mono' (hexp.const_mul K)
      (measurable_from_countable' (fun k : ℤ => |(k : ℝ)|)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    simpa using hbd _ (abs_nonneg ((k : ℝ)))
  obtain ⟨C₂, hC₂, hmean⟩ :=
    exists_meanuOriented_log_upper (d := d) hd ν hint hν.mean hθ hexp
  refine ⟨C₂ + 7 * C₁ + 3 * C₀, by positivity, fun n hn => ?_⟩
  set L : ℝ := Real.log ((n : ℝ) + 1) with hL
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hL0 : 0 < L := by linarith
  set rn : ℝ := (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ) with hrn
  have hrn2 : (2 : ℝ) ≤ rn := le_max_left _ _
  have hrnL : L ≤ rn := le_trans (Nat.le_ceil L) (le_max_right _ _)
  have hrnub : rn ≤ 2 + L := by
    refine max_le (by linarith) ?_
    have := Nat.ceil_lt_add_one (le_of_lt hL0)
    linarith
  have hrn4 : rn ≤ 4 * L := by linarith
  have hrn0 : (0 : ℝ) ≤ rn := by linarith
  set A : ℝ := (∫ ω : Data d, (U ω n 0 : ℝ) ^ rn ∂(orientedLaw d ν)) ^ ((1 : ℝ) / rn) with hA
  have hI0 : (0 : ℝ) ≤ ∫ ω : Data d, (U ω n 0 : ℝ) ^ rn ∂(orientedLaw d ν) :=
    integral_nonneg fun ω => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hA0 : 0 ≤ A := Real.rpow_nonneg hI0 _
  -- the divisible moment
  have hkappa : orientedKappa d n ≤ 2 * L := by
    rcases eq_or_ne d 3 with h3 | h3
    · subst h3
      have he : orientedKappa 3 n = L := by simp [orientedKappa, hL]
      rw [he]; linarith
    · have he : orientedKappa d n = 1 := by
        rw [orientedKappa, if_neg (show d ≠ 2 by omega), if_neg h3]
      rw [he]; linarith
  have hsq : Real.sqrt (rn * orientedKappa d n) ≤ 3 * L := by
    have h1 : rn * orientedKappa d n ≤ (4 * L) * (2 * L) :=
      mul_le_mul hrn4 hkappa (orientedKappa_nonneg d n) (by linarith)
    have h2 : Real.sqrt (rn * orientedKappa d n) ≤ Real.sqrt ((4 * L) * (2 * L)) :=
      Real.sqrt_le_sqrt h1
    have h3 : Real.sqrt ((4 * L) * (2 * L)) ≤ 3 * L := by
      rw [show (4 * L) * (2 * L) = (3 * L) ^ 2 - L ^ 2 by ring]
      have : Real.sqrt ((3 * L) ^ 2 - L ^ 2) ≤ Real.sqrt ((3 * L) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
      rwa [Real.sqrt_sq (by linarith)] at this
    linarith
  have hDu : (∫ ω : Data d, |uOriented (confReal ω) n 0| ^ rn ∂(orientedLaw d ν)) ^
      ((1 : ℝ) / rn) ≤ (C₂ + 7 * C₁) * L := by
    refine (hu n hn rn hrn2).trans ?_
    have h1 := hmean n hn
    rw [← hL] at h1
    nlinarith [hC₁.le]
  -- the prefactor
  have hpre : ((n : ℝ) + 1) ^ ((1 : ℝ) / rn) ≤ 3 := by
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hle : Real.log ((n : ℝ) + 1) * (1 / rn) ≤ 1 := by
      rw [mul_one_div, div_le_one (by linarith)]
      exact hrnL
    rw [Real.rpow_def_of_pos hpos]
    calc Real.exp (Real.log ((n : ℝ) + 1) * (1 / rn)) ≤ Real.exp 1 :=
          Real.exp_le_exp.mpr hle
      _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hstep := hrec d (by omega) ν hν n rn hrn2
  have hsqrtA : Real.sqrt rn * A ^ ((1 : ℝ) / 2) = Real.sqrt (rn * A) := by
    rw [Real.sqrt_mul hrn0, Real.sqrt_eq_rpow A]
  have hmid : C₀ * ((n : ℝ) + 1) ^ ((1 : ℝ) / rn) * (Real.sqrt rn * A ^ ((1 : ℝ) / 2) + rn)
      ≤ 3 * C₀ * (Real.sqrt (rn * A) + rn) := by
    rw [hsqrtA]
    have h0 : (0 : ℝ) ≤ Real.sqrt (rn * A) + rn := by
      have := Real.sqrt_nonneg (rn * A); linarith
    have h1 : C₀ * ((n : ℝ) + 1) ^ ((1 : ℝ) / rn) ≤ C₀ * 3 :=
      mul_le_mul_of_nonneg_left hpre hC₀.le
    nlinarith
  have hK1 : (C₂ + 7 * C₁) * L ≤ (C₂ + 7 * C₁ + 3 * C₀) * L := by nlinarith [hC₀.le]
  have hK2 : 3 * C₀ * (Real.sqrt (rn * A) + rn)
      ≤ (C₂ + 7 * C₁ + 3 * C₀) * (Real.sqrt (rn * A) + rn) := by
    refine mul_le_mul_of_nonneg_right ?_ (by linarith [Real.sqrt_nonneg (rn * A)])
    nlinarith [hC₁.le, hC₂.le]
  linarith [hstep, hDu, hmid]

end Parking
end
