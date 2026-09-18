/-
The moments of every order that `prop:w-moment` needs.

The paper's remark after `eq:apriori-finite` is that "whenever `η(0)⁺` has an
exponential moment, the finite sum on the right has moments of every order".
That is what this module proves, in the three steps the remark hides.

- A power is dominated by an exponential on the half line:
  `t^r ≤ C exp(θ t)` for `t ≥ 0`, with `C` depending on `r` and `θ`.  The proof
  is `1 + s/n ≤ e^{s/n}` raised to the power `n`, which gives `(s/n)^n ≤ e^s`
  with no series and no Stirling.
- The configuration at one site has the law `ν`, so the exponential moment of
  the statement is an exponential moment of every coordinate.
- The sum over a box is bounded by the box's cardinality times the average, and
  the power of an average is at most the average of the powers, so a finite sum
  of coordinates has moments of every order too.

Everything the proof of `prop:w-moment` integrates is then dominated by such a
sum: the odometer by `eq:apriori-finite`, and the error and its maximal average
by the pathwise bound of `Parking/Support/WBound.lean`.
-/
import Parking.Support.WBound

noncomputable section

namespace Parking

open LatticeProb Finset MeasureTheory

variable {d : ℕ}

/-! ### A power is dominated by an exponential -/

/-- **`t^r ≤ C e^{θ t}` on the half line.**  The witness comes from
`1 + s/n ≤ e^{s/n}` raised to the power `n`. -/
theorem rpow_le_const_mul_exp {r θ : ℝ} (hr : 0 ≤ r) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → t ^ r ≤ C * Real.exp (θ * t) := by
  set n : ℕ := ⌈r⌉₊ + 1 with hn
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hrn : r ≤ (n : ℝ) := by
    have h1 : r ≤ (⌈r⌉₊ : ℝ) := Nat.le_ceil r
    have h2 : ((⌈r⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
      have : (⌈r⌉₊ : ℕ) ≤ n := by omega
      exact_mod_cast this
    linarith
  -- the polynomial bound
  have hpoly : ∀ t : ℝ, 0 ≤ t → t ^ n ≤ ((n : ℝ) / θ) ^ n * Real.exp (θ * t) := by
    intro t ht
    have hs : (0 : ℝ) ≤ θ * t := by positivity
    have hstep : (θ * t / (n : ℝ)) ^ n ≤ Real.exp (θ * t) := by
      have h1 : θ * t / (n : ℝ) + 1 ≤ Real.exp (θ * t / (n : ℝ)) :=
        Real.add_one_le_exp _
      have h2 : (0 : ℝ) ≤ θ * t / (n : ℝ) := by positivity
      have h3 : (θ * t / (n : ℝ)) ^ n ≤ (θ * t / (n : ℝ) + 1) ^ n :=
        pow_le_pow_left₀ h2 (by linarith) n
      have h4 : (θ * t / (n : ℝ) + 1) ^ n ≤ (Real.exp (θ * t / (n : ℝ))) ^ n :=
        pow_le_pow_left₀ (by linarith) h1 n
      have h5 : (Real.exp (θ * t / (n : ℝ))) ^ n = Real.exp (θ * t) := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp
      linarith [h3, h4, h5.le, h5.ge]
    have hmul : ((n : ℝ) / θ) ^ n * (θ * t / (n : ℝ)) ^ n = t ^ n := by
      rw [← mul_pow]
      congr 1
      field_simp
    calc t ^ n = ((n : ℝ) / θ) ^ n * (θ * t / (n : ℝ)) ^ n := hmul.symm
      _ ≤ ((n : ℝ) / θ) ^ n * Real.exp (θ * t) := by
          refine mul_le_mul_of_nonneg_left hstep ?_
          positivity
  refine ⟨1 + ((n : ℝ) / θ) ^ n, by positivity, fun t ht => ?_⟩
  have hrpow : t ^ r ≤ 1 + t ^ n := by
    rcases le_total t 1 with h1 | h1
    · have hA : t ^ r ≤ 1 := Real.rpow_le_one ht h1 hr
      have hB : (0 : ℝ) ≤ t ^ n := by positivity
      linarith
    · have h2 : t ^ r ≤ t ^ ((n : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 hrn
      rw [Real.rpow_natCast] at h2
      linarith
  have hexp1 : (1 : ℝ) ≤ Real.exp (θ * t) := Real.one_le_exp (by positivity)
  have hcoef : (0 : ℝ) ≤ ((n : ℝ) / θ) ^ n := by positivity
  calc t ^ r ≤ 1 + t ^ n := hrpow
    _ ≤ 1 * Real.exp (θ * t) + ((n : ℝ) / θ) ^ n * Real.exp (θ * t) := by
        have := hpoly t ht
        linarith
    _ = (1 + ((n : ℝ) / θ) ^ n) * Real.exp (θ * t) := by ring

/-! ### The law of one coordinate of the configuration -/

theorem law_map_conf_eval (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (z : Site d) :
    (law d ν).map (fun ω : Data d => ω.1 z) = ν := by
  haveI := stackRankLaw_isProbability (d := d) hd
  have h1 : (fun ω : Data d => ω.1 z)
      = (fun η : Site d → ℤ => η z) ∘ (Prod.fst : Data d → (Site d → ℤ)) := rfl
  rw [h1, ← Measure.map_map (measurable_pi_apply z) measurable_fst]
  have h2 : (law d ν).map (Prod.fst : Data d → (Site d → ℤ)) = LatticeProb.iidLaw d ν := by
    have hlaw : law d ν = (LatticeProb.iidLaw d ν).prod (stackRankLaw d) := rfl
    rw [hlaw]
    exact Measure.fst_prod (μ := LatticeProb.iidLaw d ν) (ν := stackRankLaw d)
  rw [h2, LatticeProb.iidLaw, Measure.infinitePi_map_eval]

/-! ### Moments of every order at one site -/

theorem toNat_cast_eq_max (k : ℤ) : (((k.toNat : ℕ) : ℝ)) = max (k : ℝ) 0 := by
  rcases le_total 0 k with h | h
  · rw [max_eq_left (show (0 : ℝ) ≤ (k : ℝ) by exact_mod_cast h)]
    have hk : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg h
    exact_mod_cast congrArg (fun m : ℤ => (m : ℝ)) hk
  · rw [max_eq_right (show ((k : ℝ)) ≤ 0 by exact_mod_cast h),
      Int.toNat_of_nonpos h]
    norm_num

theorem integrable_conf_rpow (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν)
    {r : ℝ} (hr : 0 ≤ r) (z : Site d) :
    Integrable (fun ω : Data d => (((ω.1 z).toNat : ℕ) : ℝ) ^ r) (law d ν) := by
  obtain ⟨C, hC, hbound⟩ := rpow_le_const_mul_exp hr hθ
  have hg : Integrable (fun k : ℤ => (((k.toNat : ℕ) : ℝ)) ^ r) ν := by
    refine Integrable.mono' (hexp.const_mul C)
      (measurable_from_countable' (fun k : ℤ => (((k.toNat : ℕ) : ℝ)) ^ r)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => ?_)
    have h0 : (0 : ℝ) ≤ (((k.toNat : ℕ) : ℝ)) := Nat.cast_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 r), toNat_cast_eq_max]
    exact hbound _ (le_max_right _ _)
  have hmap := law_map_conf_eval hd ν z
  have hmeas : AEMeasurable (fun ω : Data d => ω.1 z) (law d ν) :=
    ((measurable_pi_apply z).comp measurable_fst).aemeasurable
  have hg2 : Integrable (fun k : ℤ => (((k.toNat : ℕ) : ℝ)) ^ r)
      ((law d ν).map (fun ω : Data d => ω.1 z)) := by
    rw [hmap]; exact hg
  exact hg2.comp_aemeasurable hmeas

/-! ### Moments of every order of the configuration over a box -/

theorem measurable_confBoxNat (x : Site d) (R : ℕ) :
    Measurable fun ω : Data d => (∑ z ∈ boxFinset x R, (ω.1 z).toNat : ℕ) :=
  Finset.measurable_sum _ fun z _ =>
    (measurable_from_countable' fun k : ℤ => k.toNat).comp
      ((measurable_pi_apply z).comp measurable_fst)

theorem measurable_confBox (x : Site d) (R : ℕ) :
    Measurable fun ω : Data d => confBox ω x R :=
  (measurable_from_countable' fun m : ℕ => (m : ℝ)).comp (measurable_confBoxNat x R)

/-- **The power of a sum against the sum of the powers.**  The average of the
terms raised to the power `p ≥ 1` is at most the average of the powers. -/
theorem rpow_sum_le {ι : Type} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hs : s.Nonempty) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ s, a i) ^ p ≤ (s.card : ℝ) ^ p * ∑ i ∈ s, a i ^ p := by
  classical
  have hcard : (0 : ℝ) < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  set N : ℝ := (s.card : ℝ) with hN
  have hw : ∀ i ∈ s, (0 : ℝ) ≤ 1 / N := fun i _ => by positivity
  have hw' : ∑ _i ∈ s, (1 : ℝ) / N = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, ← hN]
    field_simp
  have hjensen := Real.rpow_arith_mean_le_arith_mean_rpow s (fun _ => 1 / N) a hw hw' ha hp
  have hL : ∑ i ∈ s, (1 / N) * a i = (1 / N) * ∑ i ∈ s, a i := by
    rw [Finset.mul_sum]
  have hR : ∑ i ∈ s, (1 / N) * a i ^ p = (1 / N) * ∑ i ∈ s, a i ^ p := by
    rw [Finset.mul_sum]
  rw [hL, hR] at hjensen
  have hsum0 : (0 : ℝ) ≤ ∑ i ∈ s, a i := Finset.sum_nonneg ha
  have hsplit : ((1 : ℝ) / N * ∑ i ∈ s, a i) ^ p = (1 / N) ^ p * (∑ i ∈ s, a i) ^ p :=
    Real.mul_rpow (by positivity) hsum0
  rw [hsplit] at hjensen
  have hNp : (0 : ℝ) < N ^ p := Real.rpow_pos_of_pos hcard p
  have hinv : (1 / N) ^ p = (N ^ p)⁻¹ := by
    rw [one_div, Real.inv_rpow (le_of_lt hcard)]
  rw [hinv] at hjensen
  have hmul := mul_le_mul_of_nonneg_left hjensen (le_of_lt hNp)
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hNp), one_mul] at hmul
  refine le_trans hmul ?_
  have hsumnn : (0 : ℝ) ≤ ∑ i ∈ s, a i ^ p :=
    Finset.sum_nonneg fun i hi => Real.rpow_nonneg (ha i hi) p
  have hle : N ^ p * (1 / N * ∑ i ∈ s, a i ^ p) ≤ N ^ p * ∑ i ∈ s, a i ^ p := by
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hNp)
    have h1N : (1 : ℝ) / N ≤ 1 := by
      rw [div_le_one hcard, hN]
      have : (1 : ℕ) ≤ s.card := Finset.card_pos.mpr hs
      exact_mod_cast this
    nlinarith
  exact hle

theorem integrable_confBox_rpow (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν)
    {r : ℝ} (hr : 1 ≤ r) (x : Site d) (R : ℕ) :
    Integrable (fun ω : Data d => confBox ω x R ^ r) (law d ν) := by
  classical
  have hne : (boxFinset x R).Nonempty := ⟨x, by
    rw [mem_boxFinset_iff]; intro i; simp⟩
  have hdom : Integrable (fun ω : Data d =>
      ((boxFinset x R).card : ℝ) ^ r *
        ∑ z ∈ boxFinset x R, (((ω.1 z).toNat : ℕ) : ℝ) ^ r) (law d ν) := by
    refine Integrable.const_mul ?_ _
    exact integrable_finsetSum _ fun z _ =>
      integrable_conf_rpow hd ν hθ hexp (le_trans zero_le_one hr) z
  have hmeas : Measurable fun ω : Data d => confBox ω x R ^ r := by
    have heq : (fun ω : Data d => confBox ω x R ^ r)
        = (fun m : ℕ => ((m : ℝ)) ^ r)
          ∘ (fun ω : Data d => (∑ z ∈ boxFinset x R, (ω.1 z).toNat : ℕ)) := rfl
    rw [heq]
    exact (measurable_from_countable' _).comp (measurable_confBoxNat x R)
  refine Integrable.mono' hdom hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  have hexpand : confBox ω x R = ∑ z ∈ boxFinset x R, (((ω.1 z).toNat : ℕ) : ℝ) := by
    rw [confBox]; push_cast; ring
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (confBox_nonneg ω x R) r), hexpand]
  exact rpow_sum_le _ _ (fun z _ => Nat.cast_nonneg _) hne hr

end Parking

end
