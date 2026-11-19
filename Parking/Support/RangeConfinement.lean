import Parking.Support.RangeBoxIteration
import Parking.Support.TailRangeBounds
import LatticeProb.Walk.Shells

/-!
# Confinement and the range moment

Repeated returns to a finite box give a lower bound on the exponential moment
of the random-walk range.
-/

open MeasureTheory

noncomputable section

namespace Parking

variable {d : ℕ}

/-- A uniform box-block probability yields a lower bound for the range moment
at every time covered by the blocks. -/
theorem exp_mul_pow_le_rangeExp_of_boxBlocks (hd : 1 ≤ d) {a : ℝ} (ha : 0 ≤ a)
    (n j t L : ℕ) (c : ℝ) (hc : 0 ≤ c) (ht : t ≤ j * n)
    (hblock : ∀ y : Site d, (∀ i, |(y i : ℝ)| ≤ (L : ℝ)) →
      c ≤ (LatticeProb.siteWalkLaw d y).real (boxBlock n L)) :
    Real.exp (-(a * (((4 * L + 1 : ℕ) ^ d : ℕ) : ℝ))) * c ^ j ≤ rangeExp d a t := by
  have : NeZero d := ⟨by omega⟩
  let B : Finset (Site d) := LatticeProb.boxFinset 0 (2 * L)
  have hsub : boxBlock (j * n) (L : ℝ) ⊆
      {X : ℕ → Site d | ∀ k ≤ t, X k ∈ B} := by
    intro X hX k hk
    apply LatticeProb.mem_boxFinset_iff.mpr
    intro i
    have hbound := hX.1 k (le_trans hk ht) i
    have hreal : |(X k i : ℝ)| ≤ ((2 * L : ℕ) : ℝ) := by
      push_cast
      exact hbound
    have hint : |X k i| ≤ ((2 * L : ℕ) : ℤ) := by exact_mod_cast hreal
    simpa [B] using hint
  have hpow : c ^ j ≤ (LatticeProb.siteWalkLaw d 0).real (boxBlock (j * n) (L : ℝ)) :=
    pow_le_measureReal_boxBlock_mul hd n L c (by positivity) hc hblock j 0 (by simp)
  have hprob := measureReal_mono (μ := LatticeProb.siteWalkLaw d 0) hsub (measure_ne_top _ _)
  have hcard : B.card = (4 * L + 1) ^ d := by
    rw [show B = LatticeProb.boxFinset (0 : Site d) (2 * L) from rfl,
      LatticeProb.card_boxFinset_zero]
    congr 1
    omega
  have hconf := rangeExp_ge_exp_mul_confinement_probability hd ha B t
  rw [hcard] at hconf
  exact (mul_le_mul_of_nonneg_left (hpow.trans hprob) (Real.exp_nonneg _)).trans hconf

/-- A box of radius proportional to `d * k` and blocks of length `2 * k²`
give an explicit lower bound for the range moment. -/
theorem exp_mul_pow_le_rangeExp (hd : 1 ≤ d) {a : ℝ} (ha : 0 ≤ a)
    (k t : ℕ) (hk : 1 ≤ k) :
    Real.exp (-(a * (((8 * d * k + 1 : ℕ) ^ d : ℕ) : ℝ))) *
      ((2 * (2 : ℝ) ^ d)⁻¹) ^ (t / (2 * k ^ 2) + 1) ≤ rangeExp d a t := by
  let n : ℕ := 2 * k ^ 2
  let L : ℕ := 2 * d * k
  let j : ℕ := t / n + 1
  let c : ℝ := (2 * (2 : ℝ) ^ d)⁻¹
  have hn : 1 ≤ n := by dsimp [n]; nlinarith
  have ht : t ≤ j * n := by
    have hmod := Nat.mod_lt t (by omega : 0 < n)
    have hdiv := Nat.div_add_mod t n
    dsimp [j]
    nlinarith
  have hr : 0 < 2 * (k : ℝ) := by exact_mod_cast (show 0 < 2 * k by omega)
  have hnreal : (n : ℝ) ≤ (2 * (k : ℝ)) ^ 2 / 2 := by
    dsimp [n]
    push_cast
    ring_nf
    rfl
  have hL : (d : ℝ) * (2 * (k : ℝ)) ≤ (L : ℝ) := by
    dsimp [L]
    push_cast
    ring_nf
    rfl
  have hpow : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hblock : ∀ y : Site d, (∀ i, |(y i : ℝ)| ≤ (L : ℝ)) →
      c ≤ (LatticeProb.siteWalkLaw d y).real (boxBlock n L) := by
    intro y hy
    have h := half_le_pow_mul_measureReal_boxBlock hd n y hr hnreal hL hy
    have heq : c = (1 / 2 : ℝ) / (2 : ℝ) ^ d := by
      dsimp [c]
      field_simp
    rw [heq, div_le_iff₀ hpow]
    simpa [mul_comm] using h
  have h := exp_mul_pow_le_rangeExp_of_boxBlocks hd ha n j t L c hc ht hblock
  have hL' : 4 * L + 1 = 8 * d * k + 1 := by dsimp [L]; ring
  rw [hL'] at h
  simpa only [n, j, c] using h

/-- The radius and block count can be chosen so that both costs have the
stretched-exponential scale `t ^ (d / (d + 2))`. -/
theorem range_moment_lower_bound : RangeMomentLowerBound := by
  intro d hd a ha
  let β : ℝ := 1 / ((d : ℝ) + 2)
  let α : ℝ := (d : ℝ) / ((d : ℝ) + 2)
  let c : ℝ := (2 * (2 : ℝ) ^ d)⁻¹
  let b : ℝ := -Real.log c
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (0 : ℝ) < (d : ℝ) + 2 := by linarith
  have hβ : 0 < β := by dsimp [β]; positivity
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    exact (inv_le_one₀ (by positivity)).2 (by linarith)
  have hb : 0 ≤ b := by dsimp [b]; linarith [Real.log_nonpos hc.le hc1]
  let K : ℝ := a * (16 * (d : ℝ) + 1) ^ d + 2 * b + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, 1, hK, le_rfl, fun t ht => ?_⟩
  have hT : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hTpos : (0 : ℝ) < t := by linarith
  let x : ℝ := (t : ℝ) ^ β
  let k : ℕ := ⌈x⌉₊
  let j : ℕ := t / (2 * k ^ 2) + 1
  have hx : 1 ≤ x := by dsimp [x]; exact Real.one_le_rpow hT hβ.le
  have hxk : x ≤ (k : ℝ) := Nat.le_ceil x
  have hk : 1 ≤ k := by
    have : (1 : ℝ) ≤ k := hx.trans hxk
    exact_mod_cast this
  have hk2 : (k : ℝ) ≤ 2 * x := by
    have h := Nat.ceil_lt_add_one (le_trans zero_le_one hx)
    dsimp [k]
    linarith
  have hpow : x ^ d = (t : ℝ) ^ α := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hTpos.le]
    congr 1
    dsimp [α, β]
    field_simp
  have hscale : x ^ 2 * (t : ℝ) ^ α = (t : ℝ) := by
    have hexp : β * 2 + α = 1 := by
      dsimp [α, β]
      field_simp; ring
    calc x ^ 2 * (t : ℝ) ^ α = (t : ℝ) ^ (β * 2) * (t : ℝ) ^ α := by
          dsimp [x]
          rw [← Real.rpow_natCast, ← Real.rpow_mul hTpos.le]
          norm_num
      _ = (t : ℝ) ^ (β * 2 + α) := (Real.rpow_add hTpos _ _).symm
      _ = (t : ℝ) := by rw [hexp, Real.rpow_one]
  have hαone : 1 ≤ (t : ℝ) ^ α := Real.one_le_rpow hT hα
  have hαnonneg : 0 ≤ (t : ℝ) ^ α := le_trans zero_le_one hαone
  have hsq : x ^ 2 ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hxk 2
  have hTbound : (t : ℝ) ≤ (2 * (k : ℝ) ^ 2) * (t : ℝ) ^ α := by
    have hm := mul_le_mul_of_nonneg_right hsq hαnonneg
    have hs : 0 ≤ (k : ℝ) ^ 2 * (t : ℝ) ^ α := mul_nonneg (sq_nonneg _) hαnonneg
    nlinarith [hscale, hm, hs]
  have hdiv : (t : ℝ) / (2 * (k : ℝ) ^ 2) ≤ (t : ℝ) ^ α := by
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
    exact (div_le_iff₀ (by positivity)).2 (by simpa only [mul_comm] using hTbound)
  have hj : (j : ℝ) ≤ 2 * (t : ℝ) ^ α := by
    have hcast : ((t / (2 * k ^ 2) : ℕ) : ℝ) ≤
        (t : ℝ) / (2 * (k : ℝ) ^ 2) := by
      have h := Nat.cast_div_le (α := ℝ) (m := t) (n := 2 * k ^ 2)
      push_cast at h
      exact h
    dsimp [j]
    push_cast
    linarith
  have hbase : (0 : ℝ) ≤ 8 * (d : ℝ) * (k : ℝ) + 1 := by positivity
  have hbase_le : 8 * (d : ℝ) * (k : ℝ) + 1 ≤ (16 * (d : ℝ) + 1) * x := by
    have hm := mul_le_mul_of_nonneg_left hk2 (show (0 : ℝ) ≤ 8 * (d : ℝ) by positivity)
    nlinarith
  have hcard : (((8 * d * k + 1 : ℕ) ^ d : ℕ) : ℝ) ≤
      (16 * (d : ℝ) + 1) ^ d * (t : ℝ) ^ α := by
    have hp := pow_le_pow_left₀ hbase hbase_le d
    rw [mul_pow, hpow] at hp
    push_cast
    exact hp
  have hcost : a * (((8 * d * k + 1 : ℕ) ^ d : ℕ) : ℝ) + b * (j : ℝ) ≤
      K * (t : ℝ) ^ α := by
    have h₁ := mul_le_mul_of_nonneg_left hcard ha.le
    have h₂ := mul_le_mul_of_nonneg_left hj hb
    dsimp [K]
    nlinarith
  have hpowc : c ^ j = Real.exp (-(b * (j : ℝ))) := by
    dsimp [b]
    rw [neg_mul, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hc]
  have hbound := exp_mul_pow_le_rangeExp hd ha.le k t hk
  change Real.exp (-(a * (((8 * d * k + 1 : ℕ) ^ d : ℕ) : ℝ))) * c ^ j ≤ _ at hbound
  rw [hpowc, ← Real.exp_add] at hbound
  simp only [one_mul]
  calc Real.exp (-(K * (t : ℝ) ^ α)) ≤
      Real.exp (-(a * (((8 * d * k + 1 : ℕ) ^ d : ℕ) : ℝ)) + -(b * (j : ℝ))) := by
        apply Real.exp_le_exp.mpr
        linarith
    _ ≤ rangeExp d a t := hbound

/-- The lower subcritical tail bound follows from box confinement. -/
theorem exists_lower_tail_of_confinement (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k, (k : ℝ) ∂ν < 0) (hpos : 0 < ν (Set.Ioi (0 : ℤ)))
    {θ : ℝ} (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧ ∀ t : ℕ, 1 ≤ t →
      C⁻¹ * Real.exp (-(K * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)))) ≤ S (law d ν) t :=
  exists_lower_tail_of_range_moment hd (range_moment_lower_bound d hd) hint hmean hpos hθ hexp

/-- The upper range moment estimate alone implies both subcritical tail bounds. -/
theorem exists_tail_bounds_of_upper_range_moment (hd : 1 ≤ d)
    (hUpper : ∀ a : ℝ, 0 < a → ∃ c C : ℝ, 0 < c ∧ 1 ≤ C ∧
      ∀ t : ℕ, 1 ≤ t →
        rangeExp d a t ≤ C * Real.exp (-(c * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)))))
    {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k, (k : ℝ) ∂ν < 0) (hpos : 0 < ν (Set.Ioi (0 : ℤ)))
    {θ : ℝ} (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ t : ℕ, 1 ≤ t →
      C⁻¹ * Real.exp (-(C * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)))) ≤ S (law d ν) t ∧
        S (law d ν) t ≤ C * Real.exp (-(c * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)))) := by
  obtain ⟨K, C₁, _, hC₁, hlow⟩ :=
    exists_lower_tail_of_confinement hd hint hmean hpos hθ hexp
  obtain ⟨c, C₂, hc, _, hup⟩ :=
    exists_upper_tail_of_range_moment hd hUpper hint hmean hθ hexp
  exact two_sided_combine hC₁ hc hlow hup

/-- Both subcritical tail bounds hold without a range hypothesis in dimension one. -/
theorem exists_tail_bounds_one {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k, (k : ℝ) ∂ν < 0) (hpos : 0 < ν (Set.Ioi (0 : ℤ)))
    {θ : ℝ} (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ t : ℕ, 1 ≤ t →
      C⁻¹ * Real.exp (-(C * (t : ℝ) ^ ((1 : ℝ) / 3))) ≤ S (law 1 ν) t ∧
        S (law 1 ν) t ≤ C * Real.exp (-(c * (t : ℝ) ^ ((1 : ℝ) / 3))) := by
  obtain ⟨K, C₁, _, hC₁, hlow⟩ :=
    exists_lower_tail_of_confinement (d := 1) (by norm_num) hint hmean hpos hθ hexp
  have hr : ((1 : ℕ) : ℝ) / (((1 : ℕ) : ℝ) + 2) = (1 : ℝ) / 3 := by norm_num
  rw [hr] at hlow
  obtain ⟨c, C₂, hc, _, hup⟩ := exists_upper_tail_one hint hmean hθ hexp
  exact two_sided_combine hC₁ hc hlow hup

end Parking

end
