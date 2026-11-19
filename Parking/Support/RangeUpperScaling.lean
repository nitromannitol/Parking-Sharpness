import Parking.Support.RangeConnected
import Parking.Support.RangeConfinement

/-!
# Scaling of the small-range estimate

A block length proportional to the square of a spatial scale controls the
heat-kernel factor for ranges of comparable volume.
-/

open MeasureTheory LatticeProb

noncomputable section

namespace Parking

variable {d : ℕ}

/-- A quadratic block length makes the heat-kernel factor small for a range of
at most twice the `d`-dimensional volume of the scale. -/
theorem exists_range_block_scale (hd : 1 ≤ d) : ∃ Q : ℕ, 1 ≤ Q ∧ ∀ m k : ℕ, 1 ≤ k →
    (m : ℝ) ≤ 2 * (k : ℝ) ^ d →
      (m : ℝ) * (Real.sqrt 2 ^ d * greenConst d *
        ((Q * k ^ 2 : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) ≤ 1 / 2 := by
  let C : ℝ := Real.sqrt 2 ^ d * greenConst d
  have hC : 0 ≤ C := mul_nonneg (by positivity) (greenConst_nonneg d)
  obtain ⟨q, hq⟩ := exists_nat_ge ((4 * C) ^ 2)
  let Q := q + 1
  have hQ1 : (1 : ℝ) ≤ Q := by dsimp [Q]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  have hQpos : (0 : ℝ) < Q := by linarith
  have hQsq : (4 * C) ^ 2 ≤ (Q : ℝ) := by dsimp [Q]; push_cast; linarith
  have hQsqrt : 4 * C ≤ Real.sqrt (Q : ℝ) := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 4 * C)]
    exact Real.sqrt_le_sqrt hQsq
  have hQpow : Real.sqrt (Q : ℝ) ≤ (Q : ℝ) ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    apply Real.rpow_le_rpow_of_exponent_le hQ1
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hQfactor : (4 * C) * (Q : ℝ) ^ (-(d : ℝ) / 2) ≤ 1 := by
    have hpow : 0 ≤ (Q : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg hQpos.le _
    calc (4 * C) * (Q : ℝ) ^ (-(d : ℝ) / 2)
        ≤ (Q : ℝ) ^ ((d : ℝ) / 2) * (Q : ℝ) ^ (-(d : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right (hQsqrt.trans hQpow) hpow
      _ = 1 := by
        rw [← Real.rpow_add hQpos, show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring,
          Real.rpow_zero]
  refine ⟨Q, by dsimp [Q]; omega, fun m k hk hm => ?_⟩
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hkpow : (0 : ℝ) < (k : ℝ) ^ d := pow_pos hkpos _
  have hdec : (((Q * k ^ 2 : ℕ) : ℝ)) ^ (-(d : ℝ) / 2) =
      (Q : ℝ) ^ (-(d : ℝ) / 2) * ((k : ℝ) ^ d)⁻¹ := by
    push_cast
    rw [Real.mul_rpow hQpos.le (sq_nonneg _), ← Real.rpow_natCast (k : ℝ) 2,
      ← Real.rpow_mul hkpos.le]
    have he : ((2 : ℕ) : ℝ) * (-(d : ℝ) / 2) = -(d : ℝ) := by push_cast; ring
    rw [he, Real.rpow_neg hkpos.le, Real.rpow_natCast]
  rw [hdec]
  have hnonneg : 0 ≤ C * ((Q : ℝ) ^ (-(d : ℝ) / 2) * ((k : ℝ) ^ d)⁻¹) := by positivity
  calc (m : ℝ) * (C * ((Q : ℝ) ^ (-(d : ℝ) / 2) * ((k : ℝ) ^ d)⁻¹))
      ≤ (2 * (k : ℝ) ^ d) *
          (C * ((Q : ℝ) ^ (-(d : ℝ) / 2) * ((k : ℝ) ^ d)⁻¹)) :=
        mul_le_mul_of_nonneg_right hm hnonneg
    _ = ((4 * C) * (Q : ℝ) ^ (-(d : ℝ) / 2)) / 2 := by
      field_simp; ring
    _ ≤ 1 / 2 := by linarith

private theorem exponential_range_cost {a ε b c z w : ℝ} {K m j : ℕ}
    (ha : 0 ≤ a) (hε : 0 ≤ ε) (hc : 0 ≤ c) (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hK : (0 : ℝ) < K) (hlo : ε * z ≤ m) (hwz : w ≤ z)
    (hcb : c ≤ b) (hca : c ≤ a * ε)
    (hcost : (Real.log K + 1) * (m : ℝ) - Real.log 2 * (j : ℝ) ≤
      (Real.log K + 1) + Real.log 2 - b * z) :
    (m : ℝ) * (K : ℝ) ^ m * (1 / 2 : ℝ) ^ j + Real.exp (-(a * (m : ℝ))) ≤
      (Real.exp ((Real.log K + 1) + Real.log 2) + 1) * Real.exp (-(c * w)) := by
  have hmexp : (m : ℝ) * (K : ℝ) ^ m ≤ Real.exp ((Real.log K + 1) * (m : ℝ)) := by
    have hm : (m : ℝ) ≤ Real.exp (m : ℝ) := by
      linarith [Real.add_one_le_exp (m : ℝ)]
    have hKexp : (K : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log K) := by
      rw [Real.exp_nat_mul, Real.exp_log hK]
    rw [hKexp]
    calc (m : ℝ) * Real.exp ((m : ℝ) * Real.log K)
        ≤ Real.exp (m : ℝ) * Real.exp ((m : ℝ) * Real.log K) :=
          mul_le_mul_of_nonneg_right hm (Real.exp_nonneg _)
      _ = Real.exp ((Real.log K + 1) * (m : ℝ)) := by
          rw [← Real.exp_add]
          congr 1
          ring
  have hhalf : (1 / 2 : ℝ) ^ j = Real.exp (-(Real.log 2 * (j : ℝ))) := by
    rw [show -(Real.log 2 * (j : ℝ)) = (j : ℝ) * (-Real.log 2) by ring,
      Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hcw : c * w ≤ b * z :=
    (mul_le_mul_of_nonneg_left hwz hc).trans (mul_le_mul_of_nonneg_right hcb hz)
  have hfirst : (m : ℝ) * (K : ℝ) ^ m * (1 / 2 : ℝ) ^ j ≤
      Real.exp ((Real.log K + 1) + Real.log 2) * Real.exp (-(c * w)) := by
    calc (m : ℝ) * (K : ℝ) ^ m * (1 / 2 : ℝ) ^ j
        ≤ Real.exp ((Real.log K + 1) * (m : ℝ)) * (1 / 2 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hmexp (by positivity)
      _ = Real.exp ((Real.log K + 1) * (m : ℝ) - Real.log 2 * (j : ℝ)) := by
          rw [hhalf, ← Real.exp_add]
          congr 1
      _ ≤ Real.exp ((Real.log K + 1) + Real.log 2 - c * w) := by
          apply Real.exp_le_exp.mpr
          linarith only [hcost, hcw]
      _ = Real.exp ((Real.log K + 1) + Real.log 2) * Real.exp (-(c * w)) := by
          rw [← Real.exp_add]
          congr 1
  have hca' : c * w ≤ a * (m : ℝ) := by
    calc c * w ≤ (a * ε) * w := mul_le_mul_of_nonneg_right hca hw
      _ ≤ (a * ε) * z := mul_le_mul_of_nonneg_left hwz (mul_nonneg ha hε)
      _ = a * (ε * z) := by ring
      _ ≤ a * (m : ℝ) := mul_le_mul_of_nonneg_left hlo ha
  have hsecond : Real.exp (-(a * (m : ℝ))) ≤ Real.exp (-(c * w)) :=
    Real.exp_le_exp.mpr (neg_le_neg hca')
  calc (m : ℝ) * (K : ℝ) ^ m * (1 / 2 : ℝ) ^ j + Real.exp (-(a * (m : ℝ)))
      ≤ Real.exp ((Real.log K + 1) + Real.log 2) * Real.exp (-(c * w)) +
          Real.exp (-(c * w)) := add_le_add hfirst hsecond
    _ = (Real.exp ((Real.log K + 1) + Real.log 2) + 1) * Real.exp (-(c * w)) := by ring

/-- The upper range-moment estimate obtained from finite-set confinement and
the exponential count of connected ranges; see Kesten, *Percolation Theory for
Mathematicians* (1982), p. 85, for the connected-set count. -/
theorem range_moment_upper_bound_of_range_count : RangeMomentUpperBound := by
  intro d hd a ha
  obtain ⟨K, hK, hmoment⟩ := exists_rangeExp_upper_of_smallRange (d := d) hd
  obtain ⟨Q, hQ, hblock⟩ := exists_range_block_scale (d := d) hd
  let β : ℝ := 1 / ((d : ℝ) + 2)
  let α : ℝ := (d : ℝ) / ((d : ℝ) + 2)
  let L : ℝ := Real.log (K : ℝ) + 1
  let H : ℝ := (Q : ℝ) * (2 : ℝ) ^ (d + 2)
  let ε : ℝ := min 1 (Real.log 2 / (2 * L * H))
  let b : ℝ := Real.log 2 / (2 * H)
  let c : ℝ := min b (a * ε)
  let C : ℝ := Real.exp (L + Real.log 2) + 1
  have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hQ)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hβ : 0 < β := by dsimp [β]; positivity
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hL : 0 < L := by dsimp [L]; linarith [Real.log_nonneg hKreal]
  have hH : 0 < H := by dsimp [H]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεbound : L * ε ≤ b := by
    have h := min_le_right (1 : ℝ) (Real.log 2 / (2 * L * H))
    have hm := mul_le_mul_of_nonneg_left h hL.le
    have heq : L * (Real.log 2 / (2 * L * H)) = b := by
      dsimp [b]
      field_simp
    exact hm.trans_eq heq
  have hb : 0 < b := by dsimp [b]; positivity
  have hc : 0 < c := lt_min hb (mul_pos ha hε)
  have hC : 1 ≤ C := by dsimp [C]; linarith [Real.exp_pos (L + Real.log 2)]
  refine ⟨c, C, hc, hC, fun t ht => ?_⟩
  have hT : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hTpos : (0 : ℝ) < t := by linarith
  let x : ℝ := (t : ℝ) ^ β
  let k : ℕ := ⌈x⌉₊
  let m : ℕ := ⌈ε * (k : ℝ) ^ d⌉₊
  let n : ℕ := Q * k ^ 2
  let j : ℕ := t / n
  have hx : 1 ≤ x := by dsimp [x]; exact Real.one_le_rpow hT hβ.le
  have hxk : x ≤ (k : ℝ) := Nat.le_ceil x
  have hk : 1 ≤ k := by
    have : (1 : ℝ) ≤ k := hx.trans hxk
    exact_mod_cast this
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hk2 : (k : ℝ) ≤ 2 * x := by
    have h := Nat.ceil_lt_add_one (le_trans zero_le_one hx)
    dsimp [k]
    linarith
  have hxpow : x ^ d = (t : ℝ) ^ α := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hTpos.le]
    congr 1
    dsimp [α, β]
    field_simp
  have hxtime : x ^ (d + 2) = (t : ℝ) := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hTpos.le]
    have he : β * ((d + 2 : ℕ) : ℝ) = 1 := by
      dsimp [β]
      push_cast
      field_simp
    rw [he, Real.rpow_one]
  have hzpos : 0 < (k : ℝ) ^ d := pow_pos hkpos _
  have hzone : 1 ≤ (k : ℝ) ^ d := one_le_pow₀ (by linarith)
  have hmlo : ε * (k : ℝ) ^ d ≤ (m : ℝ) := Nat.le_ceil _
  have hmhi : (m : ℝ) ≤ ε * (k : ℝ) ^ d + 1 := by
    have h := Nat.ceil_lt_add_one (mul_nonneg hε.le hzpos.le)
    dsimp [m]
    linarith
  have hmscale : (m : ℝ) ≤ 2 * (k : ℝ) ^ d := by
    have hm := mul_le_mul_of_nonneg_right hε1 hzpos.le
    nlinarith
  have hn : 1 ≤ n := by dsimp [n]; nlinarith
  have hheat : (m : ℝ) * (Real.sqrt 2 ^ d * greenConst d *
      (n : ℝ) ^ (-(d : ℝ) / 2)) ≤ 1 / 2 := by
    dsimp [n]
    exact hblock m k hk hmscale
  have htimepow : (k : ℝ) ^ (d + 2) ≤ (2 : ℝ) ^ (d + 2) * (t : ℝ) := by
    have h := pow_le_pow_left₀ hkpos.le hk2 (d + 2)
    rw [mul_pow, hxtime] at h
    exact h
  have htimediv : (k : ℝ) ^ d / H ≤ (t : ℝ) / (n : ℝ) := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    rw [div_le_div_iff₀ hH hnpos]
    dsimp [H, n]
    push_cast
    rw [pow_add] at htimepow
    nlinarith [htimepow]
  have hj : (k : ℝ) ^ d / H - 1 ≤ (j : ℝ) := by
    have hn' : 0 < n := by omega
    have hmod := Nat.mod_lt t hn'
    have hdiv := Nat.div_add_mod t n
    have hmodR : ((t % n : ℕ) : ℝ) < n := by exact_mod_cast hmod
    have hdivR : (n : ℝ) * ((t / n : ℕ) : ℝ) + ((t % n : ℕ) : ℝ) = t := by
      exact_mod_cast hdiv
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn'
    have hfloor : (t : ℝ) / n - 1 ≤ ((t / n : ℕ) : ℝ) := by
      rw [sub_le_iff_le_add, div_le_iff₀ hnpos]
      nlinarith
    exact (sub_le_sub_right htimediv 1).trans hfloor
  have hcost : L * (m : ℝ) - Real.log 2 * (j : ℝ) ≤
      L + Real.log 2 - b * (k : ℝ) ^ d := by
    have hmL := mul_le_mul_of_nonneg_left hmhi hL.le
    have hεz := mul_le_mul_of_nonneg_right hεbound hzpos.le
    have hjlog := mul_le_mul_of_nonneg_left hj hlog2.le
    have hid : Real.log 2 * ((k : ℝ) ^ d / H) = 2 * b * (k : ℝ) ^ d := by
      dsimp [b]
      ring
    nlinarith only [hmL, hεz, hjlog, hid]
  have hkp : (t : ℝ) ^ α ≤ (k : ℝ) ^ d := by
    rw [← hxpow]
    exact pow_le_pow_left₀ (by linarith) hxk d
  have h := hmoment a ha m n t hn hheat
  change rangeExp d a t ≤ (m : ℝ) * (K : ℝ) ^ m * (1 / 2 : ℝ) ^ j +
    Real.exp (-(a * (m : ℝ))) at h
  have hcost' : (Real.log K + 1) * (m : ℝ) - Real.log 2 * (j : ℝ) ≤
      (Real.log K + 1) + Real.log 2 - b * (k : ℝ) ^ d := by
    simpa only [L] using hcost
  have hfinal := exponential_range_cost ha.le hε.le hc.le hzpos.le
    (Real.rpow_pos_of_pos hTpos α).le hKpos hmlo hkp (min_le_left _ _)
    (min_le_right _ _) hcost'
  exact h.trans hfinal

/-- The two-sided subcritical tail estimate with the range bounds supplied. -/
theorem subcritical_tail_of_range_count
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hprob : IsProbabilityMeasure ν)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k, (k : ℝ) ∂ν < 0)
    (hpos : 0 < ν (Set.Ioi 0)) (θ : ℝ) (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ t : ℕ, 1 ≤ t →
      C⁻¹ * Real.exp (-(C * (t : ℝ) ^ ((d : ℝ) / (d + 2)))) ≤ S (law d ν) t ∧
        S (law d ν) t ≤ C * Real.exp (-(c * (t : ℝ) ^ ((d : ℝ) / (d + 2)))) := by
  let _ := hprob
  exact exists_tail_bounds_of_upper_range_moment hd
    (range_moment_upper_bound_of_range_count d hd) hint hmean hpos hθ hexp


end Parking

end
