import Parking.Support.DVConfine
import Parking.Support.DVRateLimit
import Parking.Support.DVConstant

/-!
# The upper limit of `-log E_0 e^{-a|R_t|} / t^{d/(d+2)}`

If `n^{2/d} dirichletRate d n → c`, then for every `ε > 0`, eventually

  `log E_0 e^{-a|R_t|} ≥ -(dvConst d a c + ε) t^{d/(d+2)}`

(`eventually_log_rangeExp_ge`).  Take `w > 0` with `a w + c w^{-2/d}` within `ε/4` of
`dvConst d a c`, and `n = ⌈w s⌉`, `s = t^{d/(d+2)}`.  A function of Dirichlet ratio
`μ < (c + ε₁) n^{-2/d}` vanishing off a set of at most `n` sites confines the walk
(`rangeExp_ge_of_ratio`):
`log E_0 e^{-a|R_t|} ≥ -a n + (t+1) log(1 - μ) - (1/2) log n`, and
`(t + 1) n^{-2/d} ≤ (1 + 1/t) w^{-2/d} s` since `t · s^{-2/d} = s`.
-/

noncomputable section

namespace Parking

open LatticeProb MeasureTheory Filter Topology

variable {d : ℕ}

/-- `t · (t^{d/(d+2)})^{-2/d} = t^{d/(d+2)}`. -/
theorem mul_rpow_scale (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) :
    t * (t ^ ((d : ℝ) / (d + 2))) ^ (-(2 : ℝ) / d) = t ^ ((d : ℝ) / (d + 2)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [← Real.rpow_mul ht.le]
  have h : (d : ℝ) / (d + 2) * (-(2 : ℝ) / d) = (d : ℝ) / (d + 2) - 1 := by
    field_simp; ring
  rw [h, Real.rpow_sub_one ht.ne']
  field_simp

/-- The confinement bound in logarithmic form. -/
theorem log_rangeExp_ge_of_ratio (hd : 1 ≤ d) {a : ℝ} (ha : 0 ≤ a) {V : Finset (Site d)}
    {h : Site d → ℝ} (hV : ∀ x ∉ V, h x = 0) (hm : 0 < sqMass h) {n : ℕ} (hVn : V.card ≤ n)
    (hn : 0 < n) {B ε₃ : ℝ} (hμB : latEnergy h / sqMass h ≤ B) (hB : 2 * B ≤ ε₃)
    (hε₃ : ε₃ ≤ 1) (t : ℕ) :
    -(a * n) - (t + 1) * (B * (1 + ε₃)) - Real.log n / 2 ≤ Real.log (rangeExp d a t) := by
  set μ := latEnergy h / sqMass h with hμdef
  have hμ0 : 0 ≤ μ := div_nonneg (latEnergy_nonneg h) hm.le
  have hB0 : 0 ≤ B := hμ0.trans hμB
  have hμ1 : μ ≤ 1 := by linarith
  have hpos1 : 0 < 1 - μ := by linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hconf := rangeExp_ge_of_ratio hd ha hV hm hμ1 t
  rw [← hμdef] at hconf
  have hVcard : (V.card : ℝ) ≤ n := by exact_mod_cast hVn
  have hZ : 0 < rangeExp d a t := rangeExp_pos hd ha t
  have hA : Real.exp (-(a * n)) * (1 - μ) ^ (t + 1) ≤ Real.sqrt n * rangeExp d a t := by
    calc Real.exp (-(a * n)) * (1 - μ) ^ (t + 1)
        ≤ Real.exp (-(a * V.card)) * (1 - μ) ^ (t + 1) := by gcongr
      _ ≤ Real.sqrt V.card * rangeExp d a t := hconf
      _ ≤ Real.sqrt n * rangeExp d a t := by gcongr
  have hL := Real.log_le_log (by positivity) hA
  rw [Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow,
    Real.log_mul (by positivity) hZ.ne', Real.log_sqrt hnpos.le] at hL
  have hlog2 : -(B * (1 + ε₃)) ≤ Real.log (1 - μ) := by
    have h1 := Real.one_sub_inv_le_log_of_pos hpos1
    have h2 : (1 - μ)⁻¹ ≤ 1 + 2 * μ := by
      rw [inv_le_iff_one_le_mul₀ hpos1]
      nlinarith
    have h3 : μ * (1 + 2 * μ) ≤ B * (1 + ε₃) :=
      mul_le_mul hμB (by linarith) (by positivity) hB0
    have e : 1 - (1 - μ)⁻¹ = -(μ * (1 - μ)⁻¹) := by field_simp; ring
    have h5 : μ * (1 - μ)⁻¹ ≤ μ * (1 + 2 * μ) := mul_le_mul_of_nonneg_left h2 hμ0
    linarith
  have ht : (0 : ℝ) ≤ (t : ℝ) + 1 := by positivity
  have h4 : -((t + 1) * (B * (1 + ε₃))) ≤ (t + 1) * Real.log (1 - μ) := by
    have := mul_le_mul_of_nonneg_left hlog2 ht
    linarith
  push_cast at hL
  linarith

/-- The scaling of the time against the volume. -/
theorem time_mul_rpow_le (hd : 1 ≤ d) {t : ℕ} (ht : 1 ≤ t) {n w c' ε₃ : ℝ} (hw : 0 < w)
    (hc' : 0 ≤ c') (hwn : w * (t : ℝ) ^ ((d : ℝ) / (d + 2)) ≤ n)
    (htε : ((t : ℝ) + 1) ≤ (1 + ε₃) * t) :
    (t + 1) * (c' * n ^ (-((2 : ℝ) / d)))
      ≤ (1 + ε₃) * (c' * w ^ (-(2 : ℝ) / d)) * (t : ℝ) ^ ((d : ℝ) / (d + 2)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  set s := (t : ℝ) ^ ((d : ℝ) / (d + 2)) with hsdef
  have hs0 : 0 < s := by positivity
  have hnw : n ^ (-((2 : ℝ) / d)) ≤ (w * s) ^ (-((2 : ℝ) / d)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hwn (by
      have : (0 : ℝ) ≤ 2 / d := by positivity
      linarith)
  have hws : (w * s) ^ (-((2 : ℝ) / d)) = w ^ (-(2 : ℝ) / d) * s ^ (-((2 : ℝ) / d)) := by
    rw [Real.mul_rpow hw.le hs0.le, neg_div]
  have hscale := mul_rpow_scale hd htpos
  rw [← hsdef, show -(2 : ℝ) / d = -((2 : ℝ) / d) by ring] at hscale
  have hsp : 0 ≤ s ^ (-((2 : ℝ) / d)) := by positivity
  calc (t + 1) * (c' * n ^ (-((2 : ℝ) / d)))
      ≤ ((1 + ε₃) * t) * (c' * (w ^ (-(2 : ℝ) / d) * s ^ (-((2 : ℝ) / d)))) := by
        rw [← hws]
        have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hwn
        refine mul_le_mul htε (mul_le_mul_of_nonneg_left hnw hc')
          (mul_nonneg hc' (Real.rpow_pos_of_pos hnpos _).le) ?_
        linarith
    _ = (1 + ε₃) * (c' * w ^ (-(2 : ℝ) / d)) * (t * s ^ (-((2 : ℝ) / d))) := by ring
    _ = (1 + ε₃) * (c' * w ^ (-(2 : ℝ) / d)) * s := by rw [hscale]

/-- `log n / 2 ≤ (ε / 4) s` once `s` is large and `n ≤ w s + 1`. -/
theorem log_div_two_le {n w s ε : ℝ} (hn : 0 < n) (hw : 0 < w) (hε : 0 < ε) (hs1 : 1 ≤ s)
    (hns : n ≤ w * s + 1) (hs : 16 * (w + 1) / (ε / 2) ^ 2 ≤ s) :
    Real.log n / 2 ≤ ε / 4 * s := by
  have h1 := Real.log_le_rpow_div (x := n) hn.le (by norm_num : (0 : ℝ) < 1 / 2)
  have h2 : n ≤ (w + 1) * s := by nlinarith
  have h3 : n ^ ((1 : ℝ) / 2) ≤ ((w + 1) * s) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow hn.le h2 (by norm_num)
  have h4 : ((w + 1) * s) ^ ((1 : ℝ) / 2) ≤ ε / 4 * s := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hs
    nlinarith
  have h5 : n ^ ((1 : ℝ) / 2) / (1 / 2) = 2 * n ^ ((1 : ℝ) / 2) := by ring
  linarith

/-- The final bookkeeping. -/
theorem final_bound_upper {K ε a w c W ε₁ ε₃ s t n B logZ logn : ℝ} (hs : 0 ≤ s)
    (hlog1 : -(a * n) - (t + 1) * (B * (1 + ε₃)) - logn ≤ logZ)
    (e1 : a * n ≤ a * w * s + a) (e3 : a ≤ ε / 4 * s)
    (e5 : (t + 1) * (B * (1 + ε₃)) ≤ ((c + ε₁) * W + ε / 8) * s) (e4 : ε₁ * W = ε / 8)
    (hlogn : logn ≤ ε / 4 * s) (hkey : a * w + c * W ≤ K + ε / 4) :
    -(K + ε) * s ≤ logZ := by
  have e6 : (a * w + c * W) * s ≤ (K + ε / 4) * s := mul_le_mul_of_nonneg_right hkey hs
  have e8 : ((c + ε₁) * W + ε / 8) * s = c * W * s + ε / 8 * s + ε / 8 * s := by
    rw [add_mul c ε₁, e4]; ring
  have e9 : (a * w + c * W) * s = a * w * s + c * W * s := by ring
  have e10 : -(K + ε) * s = -((K + ε / 4) * s) - 3 * (ε / 4 * s) := by ring
  rw [e10]
  linarith

/-- **The lower bound on the range moment at the scale `t^{d/(d+2)}`.** -/
theorem eventually_log_rangeExp_ge (hd : 1 ≤ d) {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c)
    (hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ ((2 : ℝ) / d) * dirichletRate d n) atTop (𝓝 c))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop,
      -(dvConst d a c + ε) * (t : ℝ) ^ ((d : ℝ) / (d + 2)) ≤ Real.log (rangeExp d a t) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨w, hw, hwk⟩ := exists_le_dvConst hd ha hc (by positivity : (0 : ℝ) < ε / 4)
  set W := w ^ (-(2 : ℝ) / d) with hW
  have hW0 : 0 < W := Real.rpow_pos_of_pos hw _
  set ε₁ := ε / (8 * W) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  have hε₁W : ε₁ * W = ε / 8 := by rw [hε₁]; field_simp
  set ε₃ := min 1 (ε / (24 * ((c + ε₁) * W))) with hε₃
  have hε₃0 : 0 < ε₃ := lt_min one_pos (by positivity)
  have hε₃1 : ε₃ ≤ 1 := min_le_left _ _
  have hε₃c : 3 * ε₃ * ((c + ε₁) * W) ≤ ε / 8 := by
    have h := min_le_right 1 (ε / (24 * ((c + ε₁) * W)))
    rw [← hε₃] at h
    have hpos : 0 < (c + ε₁) * W := by positivity
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  -- thresholds in `n`
  have hev1 : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ ((2 : ℝ) / d) * dirichletRate d n < c + ε₁ :=
    hlim.eventually (gt_mem_nhds (by linarith))
  have hneg : Tendsto (fun n : ℕ => (n : ℝ) ^ (-((2 : ℝ) / d))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  have hev2 : ∀ᶠ n : ℕ in atTop, (c + ε₁) * (n : ℝ) ^ (-((2 : ℝ) / d)) < ε₃ / 2 :=
    (hneg.const_mul (c + ε₁)).eventually (gt_mem_nhds (by rw [mul_zero]; positivity))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hev1.and (hev2.and (eventually_ge_atTop (2 ^ d))))
  -- thresholds in `t`
  have hs : Tendsto (fun t : ℕ => (t : ℝ) ^ ((d : ℝ) / (d + 2))) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  set S₀ : ℝ := max 1 (max ((N₁ : ℝ) / w) (max (4 * a / ε) (16 * (w + 1) / (ε / 2) ^ 2)))
  filter_upwards [hs.eventually_ge_atTop S₀, eventually_ge_atTop 1,
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hε₃0)]
    with t hsS ht1 htε
  set s := (t : ℝ) ^ ((d : ℝ) / (d + 2)) with hsdef
  have hs1 : 1 ≤ s := le_trans (le_max_left _ _) hsS
  have hsN : (N₁ : ℝ) / w ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hsS
  have hsa : 4 * a / ε ≤ s :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hsS
  have hslog : 16 * (w + 1) / (ε / 2) ^ 2 ≤ s :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hsS
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht1
  have htε' : ((t : ℝ) + 1) ≤ (1 + ε₃) * t := by
    have h1 : 1 / (t : ℝ) * t = 1 := by field_simp
    have h2 : 1 / (t : ℝ) * t ≤ ε₃ * t := mul_le_mul_of_nonneg_right htε.le htpos.le
    linarith
  -- the volume `n`
  set n : ℕ := ⌈w * s⌉₊ with hn
  have hn1 : w * s ≤ n := Nat.le_ceil _
  have hn2 : (n : ℝ) ≤ w * s + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hnN : N₁ ≤ n := by
    have : (N₁ : ℝ) ≤ w * s := by rw [div_le_iff₀ hw] at hsN; linarith
    exact_mod_cast this.trans hn1
  obtain ⟨hΛn, hBn, hn2d⟩ := hN₁ n hnN
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn1
  set B := (c + ε₁) * (n : ℝ) ^ (-((2 : ℝ) / d)) with hB
  have hΛB : dirichletRate d n < B := by
    have hpq : (n : ℝ) ^ ((2 : ℝ) / d) * (n : ℝ) ^ (-((2 : ℝ) / d)) = 1 := by
      rw [← Real.rpow_add hnpos, add_neg_cancel, Real.rpow_zero]
    have hq0 : 0 < (n : ℝ) ^ (-((2 : ℝ) / d)) := Real.rpow_pos_of_pos hnpos _
    calc dirichletRate d n
        = dirichletRate d n * ((n : ℝ) ^ ((2 : ℝ) / d) * (n : ℝ) ^ (-((2 : ℝ) / d))) := by
          rw [hpq, mul_one]
      _ = ((n : ℝ) ^ ((2 : ℝ) / d) * dirichletRate d n) * (n : ℝ) ^ (-((2 : ℝ) / d)) := by ring
      _ < (c + ε₁) * (n : ℝ) ^ (-((2 : ℝ) / d)) := mul_lt_mul_of_pos_right hΛn hq0
  obtain ⟨V, h, hVn, hV, hm, hμ⟩ := exists_lt_of_dirichletRate_lt hn2d hΛB
  have hlog1 := log_rangeExp_ge_of_ratio hd ha.le hV hm ((card_le_card_fatten V).trans hVn)
    (by exact_mod_cast hnpos) hμ.le (by linarith) hε₃1 t (a := a)
  have hTB := time_mul_rpow_le hd ht1 hw (by positivity : (0 : ℝ) ≤ c + ε₁) hn1 htε'
  rw [← hW, ← hsdef] at hTB
  have hlogn := log_div_two_le hnpos hw hε hs1 hn2 hslog
  -- assemble
  have e1 : a * n ≤ a * w * s + a := by
    have := mul_le_mul_of_nonneg_left hn2 ha.le
    linarith
  have e3 : a ≤ ε / 4 * s := by rw [div_le_iff₀ hε] at hsa; linarith
  have e5 : (t + 1) * (B * (1 + ε₃)) ≤ ((c + ε₁) * W + ε / 8) * s := by
    have hcW : 0 ≤ (c + ε₁) * W := by positivity
    calc (t + 1) * (B * (1 + ε₃)) = ((t + 1) * B) * (1 + ε₃) := by ring
      _ ≤ ((1 + ε₃) * ((c + ε₁) * W) * s) * (1 + ε₃) :=
          mul_le_mul_of_nonneg_right hTB (by linarith)
      _ = ((c + ε₁) * W + (2 * ε₃ + ε₃ ^ 2) * ((c + ε₁) * W)) * s := by ring
      _ ≤ ((c + ε₁) * W + ε / 8) * s := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith)
          have : (2 * ε₃ + ε₃ ^ 2) * ((c + ε₁) * W) ≤ 3 * ε₃ * ((c + ε₁) * W) := by
            refine mul_le_mul_of_nonneg_right ?_ hcW
            nlinarith
          linarith
  exact final_bound_upper (by linarith) hlog1 e1 e3 e5 hε₁W hlogn hwk

end Parking

end
