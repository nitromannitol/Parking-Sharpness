/-
The two-sided rates of the ℓ²-norm and the max-norm of the finite-time SRW
Green kernel (`eq:green-norms`), proved rather than assumed.

* The ℓ² clause is `Parking.green d n` read through `Parking.green_eq_srwGreen`
  as `LatticeProb.srwGreen d n`, whose sum of squares is
  `LatticeProb.exists_tsum_srwGreen_sq_bounds` (already proved, two-sided);
  taking square roots and matching `LatticeProb.varianceRate`'s square root to
  `Parking.External.greenL2Rate` finishes it in every dimension at once.
* The max-norm UPPER half is `LatticeProb.srwGreen_{one,two,high}_dim_le`
  (already proved), read at `x` and taken through the truncated-Green bridge;
  each is an affine bound `A + B · rate`, turned into the required
  multiplicative form using `rate n ≥ rate 2 > 0` for `n ≥ 2`.
* The max-norm LOWER half is absent from the shared library (filed there as a
  separate request).  It is short enough to supply here: `greenMax d n ≥
  green d n 0`, and summing `LatticeProb.exists_srwHeat_diag_lower`'s
  `c / √k^d ≤ srwHeat d (2k) 0` over only the even times `2k ≤ n - 1` gives
  `green d n 0 ≥ c · ∑_{k=1}^{K} k^{-d/2}` with `K = ⌊(n-1)/2⌋`.  For `d = 1`
  this series is at least `√K` (an elementary telescoping bound, proved below
  by induction) and for `d = 2` it is at least `log(K+1)` (the same telescoping
  argument against `Real.log_le_sub_one_of_pos`).  Both hold for every `n ≥ 4`
  once `K ≥ n/4` is used, which turns them into the rates `Parking.External.
  greenMaxRate` names; the finitely many smaller `n` are absorbed by the
  standard "eventually implies for all `n ≥ 2`" extension used already for
  `Parking.External.sandpileGrowth`, since `n ↦ greenMax d n` is monotone and
  positive at `n = 1`.  For `d ≥ 3`, `greenMaxRate d n = 1` and both bounds are
  immediate: `heat d 0 0 = 1` alone gives the lower bound, and
  `srwGreen_high_dim_le` alone gives the upper bound, without any horizon
  growth needed.
-/
import Parking.External.GreenNorms
import Parking.Support.WMartingale
import Parking.Support.GreenBridge
import LatticeProb.Walk.VarianceScale
import LatticeProb.Walk.SRWGreenSup
import LatticeProb.Walk.SRWDiag

open Filter Topology

/-! ### An elementary series lower bound: `√K ≤ ∑_{k=1}^K 1/√k`. -/

private theorem sum_inv_sqrt_ge (K : ℕ) :
    Real.sqrt (K : ℝ) ≤ ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / Real.sqrt (k : ℝ) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1)]
    have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hstep : Real.sqrt ((K : ℝ) + 1) - Real.sqrt (K : ℝ) ≤ 1 / Real.sqrt ((K : ℝ) + 1) := by
      rcases Nat.eq_zero_or_pos K with hK0 | hKpos
      · subst hK0; norm_num
      · have hKpos' : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
        have hK1pos : (0 : ℝ) < (K : ℝ) + 1 := by linarith
        have ht : 0 < Real.sqrt ((K : ℝ) + 1) := Real.sqrt_pos.mpr hK1pos
        have hprodeq : Real.sqrt ((K : ℝ) * ((K : ℝ) + 1))
            = Real.sqrt (K : ℝ) * Real.sqrt ((K : ℝ) + 1) :=
          Real.sqrt_mul (by positivity) _
        have hKsq : Real.sqrt (((K : ℝ)) ^ 2) = (K : ℝ) := Real.sqrt_sq (by positivity)
        have hmono : Real.sqrt (((K : ℝ)) ^ 2) ≤ Real.sqrt ((K : ℝ) * ((K : ℝ) + 1)) :=
          Real.sqrt_le_sqrt (by nlinarith)
        have hKle : (K : ℝ) ≤ Real.sqrt (K : ℝ) * Real.sqrt ((K : ℝ) + 1) := by
          calc (K : ℝ) = Real.sqrt (((K : ℝ)) ^ 2) := hKsq.symm
            _ ≤ Real.sqrt ((K : ℝ) * ((K : ℝ) + 1)) := hmono
            _ = Real.sqrt (K : ℝ) * Real.sqrt ((K : ℝ) + 1) := hprodeq
        rw [le_div_iff₀ ht]
        have ht2 : Real.sqrt ((K : ℝ) + 1) ^ 2 = (K : ℝ) + 1 := Real.sq_sqrt hK1pos.le
        nlinarith [hKle, ht2]
    linarith [ih]

/-! ### An elementary series lower bound: `log(K+1) ≤ ∑_{k=1}^K 1/k`. -/

private theorem sum_inv_ge_log (K : ℕ) :
    Real.log ((K : ℝ) + 1) ≤ ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (k : ℝ) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1)]
    have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hassoc : (K : ℝ) + 1 + 1 = (K : ℝ) + 2 := by ring
    rw [hassoc]
    have hKpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    have hK2pos : (0 : ℝ) < (K : ℝ) + 2 := by positivity
    have hstep : Real.log ((K : ℝ) + 2) - Real.log ((K : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) := by
      have hx : Real.log (((K : ℝ) + 2) / ((K : ℝ) + 1)) ≤ ((K : ℝ) + 2) / ((K : ℝ) + 1) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hK2pos hKpos)
      rw [Real.log_div (by positivity) (by positivity)] at hx
      have heq : ((K : ℝ) + 2) / ((K : ℝ) + 1) - 1 = 1 / ((K : ℝ) + 1) := by
        field_simp
        ring
      rw [heq] at hx
      linarith
    linarith [ih]

/-! ### Turning an eventual lower bound into one holding for all `n ≥ 2`. -/

private theorem exists_greenMax_lower_of_eventual (d : ℕ) (hd : 1 ≤ d)
    (rate : ℕ → ℝ) (hratemono : Monotone rate) (hrate2 : 0 < rate 2)
    (N : ℕ) (c : ℝ) (hc : 0 < c) (hev : ∀ n : ℕ, N ≤ n → c * rate n ≤ Parking.greenMax d n) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ n : ℕ, 2 ≤ n → c' * rate n ≤ Parking.greenMax d n := by
  have hbdd1 : BddAbove (Set.range fun x => Parking.green d 1 x) :=
    ⟨1, by rintro _ ⟨x, rfl⟩; simpa using Parking.green_le hd 1 x⟩
  have hgreen10 : Parking.green d 1 0 = 1 := by
    show ∑ j ∈ Finset.range 1, Parking.heat d j 0 = 1
    rw [Finset.sum_range_one]
    show (if (0 : Parking.Site d) = 0 then (1 : ℝ) else 0) = 1
    rw [if_pos rfl]
  have hM1 : 0 < Parking.greenMax d 1 :=
    lt_of_lt_of_le (by rw [hgreen10]; norm_num) (le_ciSup hbdd1 0)
  have hMmono : Monotone (fun n => Parking.greenMax d n) := by
    intro m n hmn
    have hbdd : BddAbove (Set.range fun x => Parking.green d n x) :=
      ⟨n, by rintro _ ⟨x, rfl⟩; simpa using Parking.green_le hd n x⟩
    apply ciSup_mono hbdd
    intro x
    show ∑ j ∈ Finset.range m, Parking.heat d j x ≤ ∑ j ∈ Finset.range n, Parking.heat d j x
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun j hj => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hmn))
      (fun j _ _ => Parking.heat_nonneg j x)
  set T : ℕ := max N 2 with hT
  have hT2 : 2 ≤ T := le_max_right _ _
  have hTN : N ≤ T := le_max_left _ _
  have hrateTpos : 0 < rate T := lt_of_lt_of_le hrate2 (hratemono hT2)
  set c' : ℝ := min c (Parking.greenMax d 1 / rate T) with hc'def
  have hc' : 0 < c' := lt_min hc (div_pos hM1 hrateTpos)
  refine ⟨c', hc', fun n hn => ?_⟩
  by_cases hlarge : T ≤ n
  · have hratenonneg : 0 ≤ rate n := le_trans hrate2.le (hratemono (le_trans hT2 hlarge))
    calc c' * rate n ≤ c * rate n := mul_le_mul_of_nonneg_right (min_le_left _ _) hratenonneg
      _ ≤ Parking.greenMax d n := hev n (le_trans hTN hlarge)
  · rw [not_le] at hlarge
    have hn1 : 1 ≤ n := by omega
    have hraten_le : rate n ≤ rate T := hratemono hlarge.le
    have hratenonneg : 0 ≤ rate n := le_trans hrate2.le (hratemono hn)
    calc c' * rate n
        ≤ (Parking.greenMax d 1 / rate T) * rate n :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hratenonneg
      _ ≤ (Parking.greenMax d 1 / rate T) * rate T :=
          mul_le_mul_of_nonneg_left hraten_le (div_nonneg hM1.le hrateTpos.le)
      _ = Parking.greenMax d 1 := by field_simp
      _ ≤ Parking.greenMax d n := hMmono hn1

/-! ### The even-time sum sitting inside the truncated Green function at `0`. -/

private theorem sum_heat_two_mul_le_green (d n K : ℕ) (hK : 2 * K < n) :
    ∑ k ∈ Finset.Icc 1 K, Parking.heat d (2 * k) 0 ≤ Parking.green d n 0 := by
  have hinj : Set.InjOn (fun k : ℕ => 2 * k) (Finset.Icc 1 K : Finset ℕ) :=
    fun a _ b _ h => by simpa using h
  rw [← Finset.sum_image (f := fun j => Parking.heat d j 0) hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨k, hk, rfl⟩ := hj
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_range]
    omega
  · intro j _ _
    exact Parking.heat_nonneg j 0

private theorem sum_heat_two_mul_ge (d : ℕ) (hd : 0 < d) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ K : ℕ,
      c₀ * ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / Real.sqrt (k : ℝ) ^ d
        ≤ ∑ k ∈ Finset.Icc 1 K, Parking.heat d (2 * k) 0 := by
  obtain ⟨c₀, hc₀, hlow⟩ := LatticeProb.exists_srwHeat_diag_lower (d := d) hd
  refine ⟨c₀, hc₀, fun K => ?_⟩
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  rw [Finset.mem_Icc] at hk
  have h := hlow k hk.1
  rw [show Parking.heat d (2 * k) 0 = LatticeProb.srwHeat d (2 * k) 0 from
    Parking.heat_eq_srwHeat d (2 * k) 0]
  rw [mul_one_div]
  exact h

/-! ### The Nat arithmetic relating the horizon `n` to `K = ⌊(n-1)/2⌋`. -/

private theorem four_K_ge (n : ℕ) (hn : 4 ≤ n) : (n : ℝ) ≤ 4 * (((n - 1) / 2 : ℕ) : ℝ) := by
  have h : n ≤ 4 * ((n - 1) / 2) := by omega
  exact_mod_cast h

private theorem two_K_lt (n : ℕ) (hn : 1 ≤ n) : 2 * ((n - 1) / 2) < n := by omega

/-! ### The max-norm lower bound, dimension by dimension. -/

private theorem exists_max_lower_one :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
      c * Parking.External.greenMaxRate 1 n ≤ Parking.greenMax 1 n := by
  have hrateeq : ∀ n : ℕ, Parking.External.greenMaxRate 1 n = Real.sqrt (n : ℝ) := by
    intro n
    rw [Parking.External.greenMaxRate, if_pos rfl, Real.sqrt_eq_rpow]
  obtain ⟨c₁, hc₁, hsum⟩ := sum_heat_two_mul_ge 1 one_pos
  obtain ⟨c₀, hc₀, hev⟩ : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ n : ℕ, 16 ≤ n →
      c₀ * Parking.External.greenMaxRate 1 n ≤ Parking.greenMax 1 n := by
    refine ⟨c₁ / 2, by positivity, fun n hn => ?_⟩
    set K : ℕ := (n - 1) / 2 with hKdef
    have hKn : 2 * K < n := two_K_lt n (by omega)
    have hbdd1 : BddAbove (Set.range fun x => Parking.green 1 n x) :=
      ⟨n, by rintro _ ⟨x, rfl⟩; simpa using Parking.green_le (le_refl 1) n x⟩
    have h1 : Parking.green 1 n 0 ≤ Parking.greenMax 1 n := le_ciSup hbdd1 0
    have h2 : ∑ k ∈ Finset.Icc 1 K, Parking.heat 1 (2 * k) 0 ≤ Parking.green 1 n 0 :=
      sum_heat_two_mul_le_green 1 n K hKn
    have h3 := hsum K
    have h4 : Real.sqrt (K : ℝ) ≤ ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / Real.sqrt (k : ℝ) ^ 1 := by
      simpa using sum_inv_sqrt_ge K
    have hK4 : (n : ℝ) ≤ 4 * (K : ℝ) := four_K_ge n (by omega)
    have hsqrt4K : Real.sqrt (n : ℝ) ≤ Real.sqrt (4 * (K : ℝ)) := Real.sqrt_le_sqrt hK4
    have hsqrt4 : Real.sqrt (4 * (K : ℝ)) = 2 * Real.sqrt (K : ℝ) := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    have hsqrt_mono : Real.sqrt (n : ℝ) / 2 ≤ Real.sqrt (K : ℝ) := by
      rw [hsqrt4] at hsqrt4K; linarith
    rw [hrateeq]
    calc c₁ / 2 * Real.sqrt (n : ℝ) = c₁ * (Real.sqrt (n:ℝ) / 2) := by ring
      _ ≤ c₁ * Real.sqrt (K : ℝ) := mul_le_mul_of_nonneg_left hsqrt_mono hc₁.le
      _ ≤ c₁ * ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / Real.sqrt (k : ℝ) ^ 1 :=
          mul_le_mul_of_nonneg_left h4 hc₁.le
      _ ≤ ∑ k ∈ Finset.Icc 1 K, Parking.heat 1 (2 * k) 0 := h3
      _ ≤ Parking.green 1 n 0 := h2
      _ ≤ Parking.greenMax 1 n := h1
  have hratemono : Monotone (fun n : ℕ => Parking.External.greenMaxRate 1 n) := by
    intro m n hmn
    simp only [hrateeq]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hmn)
  have hrate2 : 0 < Parking.External.greenMaxRate 1 2 := by
    rw [hrateeq]; positivity
  exact exists_greenMax_lower_of_eventual 1 (le_refl 1)
    (fun n => Parking.External.greenMaxRate 1 n) hratemono hrate2 16 c₀ hc₀ hev

private theorem exists_max_lower_two :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
      c * Parking.External.greenMaxRate 2 n ≤ Parking.greenMax 2 n := by
  have hrateeq : ∀ n : ℕ, Parking.External.greenMaxRate 2 n = Real.log (n : ℝ) := by
    intro n
    rw [Parking.External.greenMaxRate, if_neg (by norm_num), if_pos rfl]
  obtain ⟨c₁, hc₁, hsum⟩ := sum_heat_two_mul_ge 2 (by norm_num)
  obtain ⟨c₀, hc₀, hev⟩ : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ n : ℕ, 16 ≤ n →
      c₀ * Parking.External.greenMaxRate 2 n ≤ Parking.greenMax 2 n := by
    refine ⟨c₁ / 2, by positivity, fun n hn => ?_⟩
    set K : ℕ := (n - 1) / 2 with hKdef
    have hKn : 2 * K < n := two_K_lt n (by omega)
    have hbdd1 : BddAbove (Set.range fun x => Parking.green 2 n x) :=
      ⟨n, by rintro _ ⟨x, rfl⟩; simpa using Parking.green_le (by norm_num) n x⟩
    have h1 : Parking.green 2 n 0 ≤ Parking.greenMax 2 n := le_ciSup hbdd1 0
    have h2 : ∑ k ∈ Finset.Icc 1 K, Parking.heat 2 (2 * k) 0 ≤ Parking.green 2 n 0 :=
      sum_heat_two_mul_le_green 2 n K hKn
    have h3 := hsum K
    have h4 : Real.log ((K : ℝ) + 1) ≤ ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (k : ℝ) := sum_inv_ge_log K
    have h4' : Real.log ((K : ℝ) + 1) ≤ ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / Real.sqrt (k : ℝ) ^ 2 := by
      have hfun : ∀ k ∈ Finset.Icc 1 K, (1 : ℝ) / (k : ℝ) = (1 : ℝ) / Real.sqrt (k : ℝ) ^ 2 := by
        intro k hk
        rw [Finset.mem_Icc] at hk
        have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk.1
        rw [Real.sq_sqrt hkpos.le]
      rw [Finset.sum_congr rfl hfun] at h4
      exact h4
    have hK4 : (n : ℝ) ≤ 4 * (K : ℝ) := four_K_ge n (by omega)
    have hnnn : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hKpos : (0:ℝ) < (K:ℝ) := by nlinarith
    have hlog4 : Real.log 4 ≤ Real.log (n : ℝ) / 2 := by
      have hlog16 : Real.log 16 ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by norm_num) hnnn
      have h16 : Real.log (16 : ℝ) = 2 * Real.log 4 := by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
        push_cast; ring
      linarith
    have hlogK1 : Real.log (n : ℝ) / 2 ≤ Real.log ((K : ℝ) + 1) := by
      have hmono4K : Real.log (n : ℝ) ≤ Real.log (4 * (K:ℝ)) :=
        Real.log_le_log (by linarith) hK4
      have hsplit4K : Real.log (4 * (K:ℝ)) = Real.log 4 + Real.log (K:ℝ) := by
        rw [Real.log_mul (by norm_num) (ne_of_gt hKpos)]
      have hKK1 : Real.log (K:ℝ) ≤ Real.log ((K:ℝ) + 1) :=
        Real.log_le_log hKpos (by linarith)
      linarith
    rw [hrateeq]
    calc c₁ / 2 * Real.log (n : ℝ) = c₁ * (Real.log (n:ℝ) / 2) := by ring
      _ ≤ c₁ * Real.log ((K : ℝ) + 1) := mul_le_mul_of_nonneg_left hlogK1 hc₁.le
      _ ≤ c₁ * ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / Real.sqrt (k : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left h4' hc₁.le
      _ ≤ ∑ k ∈ Finset.Icc 1 K, Parking.heat 2 (2 * k) 0 := h3
      _ ≤ Parking.green 2 n 0 := h2
      _ ≤ Parking.greenMax 2 n := h1
  have hratemono : Monotone (fun n : ℕ => Parking.External.greenMaxRate 2 n) := by
    intro m n hmn
    simp only [hrateeq]
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0; simp
      · simp only [Nat.cast_zero, Real.log_zero]
        exact Real.log_nonneg (by exact_mod_cast hnpos)
    · exact Real.log_le_log (by exact_mod_cast hmpos) (by exact_mod_cast hmn)
  have hrate2 : 0 < Parking.External.greenMaxRate 2 2 := by
    rw [hrateeq]
    exact Real.log_pos (by norm_num)
  exact exists_greenMax_lower_of_eventual 2 (by norm_num)
    (fun n => Parking.External.greenMaxRate 2 n) hratemono hrate2 16 c₀ hc₀ hev

private theorem exists_max_lower_high {d : ℕ} (hd3 : 3 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n →
      c * Parking.External.greenMaxRate d n ≤ Parking.greenMax d n := by
  refine ⟨1, one_pos, fun n hn => ?_⟩
  have hrateeq : Parking.External.greenMaxRate d n = 1 := by
    rw [Parking.External.greenMaxRate, if_neg (by omega), if_neg (by omega)]
  rw [hrateeq, one_mul]
  have hbdd : BddAbove (Set.range fun x => Parking.green d n x) :=
    ⟨n, by rintro _ ⟨x, rfl⟩; exact Parking.green_le (by omega) n x⟩
  have h1 : Parking.green d n 0 ≤ Parking.greenMax d n := le_ciSup hbdd 0
  have h2 : Parking.heat d 0 0 ≤ Parking.green d n 0 := by
    show Parking.heat d 0 0 ≤ ∑ j ∈ Finset.range n, Parking.heat d j 0
    exact Finset.single_le_sum (fun j _ => Parking.heat_nonneg j 0)
      (Finset.mem_range.mpr (by omega))
  have h3 : Parking.heat d 0 0 = 1 := by
    show (if (0 : Parking.Site d) = 0 then (1 : ℝ) else 0) = 1
    rw [if_pos rfl]
  linarith [h1, h2, h3]

/-! ### The max-norm upper bound, dimension by dimension. -/

private theorem exists_max_upper_one :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      Parking.greenMax 1 n ≤ C * Parking.External.greenMaxRate 1 n := by
  set B : ℝ := 2 * (Real.sqrt 2 * LatticeProb.greenConst 1) with hB
  have hBnonneg : 0 ≤ B := by
    have hgc := LatticeProb.greenConst_nonneg 1
    have hs : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    positivity
  have hsqrt2pos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨1 / Real.sqrt 2 + B, add_pos_of_pos_of_nonneg (by positivity) hBnonneg, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hbdd : BddAbove (Set.range fun x => Parking.green 1 n x) :=
    ⟨n, by rintro _ ⟨x, rfl⟩; simpa using Parking.green_le (le_refl 1) n x⟩
  apply ciSup_le
  intro x
  have hub := LatticeProb.srwGreen_one_dim_le n hn1 x
  rw [← Parking.green_eq_srwGreen] at hub
  have hraten : Real.sqrt (2 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hle : (1 : ℝ) ≤ (1 / Real.sqrt 2) * Real.sqrt n := by
    calc (1 : ℝ) = (1 / Real.sqrt 2) * Real.sqrt 2 := by field_simp
      _ ≤ (1 / Real.sqrt 2) * Real.sqrt n :=
          mul_le_mul_of_nonneg_left hraten (by positivity)
  have hrateeq : Parking.External.greenMaxRate 1 n = Real.sqrt (n : ℝ) := by
    rw [Parking.External.greenMaxRate, if_pos rfl, Real.sqrt_eq_rpow]
  rw [hrateeq]
  nlinarith [hub, hle, hBnonneg, Real.sqrt_nonneg (n : ℝ)]

private theorem exists_max_upper_two :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      Parking.greenMax 2 n ≤ C * Parking.External.greenMaxRate 2 n := by
  set B : ℝ := Real.sqrt 2 ^ 2 * LatticeProb.greenConst 2 with hB
  have hBnonneg : 0 ≤ B := by
    have hgc := LatticeProb.greenConst_nonneg 2
    positivity
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨(1 + B) / Real.log 2 + B,
    add_pos_of_pos_of_nonneg (div_pos (by linarith) hlog2pos) hBnonneg, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hbdd : BddAbove (Set.range fun x => Parking.green 2 n x) :=
    ⟨n, by rintro _ ⟨x, rfl⟩; simpa using Parking.green_le (by norm_num) n x⟩
  apply ciSup_le
  intro x
  have hub := LatticeProb.srwGreen_two_dim_le n hn1 x
  rw [← Parking.green_eq_srwGreen] at hub
  have hraten : Real.log (2 : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hle : (1 + B : ℝ) ≤ ((1 + B) / Real.log 2) * Real.log n := by
    calc (1 + B : ℝ) = ((1 + B) / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ ((1 + B) / Real.log 2) * Real.log n :=
          mul_le_mul_of_nonneg_left hraten (by positivity)
  have hrateeq : Parking.External.greenMaxRate 2 n = Real.log (n : ℝ) := by
    rw [Parking.External.greenMaxRate, if_neg (by norm_num), if_pos rfl]
  rw [hrateeq]
  nlinarith [hub, hle, hBnonneg]

private theorem exists_max_upper_high {d : ℕ} (hd3 : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      Parking.greenMax d n ≤ C * Parking.External.greenMaxRate d n := by
  have hCpos : (0:ℝ) < 1 + 3 * (Real.sqrt 2 ^ d * LatticeProb.greenConst d) := by
    have hgc := LatticeProb.greenConst_nonneg d
    have hs : (0:ℝ) ≤ Real.sqrt 2 ^ d := pow_nonneg (Real.sqrt_nonneg 2) d
    nlinarith [mul_nonneg hs hgc]
  refine ⟨1 + 3 * (Real.sqrt 2 ^ d * LatticeProb.greenConst d), hCpos, fun n hn => ?_⟩
  have hrateeq : Parking.External.greenMaxRate d n = 1 := by
    rw [Parking.External.greenMaxRate, if_neg (by omega), if_neg (by omega)]
  rw [hrateeq, mul_one]
  have hn1 : 1 ≤ n := by omega
  have hbdd : BddAbove (Set.range fun x => Parking.green d n x) :=
    ⟨n, by rintro _ ⟨x, rfl⟩; simpa using Parking.green_le (by omega) n x⟩
  apply ciSup_le
  intro x
  have hub := LatticeProb.srwGreen_high_dim_le hd3 n hn1 x
  rw [← Parking.green_eq_srwGreen] at hub
  exact hub

/-! ### The ℓ² clause, at every dimension simultaneously. -/

private theorem l2Norm_green_eq (d n : ℕ) :
    Parking.l2Norm (Parking.green d n)
      = Real.sqrt (∑' x : Parking.Site d, LatticeProb.srwGreen d n x ^ 2) := by
  show Real.sqrt (∑' x : Parking.Site d, Parking.green d n x ^ 2) = _
  congr 1
  exact tsum_congr fun x => by rw [Parking.green_eq_srwGreen]

private theorem greenL2Rate_eq (d n : ℕ) :
    Parking.External.greenL2Rate d n = Real.sqrt (LatticeProb.varianceRate d n) := by
  rw [Parking.External.greenL2Rate, LatticeProb.varianceRate]
  split_ifs with h1 h2 h3 h4
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    norm_num
  · rw [Real.sqrt_eq_rpow]
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    norm_num
  · rfl
  · norm_num

private theorem exists_l2_bounds (d : ℕ) (hd : 1 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      c * Parking.External.greenL2Rate d n ≤ Parking.l2Norm (Parking.green d n) ∧
        Parking.l2Norm (Parking.green d n) ≤ C * Parking.External.greenL2Rate d n := by
  obtain ⟨c, C, hc, hC, h⟩ := LatticeProb.exists_tsum_srwGreen_sq_bounds (d := d) hd
  have hvarnonneg : ∀ n : ℕ, 0 ≤ LatticeProb.varianceRate d n := by
    intro n
    rw [LatticeProb.varianceRate]
    split_ifs <;> positivity
  refine ⟨Real.sqrt c, Real.sqrt C, Real.sqrt_pos.mpr hc, Real.sqrt_pos.mpr hC, fun n hn => ?_⟩
  obtain ⟨hlow, hup⟩ := h n hn
  rw [l2Norm_green_eq, greenL2Rate_eq]
  constructor
  · rw [← Real.sqrt_mul hc.le]
    exact Real.sqrt_le_sqrt hlow
  · rw [← Real.sqrt_mul hC.le]
    exact Real.sqrt_le_sqrt hup

/-! ### Assembly. -/

private theorem greenNorms_proof : Parking.External.GreenNorms := by
  intro d hd
  refine ⟨exists_l2_bounds d hd, ?_⟩
  rcases eq_or_ne d 1 with rfl | hd1
  · obtain ⟨c, hc, hclow⟩ := exists_max_lower_one
    obtain ⟨C, hC, hcup⟩ := exists_max_upper_one
    exact ⟨c, C, hc, hC, fun n hn => ⟨hclow n hn, hcup n hn⟩⟩
  · rcases eq_or_ne d 2 with rfl | hd2
    · obtain ⟨c, hc, hclow⟩ := exists_max_lower_two
      obtain ⟨C, hC, hcup⟩ := exists_max_upper_two
      exact ⟨c, C, hc, hC, fun n hn => ⟨hclow n hn, hcup n hn⟩⟩
    · have hd3 : 3 ≤ d := by omega
      obtain ⟨c, hc, hclow⟩ := exists_max_lower_high hd3
      obtain ⟨C, hC, hcup⟩ := exists_max_upper_high hd3
      exact ⟨c, C, hc, hC, fun n hn => ⟨hclow n hn, hcup n hn⟩⟩

-- FROZEN-STATEMENT-BEGIN
/-- The two-sided rates of `eq:green-norms`, proved rather than assumed. -/
theorem Parking.External.greenNorms : Parking.External.GreenNorms
-- FROZEN-STATEMENT-END
:= greenNorms_proof
