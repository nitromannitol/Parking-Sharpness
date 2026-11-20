import Parking.Support.DVRateScaling
import LatticeProb.Walk.LocalCLTWindow
import LatticeProb.Walk.IntersectionMoment
import LatticeProb.Walk.SRWPos

/-!
# Hitting a dense part of a box

Let `Q` be a box of side `m` of the lattice and `A ⊆ Q` a set of at least `δ m^d` sites.  From
any site of `Q`, the walk visits `A` during the times `[1, 2m^2]` with probability at least a
constant `p₀ > 0` depending only on `δ` and `d` (`exists_hit_prob_ge`), once `m` is large.

By the local central limit theorem (`LatticeProb.LocalCLT.exists_window_abs_srwHeat_sub_gauss_lt`) the
heat kernel is at least `g₀ m^{-d}` at times in `[m^2, 2m^2]` and distances at most `m` with the
right parity (`exists_srwHeat_ge`).  Of two consecutive times one has the right parity, so over
`2K` consecutive times in `[m^2, 2m^2]`, `K = ⌊m^2/2⌋`, the walk is in `A` at least
`δ K g₀` times in expectation, and each event `X_j ∈ A` lies in the hitting event; hence
`2K P(hit) ≥ δ K g₀`.
-/

noncomputable section

namespace Parking

open LatticeProb MeasureTheory

variable {d : ℕ}

/-! ### Boxes -/

/-- The box of side `m` with coarse index `z`. -/
def boxCell (m : ℕ) [NeZero m] (z : Site d) : Finset (Site d) :=
  cellsOver m {z}

theorem mem_boxCell {m : ℕ} [NeZero m] {z y : Site d} :
    y ∈ boxCell m z ↔ (fullSplit m y).1 = z := by
  rw [boxCell, mem_cellsOver, Finset.mem_singleton]

theorem card_boxCell (m : ℕ) [NeZero m] (z : Site d) : (boxCell m z).card = m ^ d := by
  classical
  rw [boxCell, cellsOver, Finset.card_image_of_injective _ (fullSplit m).symm.injective,
    Finset.card_product, Finset.card_singleton, one_mul, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]

theorem self_mem_boxCell (m : ℕ) [NeZero m] (y : Site d) : y ∈ boxCell m (fullSplit m y).1 :=
  mem_boxCell.mpr rfl

/-- Two sites of one box differ by less than `m` in every coordinate. -/
theorem abs_sub_le_of_mem_boxCell {m : ℕ} [NeZero m] {z x y : Site d} (hx : x ∈ boxCell m z)
    (hy : y ∈ boxCell m z) (i : Fin d) : |x i - y i| ≤ (m : ℤ) - 1 := by
  have hm : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_neZero m
  rw [mem_boxCell, fullSplit_fst] at hx hy
  have hxi := congrFun hx i
  have hyi := congrFun hy i
  have ex := Int.emod_add_mul_ediv (x i) m
  have ey := Int.emod_add_mul_ediv (y i) m
  have h1 := Int.emod_nonneg (x i) hm.ne'
  have h2 := Int.emod_lt_of_pos (x i) hm
  have h3 := Int.emod_nonneg (y i) hm.ne'
  have h4 := Int.emod_lt_of_pos (y i) hm
  rw [hxi] at ex
  rw [hyi] at ey
  rw [abs_le]
  constructor <;> linarith

/-! ### A lower bound for the heat kernel -/

/-- **The heat kernel on the diffusive window**: `p_j(z) ≥ g₀ m^{-d}` for `j ∈ [m^2, 2m^2]`,
`|z_i| ≤ m` and `j` of the parity of `z`, once `m` is large. -/
theorem exists_srwHeat_ge (hd : 1 ≤ d) :
    ∃ g₀ : ℝ, 0 < g₀ ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ j : ℕ, m ^ 2 ≤ j → j ≤ 2 * m ^ 2 →
      ∀ z : Site d, (∀ i, |z i| ≤ (m : ℤ)) → graphNorm z % 2 = j % 2 →
        g₀ / (m : ℝ) ^ d ≤ srwHeat d j z := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set g₀ : ℝ := (4 * Real.pi / d) ^ (-(d : ℝ) / 2) * Real.exp (-((d : ℝ) * d / 2)) with hg₀
  have hg₀pos : 0 < g₀ := by positivity
  obtain ⟨R₀, hR₀⟩ := LocalCLT.exists_window_abs_srwHeat_sub_gauss_lt d hd 1 2 (Real.sqrt d) one_pos
    (by norm_num) (Real.sqrt_nonneg _) g₀ hg₀pos
  refine ⟨g₀, hg₀pos, max d (⌈R₀⌉₊ + 1), fun m hm j hj1 hj2 z hz hpar => ?_⟩
  have hmd : d ≤ m := le_trans (le_max_left _ _) hm
  have hmR : R₀ ≤ m := by
    have : ⌈R₀⌉₊ + 1 ≤ m := le_trans (le_max_right _ _) hm
    have h1 : R₀ ≤ ⌈R₀⌉₊ := Nat.le_ceil R₀
    have h2 : ((⌈R₀⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast this
    push_cast at h2
    linarith
  have hm1 : 1 ≤ m := le_trans hd hmd
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  -- positivity of the kernel
  have hgn : graphNorm z ≤ j := by
    have h1 : graphNorm z ≤ d * m := by
      unfold graphNorm
      calc ∑ i, (z i).natAbs ≤ ∑ _i : Fin d, m := Finset.sum_le_sum fun i _ => by
            have h := hz i
            rw [abs_le] at h
            omega
        _ = d * m := by simp
    have h2 : d * m ≤ m ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right m hmd
    omega
  have hpos : 0 < srwHeat d j z := srwHeat_pos hd hgn hpar
  have hj1r : (m : ℝ) ^ 2 ≤ j := by exact_mod_cast hj1
  have hj2r : (j : ℝ) ≤ 2 * (m : ℝ) ^ 2 := by exact_mod_cast hj2
  have hsq : ∑ i, ((z i : ℝ) - ((0 : Site d) i : ℝ)) ^ 2 ≤ (Real.sqrt d * m) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hd0.le]
    calc ∑ i, ((z i : ℝ) - ((0 : Site d) i : ℝ)) ^ 2 ≤ ∑ _i : Fin d, (m : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          simp only [Pi.zero_apply, Int.cast_zero, sub_zero]
          have : |(z i : ℝ)| ≤ m := by exact_mod_cast hz i
          calc (z i : ℝ) ^ 2 = |(z i : ℝ)| ^ 2 := (sq_abs _).symm
            _ ≤ (m : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = d * (m : ℝ) ^ 2 := by simp
  have hwin := hR₀ m hmR j (by linarith) hj2r z 0 hsq (by simpa using hpos)
  simp only [sub_zero] at hwin
  -- the Gaussian factor is at least `g₀`
  set s : ℝ := (j : ℝ) / (m : ℝ) ^ 2 with hs
  have hs1 : 1 ≤ s := by rw [hs, le_div_iff₀ (by positivity)]; linarith
  have hs2 : s ≤ 2 := by rw [hs, div_le_iff₀ (by positivity)]; linarith
  have hG : g₀ ≤ (4 * Real.pi * s / (2 * d)) ^ (-(d : ℝ) / 2) *
      Real.exp (-(d : ℝ) * (∑ i, ((z i : ℝ) / m - ((0 : Site d) i : ℝ) / m) ^ 2) / (2 * s)) := by
    have hb : 4 * Real.pi * s / (2 * d) ≤ 4 * Real.pi / d := by
      rw [div_le_div_iff₀ (by positivity) hd0]
      nlinarith [mul_nonneg (sub_nonneg.mpr hs2) (by positivity : (0 : ℝ) ≤ 4 * Real.pi * d)]
    have h1 : (4 * Real.pi / d) ^ (-(d : ℝ) / 2) ≤ (4 * Real.pi * s / (2 * d)) ^ (-(d : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hb (by linarith)
    have hsum : ∑ i, ((z i : ℝ) / m - ((0 : Site d) i : ℝ) / m) ^ 2 ≤ d := by
      calc ∑ i, ((z i : ℝ) / m - ((0 : Site d) i : ℝ) / m) ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
            refine Finset.sum_le_sum fun i _ => ?_
            simp only [Pi.zero_apply, Int.cast_zero, zero_div, sub_zero, div_pow]
            rw [div_le_one (by positivity)]
            have : |(z i : ℝ)| ≤ m := by exact_mod_cast hz i
            calc (z i : ℝ) ^ 2 = |(z i : ℝ)| ^ 2 := (sq_abs _).symm
              _ ≤ (m : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = d := by simp
    have h2 : Real.exp (-((d : ℝ) * d / 2)) ≤ Real.exp (-(d : ℝ) *
        (∑ i, ((z i : ℝ) / m - ((0 : Site d) i : ℝ) / m) ^ 2) / (2 * s)) := by
      refine Real.exp_le_exp.mpr ?_
      rw [neg_mul, neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
      have h0 : 0 ≤ ∑ i, ((z i : ℝ) / m - ((0 : Site d) i : ℝ) / m) ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      nlinarith
    rw [hg₀]
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hmd' : (0 : ℝ) < (m : ℝ) ^ d := by positivity
  set X := 2 * ((m : ℝ) ^ d)⁻¹ * ((4 * Real.pi * s / (2 * d)) ^ (-(d : ℝ) / 2) *
      Real.exp (-(d : ℝ) * (∑ i, ((z i : ℝ) / m - ((0 : Site d) i : ℝ) / m) ^ 2) / (2 * s)))
    with hX
  have h3 : (m : ℝ) ^ d * (X - srwHeat d j z) < g₀ :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact le_abs_self _)
      hmd'.le) hwin
  have h4 : 2 * g₀ ≤ (m : ℝ) ^ d * X := by
    have hmX : (m : ℝ) ^ d * X = 2 * ((4 * Real.pi * s / (2 * d)) ^ (-(d : ℝ) / 2) *
        Real.exp (-(d : ℝ) * (∑ i, ((z i : ℝ) / m - ((0 : Site d) i : ℝ) / m) ^ 2) / (2 * s))) := by
      rw [hX]
      field_simp
    rw [hmX]
    linarith
  rw [div_le_iff₀ hmd']
  nlinarith

theorem sum_range_two_mul (f : ℕ → ℝ) (K : ℕ) :
    ∑ k ∈ Finset.range (2 * K), f k = ∑ i ∈ Finset.range K, (f (2 * i) + f (2 * i + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
        ih, Finset.sum_range_succ]
      ring

/-- `P_y(X_n ∈ A) = ∑_{x ∈ A} p_n(x - y)`. -/
theorem measureReal_eval_mem (hd : 1 ≤ d) (y : Site d) (n : ℕ) (A : Finset (Site d)) :
    (siteWalkLaw d y).real {Y | Y n ∈ A} = ∑ x ∈ A, srwHeat d n (x - y) := by
  classical
  have : NeZero d := ⟨by omega⟩
  have hset : {Y : ℕ → Site d | Y n ∈ A} = ⋃ x ∈ A, {Y | Y n = x} := by
    ext Y; simp
  rw [hset, measureReal_biUnion_finset]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [measureReal_def, Intersection.siteWalkLaw_eval_eq, ENNReal.toReal_ofReal (srwHeat_nonneg _ _)]
  · intro a _ b _ hab
    exact Set.disjoint_left.mpr fun Y h1 h2 => hab (h1.symm.trans h2)
  · intro x _
    exact Intersection.measurableSet_eval_eq n x

/-- **Hitting a dense part of a box.**  There are `p₀ > 0` and `m₀` such that from any site of a
box of side `m ≥ m₀`, the walk visits any set `A` of at least `δ m^d` sites of the box during the
times `[1, 2m^2]` with probability at least `p₀`. -/
theorem exists_hit_prob_ge (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ [NeZero m] (z y : Site d),
      y ∈ boxCell m z → ∀ A : Finset (Site d), A ⊆ boxCell m z → δ * (m : ℝ) ^ d ≤ A.card →
        p₀ ≤ (siteWalkLaw d y).real {Y | ∃ j, 1 ≤ j ∧ j ≤ 2 * m ^ 2 ∧ Y j ∈ A} := by
  classical
  have : NeZero d := ⟨by omega⟩
  obtain ⟨g₀, hg₀, m₁, hm₁⟩ := exists_srwHeat_ge hd
  refine ⟨δ * g₀ / 2, by positivity, max m₁ 2, fun m hm _ z y hy A hA hAcard => ?_⟩
  have hm2 : 2 ≤ m := le_trans (le_max_right _ _) hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  set K := m ^ 2 / 2 with hK
  have hK1 : 1 ≤ K := by
    rw [hK]
    have : 4 ≤ m ^ 2 := by nlinarith
    omega
  have hK2 : 2 * K ≤ m ^ 2 := by rw [hK]; omega
  set H : Set (ℕ → Site d) := {Y | ∃ j, 1 ≤ j ∧ j ≤ 2 * m ^ 2 ∧ Y j ∈ A}
  have hsub : ∀ k < 2 * K, {Y : ℕ → Site d | Y (m ^ 2 + k) ∈ A} ⊆ H := by
    intro k hk Y hY
    exact ⟨m ^ 2 + k, by nlinarith, by omega, hY⟩
  have hle : ∑ k ∈ Finset.range (2 * K), (siteWalkLaw d y).real {Y | Y (m ^ 2 + k) ∈ A}
      ≤ (2 * K : ℕ) * (siteWalkLaw d y).real H := by
    calc ∑ k ∈ Finset.range (2 * K), (siteWalkLaw d y).real {Y | Y (m ^ 2 + k) ∈ A}
        ≤ ∑ _k ∈ Finset.range (2 * K), (siteWalkLaw d y).real H :=
          Finset.sum_le_sum fun k hk => measureReal_mono (hsub k (Finset.mem_range.mp hk))
      _ = (2 * K : ℕ) * (siteWalkLaw d y).real H := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- the lower bound on the expected number of visits
  have hpair : ∀ x ∈ A, ∀ i < K,
      g₀ / (m : ℝ) ^ d ≤ srwHeat d (m ^ 2 + 2 * i) (x - y) + srwHeat d (m ^ 2 + (2 * i + 1)) (x - y) := by
    intro x hx i hi
    have hxy : ∀ k, |(x - y) k| ≤ (m : ℤ) := fun k => by
      have := abs_sub_le_of_mem_boxCell (hA hx) hy k
      simp only [Pi.sub_apply]
      omega
    have h0 := srwHeat_nonneg (d := d) (m ^ 2 + 2 * i) (x - y)
    have h1 := srwHeat_nonneg (d := d) (m ^ 2 + (2 * i + 1)) (x - y)
    rcases Nat.even_or_odd (graphNorm (x - y) + m ^ 2) with he | ho
    · have hpar : graphNorm (x - y) % 2 = (m ^ 2 + 2 * i) % 2 := by
        obtain ⟨r, hr⟩ := he; omega
      have := hm₁ m (le_trans (le_max_left _ _) hm) (m ^ 2 + 2 * i) (by omega) (by omega)
        (x - y) hxy hpar
      linarith
    · have hpar : graphNorm (x - y) % 2 = (m ^ 2 + (2 * i + 1)) % 2 := by
        obtain ⟨r, hr⟩ := ho; omega
      have := hm₁ m (le_trans (le_max_left _ _) hm) (m ^ 2 + (2 * i + 1)) (by omega) (by omega)
        (x - y) hxy hpar
      linarith
  have hlow : δ * K * g₀ ≤ ∑ k ∈ Finset.range (2 * K),
      (siteWalkLaw d y).real {Y | Y (m ^ 2 + k) ∈ A} := by
    simp_rw [measureReal_eval_mem hd]
    rw [Finset.sum_comm]
    have hx : ∀ x ∈ A, (K : ℝ) * (g₀ / (m : ℝ) ^ d)
        ≤ ∑ k ∈ Finset.range (2 * K), srwHeat d (m ^ 2 + k) (x - y) := by
      intro x hx
      rw [sum_range_two_mul (fun k => srwHeat d (m ^ 2 + k) (x - y))]
      calc (K : ℝ) * (g₀ / (m : ℝ) ^ d) = ∑ _i ∈ Finset.range K, g₀ / (m : ℝ) ^ d := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum fun i hi => hpair x hx i (Finset.mem_range.mp hi)
    calc δ * K * g₀ = (δ * (m : ℝ) ^ d) * ((K : ℝ) * (g₀ / (m : ℝ) ^ d)) := by
          field_simp
      _ ≤ (A.card : ℝ) * ((K : ℝ) * (g₀ / (m : ℝ) ^ d)) :=
          mul_le_mul_of_nonneg_right hAcard (by positivity)
      _ = ∑ _x ∈ A, (K : ℝ) * (g₀ / (m : ℝ) ^ d) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hx
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK1
  have := hlow.trans hle
  push_cast at this
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  nlinarith

end Parking

end
