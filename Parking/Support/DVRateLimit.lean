import Parking.Support.DVRateScaling

/-!
# The Faber-Krahn constant of the lattice

`n^{2/d} · dirichletRate d n` converges as `n → ∞` (`exists_tendsto_dirichletRate`).  The limit
is the Faber-Krahn constant of the walk: the least Dirichlet eigenvalue of a region of unit
volume for the generator of the walk, a fact not needed here, only the existence of the limit.

The proof uses nothing but the blow-up `dirichletRate_blowup` and the monotonicity of the rate.
A near optimal function at volume `n₀`, blown up at scale `L`, bounds the rate at volume about
`L^d n₀` by `L^{-2}` times the rate at `n₀`, up to factors tending to one as `n₀` and `L` grow.
Every large `n` lies between `L^d n₀` and `(L + 1)^d n₀` for some `L`, so the sequence is
eventually at most `(1 + ε)` times any of its late values, and its upper limit is its lower
limit.  The bound `dirichletRate d n ≤ C n^{-2/d}` comes the same way from the indicator of a
box of side `4d`.
-/

noncomputable section

namespace Parking

open LatticeProb Filter Topology

variable {d : ℕ}

/-! ### Choosing the scale -/

/-- Every `n ≥ A` lies in `[A L^d, A (L + 1)^d)` for some `L ≥ 1`. -/
theorem exists_scale (hd : 1 ≤ d) {A x : ℝ} (hA : 0 < A) (hx : A ≤ x) :
    ∃ L : ℕ, 1 ≤ L ∧ A * (L : ℝ) ^ d ≤ x ∧ x < A * ((L : ℝ) + 1) ^ d := by
  classical
  set B : ℕ := ⌈x / A⌉₊
  set L := Nat.findGreatest (fun L : ℕ => A * (L : ℝ) ^ d ≤ x) B
  have h1 : (fun L : ℕ => A * (L : ℝ) ^ d ≤ x) 1 := by simpa using hx
  have hB : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr fun h => by
    have : x / A ≤ 0 := Nat.ceil_eq_zero.mp h
    have : 0 < x / A := div_pos (hA.trans_le hx) hA
    linarith
  have hL1 : 1 ≤ L := Nat.le_findGreatest (P := fun L : ℕ => A * (L : ℝ) ^ d ≤ x) hB h1
  have hLspec : A * (L : ℝ) ^ d ≤ x :=
    Nat.findGreatest_spec (P := fun L : ℕ => A * (L : ℝ) ^ d ≤ x) hB h1
  refine ⟨L, hL1, hLspec, ?_⟩
  by_contra hcon
  push Not at hcon
  have hle : L + 1 ≤ B := by
    by_contra hgt
    push Not at hgt
    have hB' : (B : ℝ) < L + 1 := by exact_mod_cast hgt
    have hxA : x / A ≤ B := Nat.le_ceil _
    have hpow : ((L : ℝ) + 1) ≤ ((L : ℝ) + 1) ^ d :=
      le_self_pow₀ (by linarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]) (by omega)
    have : x < A * ((L : ℝ) + 1) := by
      rw [div_le_iff₀ hA] at hxA
      nlinarith
    nlinarith
  have := Nat.findGreatest_is_greatest (Nat.lt_succ_self L) hle
  exact this (by exact_mod_cast hcon)

/-- `((L + 1)^d A)^{2/d} = (L + 1)^2 A^{2/d}`. -/
theorem rpow_two_div_scale (hd : 1 ≤ d) {A y : ℝ} (hA : 0 ≤ A) (hy : 0 ≤ y) :
    (A * y ^ d) ^ ((2 : ℝ) / d) = A ^ ((2 : ℝ) / d) * y ^ 2 := by
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [Real.mul_rpow hA (by positivity), ← Real.rpow_natCast y d, ← Real.rpow_mul hy,
    mul_div_cancel₀ _ hd0]
  norm_num

/-! ### A box -/

/-- The box `[0, ℓ)^d`. -/
def cornerBox (d ℓ : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun _ => Finset.Ico (0 : ℤ) ℓ

/-- The indicator of the box `[0, ℓ)^d`. -/
def boxInd (d ℓ : ℕ) (x : Site d) : ℝ :=
  if x ∈ cornerBox d ℓ then 1 else 0

theorem card_cornerBox (ℓ : ℕ) : (cornerBox d ℓ).card = ℓ ^ d := by
  simp [cornerBox, Fintype.card_piFinset]

theorem card_fatten_cornerBox_le (ℓ : ℕ) : (fatten (cornerBox d ℓ)).card ≤ (ℓ + 1) ^ d := by
  classical
  have hsub : fatten (cornerBox d ℓ) ⊆ Fintype.piFinset fun _ => Finset.Ico (-1 : ℤ) ℓ := by
    intro x hx
    obtain ⟨S, hS⟩ := mem_fatten.mp hx
    rw [cornerBox, Fintype.mem_piFinset] at hS
    rw [Fintype.mem_piFinset]
    intro j
    have := hS j
    rw [Pi.add_apply, sum_unit_apply, Finset.mem_Ico] at this
    rw [Finset.mem_Ico]
    split_ifs at this <;> omega
  refine (Finset.card_le_card hsub).trans (le_of_eq ?_)
  simp only [Fintype.card_piFinset, Int.card_Ico, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1

theorem boxInd_eq_zero {ℓ : ℕ} {x : Site d} (hx : x ∉ cornerBox d ℓ) : boxInd d ℓ x = 0 := by
  simp [boxInd, hx]

theorem sqMass_boxInd (ℓ : ℕ) : sqMass (boxInd d ℓ) = (ℓ : ℝ) ^ d := by
  rw [sqMass_eq_sum (V := cornerBox d ℓ) fun x hx => boxInd_eq_zero hx]
  have h1 : ∀ x ∈ cornerBox d ℓ, boxInd d ℓ x ^ 2 = 1 := fun x hx => by simp [boxInd, hx]
  rw [Finset.sum_congr rfl h1]
  simp [card_cornerBox]

theorem dirEnergy_boxInd_le (hd : 1 ≤ d) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (i : Fin d) :
    dirEnergy i (boxInd d ℓ) ≤ 2 * (ℓ : ℝ) ^ (d - 1) := by
  classical
  have hfs : FinSupp (boxInd d ℓ) := ⟨cornerBox d ℓ, fun x hx => boxInd_eq_zero hx⟩
  rw [dirEnergy_eq hfs, sqMass_boxInd]
  set face : Finset (Site d) := (cornerBox d ℓ).filter fun x => x i = (ℓ : ℤ) - 1
  have hface : face.card = ℓ ^ (d - 1) := by
    have := Fintype.card_filter_piFinset_const_eq_of_mem (Finset.Ico (0 : ℤ) ℓ) i
      (x := (ℓ : ℤ) - 1) (by simp only [Finset.mem_Ico]; omega)
    simpa [face, cornerBox] using this
  have hpt : ∀ x ∈ cornerBox d ℓ, (1 : ℝ) - (if x ∈ face then 1 else 0)
      ≤ boxInd d ℓ x * boxInd d ℓ (x + unit i) := by
    intro x hx
    by_cases hf : x ∈ face
    · rw [ite_eq_left hf, sub_self]
      unfold boxInd
      split_ifs <;> norm_num
    · rw [ite_eq_right hf, sub_zero]
      have hx' := hx
      rw [cornerBox, Fintype.mem_piFinset] at hx'
      have hxi : x i ≠ (ℓ : ℤ) - 1 := fun h => hf (Finset.mem_filter.mpr ⟨hx, h⟩)
      have hshift : x + unit i ∈ cornerBox d ℓ := by
        rw [cornerBox, Fintype.mem_piFinset]
        intro j
        have := hx' j
        simp only [Pi.add_apply, unit, Pi.single_apply, Finset.mem_Ico] at this ⊢
        by_cases hj : j = i
        · subst hj; simp only [ite_true]; omega
        · rw [ite_eq_right hj]; omega
      rw [boxInd, ite_eq_left hx, boxInd, ite_eq_left hshift, mul_one]
  have hinner : (ℓ : ℝ) ^ d - (ℓ : ℝ) ^ (d - 1)
      ≤ ∑' x, boxInd d ℓ x * boxInd d ℓ (x + unit i) := by
    rw [tsum_eq_sum (s := cornerBox d ℓ) fun x hx => by rw [boxInd_eq_zero hx, zero_mul]]
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum hpt)
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, card_cornerBox,
      ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : (cornerBox d ℓ).filter (fun x => x ∈ face) = face := by
      ext x
      simp only [Finset.mem_filter, and_iff_right_iff_imp]
      exact fun h => (Finset.mem_filter.mp h).1
    rw [this, hface]
    push_cast
    ring
  have hpow : (ℓ : ℝ) ^ d = ℓ * (ℓ : ℝ) ^ (d - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  nlinarith

theorem latEnergy_boxInd_le (hd : 1 ≤ d) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    latEnergy (boxInd d ℓ) ≤ (ℓ : ℝ) ^ (d - 1) := by
  have hd0 : (0 : ℝ) < 2 * d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  unfold latEnergy
  rw [div_le_iff₀ hd0]
  calc ∑ i, dirEnergy i (boxInd d ℓ) ≤ ∑ _i : Fin d, 2 * (ℓ : ℝ) ^ (d - 1) :=
        Finset.sum_le_sum fun i _ => dirEnergy_boxInd_le hd hℓ i
    _ = (ℓ : ℝ) ^ (d - 1) * (2 * d) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### The upper bound `dirichletRate d n ≤ C n^{-2/d}` -/

/-- The rate is at most `1/(2d L^2)` at the volume `K L^d`, `K = (4d + 1)^d (1 + d 2^d)`. -/
theorem dirichletRate_scale_le (hd : 1 ≤ d) (L : ℕ) (hL : 1 ≤ L) :
    dirichletRate d ((4 * d + 1) ^ d * (1 + d * 2 ^ d) * L ^ d) ≤ 1 / (2 * d * (L : ℝ) ^ 2) := by
  have : NeZero L := ⟨by omega⟩
  set ℓ := 4 * d with hℓ
  have hℓ1 : 1 ≤ ℓ := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hV : ∀ x ∉ cornerBox d ℓ, boxInd d ℓ x = 0 := fun x hx => boxInd_eq_zero hx
  have hE := latEnergy_boxInd_le hd hℓ1
  have hM := sqMass_boxInd (d := d) ℓ
  have hpow : (ℓ : ℝ) ^ d = ℓ * (ℓ : ℝ) ^ (d - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hℓr : (ℓ : ℝ) = 4 * d := by rw [hℓ]; push_cast; ring
  set P : ℝ := (ℓ : ℝ) ^ (d - 1) with hP
  have hpd : (0 : ℝ) < P := by positivity
  have hEd : 2 * d * latEnergy (boxInd d ℓ) ≤ 2 * d * P := by nlinarith
  have hsmall : 2 * d * latEnergy (boxInd d ℓ) < sqMass (boxInd d ℓ) := by
    rw [hM, hpow, hℓr]
    nlinarith
  have hb := dirichletRate_blowup hd L hV hsmall le_rfl
  -- the volume of the blow-up is at most `K L^d`
  have hvol : L ^ d * (fatten (cornerBox d ℓ)).card + d * L ^ (d - 1) *
      (fatten (fatten (cornerBox d ℓ))).card ≤ (ℓ + 1) ^ d * (1 + d * 2 ^ d) * L ^ d := by
    have h1 := card_fatten_cornerBox_le (d := d) ℓ
    have h2 : (fatten (fatten (cornerBox d ℓ))).card ≤ 2 ^ d * (ℓ + 1) ^ d :=
      (card_fatten_le _).trans (Nat.mul_le_mul_left _ h1)
    have h3 : L ^ (d - 1) ≤ L ^ d := Nat.pow_le_pow_right hL (by omega)
    calc L ^ d * (fatten (cornerBox d ℓ)).card + d * L ^ (d - 1) *
          (fatten (fatten (cornerBox d ℓ))).card
        ≤ L ^ d * (ℓ + 1) ^ d + d * L ^ d * (2 ^ d * (ℓ + 1) ^ d) := by
          gcongr
      _ = (ℓ + 1) ^ d * (1 + d * 2 ^ d) * L ^ d := by ring
  have hanti := dirichletRate_anti (d := d) hvol (by
    have : 2 ^ d ≤ L ^ d * (fatten (cornerBox d ℓ)).card := by
      have h0 : 2 ^ d ≤ (fatten (cornerBox d ℓ)).card := by
        have := card_le_card_fatten (cornerBox d ℓ)
        rw [card_cornerBox] at this
        exact (Nat.pow_le_pow_left (by omega) d).trans this
      exact h0.trans (Nat.le_mul_of_pos_left _ (by positivity))
    exact this.trans (Nat.le_add_right _ _))
  set ρ := dirichletRate d ((ℓ + 1) ^ d * (1 + d * 2 ^ d) * L ^ d)
  set ρ' := dirichletRate d (L ^ d * (fatten (cornerBox d ℓ)).card + d * L ^ (d - 1) *
      (fatten (fatten (cornerBox d ℓ))).card)
  have hρ0 : 0 ≤ ρ := dirichletRate_nonneg _ _
  have hgap : P * (2 * d) ≤ sqMass (boxInd d ℓ) - 2 * d * latEnergy (boxInd d ℓ) := by
    rw [hM, hpow, hℓr]
    nlinarith
  have hkey : (L : ℝ) ^ 2 * ρ * (P * (2 * d)) ≤ P := by
    calc (L : ℝ) ^ 2 * ρ * (P * (2 * d))
        ≤ (L : ℝ) ^ 2 * ρ' * (sqMass (boxInd d ℓ) - 2 * d * latEnergy (boxInd d ℓ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hanti (by positivity)) hgap (by positivity)
            (mul_nonneg (by positivity) (dirichletRate_nonneg _ _))
      _ ≤ latEnergy (boxInd d ℓ) := hb
      _ ≤ P := hE
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- **`dirichletRate d n ≤ C n^{-2/d}`.** -/
theorem exists_dirichletRate_le (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ ((2 : ℝ) / d) * dirichletRate d n ≤ C := by
  set K : ℕ := (4 * d + 1) ^ d * (1 + d * 2 ^ d) with hK
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK1
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨(K : ℝ) ^ ((2 : ℝ) / d) * 4 / (2 * d) + (K : ℝ) ^ ((2 : ℝ) / d) * 2, by positivity,
    fun n hn => ?_⟩
  have hρ0 := dirichletRate_nonneg d n
  by_cases hnK : (K : ℝ) ≤ n
  · obtain ⟨L, hL1, hlo, hhi⟩ := exists_scale hd hKr hnK
    have hLn : K * L ^ d ≤ n := by exact_mod_cast hlo
    have hrate := dirichletRate_scale_le hd L hL1
    have h2d : 2 ^ d ≤ K * L ^ d := by
      have : 2 ^ d ≤ K := by
        rw [hK]
        calc 2 ^ d ≤ (4 * d + 1) ^ d := Nat.pow_le_pow_left (by omega) d
          _ ≤ (4 * d + 1) ^ d * (1 + d * 2 ^ d) := Nat.le_mul_of_pos_right _ (by positivity)
      exact this.trans (Nat.le_mul_of_pos_right _ (by positivity))
    have hmono := dirichletRate_anti (d := d) hLn h2d
    have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    have hnpow : (n : ℝ) ^ ((2 : ℝ) / d) ≤ (K : ℝ) ^ ((2 : ℝ) / d) * ((L : ℝ) + 1) ^ 2 := by
      rw [← rpow_two_div_scale hd hKr.le (by positivity)]
      exact Real.rpow_le_rpow (by positivity) hhi.le (by positivity)
    have hKL : dirichletRate d n ≤ 1 / (2 * d * (L : ℝ) ^ 2) := hmono.trans (by
      simpa [hK] using hrate)
    calc (n : ℝ) ^ ((2 : ℝ) / d) * dirichletRate d n
        ≤ (K : ℝ) ^ ((2 : ℝ) / d) * ((L : ℝ) + 1) ^ 2 * (1 / (2 * d * (L : ℝ) ^ 2)) :=
          mul_le_mul hnpow hKL hρ0 (by positivity)
      _ ≤ (K : ℝ) ^ ((2 : ℝ) / d) * 4 / (2 * d) := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
          have hK2 : 0 ≤ (K : ℝ) ^ ((2 : ℝ) / d) := by positivity
          have : ((L : ℝ) + 1) ^ 2 ≤ 4 * (L : ℝ) ^ 2 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hK2 (by positivity :
            (0 : ℝ) ≤ 2 * d))]
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  · push Not at hnK
    have hρ1 : dirichletRate d n ≤ 2 := dirichletRate_le_two d n
    have hnpow : (n : ℝ) ^ ((2 : ℝ) / d) ≤ (K : ℝ) ^ ((2 : ℝ) / d) :=
      Real.rpow_le_rpow (by positivity) hnK.le (by positivity)
    calc (n : ℝ) ^ ((2 : ℝ) / d) * dirichletRate d n ≤ (K : ℝ) ^ ((2 : ℝ) / d) * 2 :=
          mul_le_mul hnpow hρ1 hρ0 (by positivity)
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

/-! ### The limit -/

/-- The blow-up at scale `L` of a function of ratio `r` with cube hull of at most `n₀` sites
bounds the rate at every volume `n ≥ L^d n₀ (1 + d 2^d / L)` by `r / (L^2 (1 - 2d r))`. -/
theorem dirichletRate_le_of_scale (hd : 1 ≤ d) {n₀ : ℕ} {V : Finset (Site d)} {h : Site d → ℝ}
    (hV : ∀ x ∉ V, h x = 0) (hVn : (fatten V).card ≤ n₀) (hm : 0 < sqMass h)
    (hsmall : 2 * d * (latEnergy h / sqMass h) < 1) {L : ℕ} (hL : 1 ≤ L) {n : ℕ}
    (hn : (L : ℝ) ^ d * n₀ * (1 + d * 2 ^ d / L) ≤ n) :
    dirichletRate d n
      ≤ (latEnergy h / sqMass h) / ((L : ℝ) ^ 2 * (1 - 2 * d * (latEnergy h / sqMass h))) := by
  have : NeZero L := ⟨by omega⟩
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  set r := latEnergy h / sqMass h with hr
  have hE : latEnergy h = r * sqMass h := by rw [hr]; field_simp
  have hsmall' : 2 * d * latEnergy h < sqMass h := by
    rw [hE]
    nlinarith
  have hcard : L ^ d * (fatten V).card + d * L ^ (d - 1) * (fatten (fatten V)).card ≤ n := by
    have h2 : (fatten (fatten V)).card ≤ 2 ^ d * n₀ :=
      (card_fatten_le _).trans (Nat.mul_le_mul_left _ hVn)
    have hpow : (L : ℝ) ^ (d - 1) * L = (L : ℝ) ^ d := by
      rw [← pow_succ]
      congr 1
      omega
    have hreal : ((L ^ d * (fatten V).card + d * L ^ (d - 1) * (fatten (fatten V)).card : ℕ) : ℝ)
        ≤ n := by
      push_cast
      have h1r : ((fatten V).card : ℝ) ≤ n₀ := by exact_mod_cast hVn
      have h2r : ((fatten (fatten V)).card : ℝ) ≤ 2 ^ d * n₀ := by exact_mod_cast h2
      have hexp : (L : ℝ) ^ d * n₀ * (1 + d * 2 ^ d / L)
          = (L : ℝ) ^ d * n₀ + d * (L : ℝ) ^ (d - 1) * (2 ^ d * n₀) := by
        rw [← hpow]
        field_simp
      refine le_trans ?_ (hexp ▸ hn)
      gcongr
    exact_mod_cast hreal
  have hb := dirichletRate_blowup hd L hV hsmall' hcard
  have hgap : 0 < 1 - 2 * d * r := by linarith
  rw [le_div_iff₀ (by positivity)]
  rw [hE] at hb
  have : (L : ℝ) ^ 2 * dirichletRate d n * (sqMass h * (1 - 2 * d * r)) ≤ r * sqMass h := by
    calc (L : ℝ) ^ 2 * dirichletRate d n * (sqMass h * (1 - 2 * d * r))
        = (L : ℝ) ^ 2 * dirichletRate d n * (sqMass h - 2 * d * (r * sqMass h)) := by ring
      _ ≤ r * sqMass h := hb
  nlinarith

/-- A scale `L₀` at which the interpolation factors are below `1 + ε/2`. -/
theorem exists_scale_factor_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℕ, 1 ≤ L₀ ∧ (1 + (d * 2 ^ d : ℝ) * (1 / (L₀ : ℝ))) ^ ((2 : ℝ) / d)
      * (1 + 1 / (L₀ : ℝ)) ^ 2 < 1 + ε / 2 := by
  have hlim : Tendsto (fun L : ℕ => (1 + (d * 2 ^ d : ℝ) * (1 / (L : ℝ))) ^ ((2 : ℝ) / d)
      * (1 + 1 / (L : ℝ)) ^ 2) atTop (𝓝 1) := by
    have h0 := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h1 : Tendsto (fun L : ℕ => (1 + (d * 2 ^ d : ℝ) * (1 / (L : ℝ))) ^ ((2 : ℝ) / d))
        atTop (𝓝 ((1 + (d * 2 ^ d : ℝ) * 0) ^ ((2 : ℝ) / d))) :=
      ((tendsto_const_nhds.add (h0.const_mul _))).rpow_const (Or.inl (by simp))
    have h2 : Tendsto (fun L : ℕ => (1 + 1 / (L : ℝ)) ^ 2) atTop (𝓝 ((1 + 0) ^ 2)) :=
      (tendsto_const_nhds.add h0).pow 2
    simpa using h1.mul h2
  obtain ⟨L₀, hL₀⟩ := ((hlim.eventually (gt_mem_nhds (by linarith : (1 : ℝ) < 1 + ε / 2))).and
    (eventually_ge_atTop 1)).exists
  exact ⟨L₀, hL₀.2, hL₀.1⟩

/-- The blow-up bound at every `n ≥ A L₀^d`, `A = n₀ (1 + d 2^d / L₀)`, written with
`p = n₀^{2/d}`. -/
theorem rate_le_of_scale_factor (hd : 1 ≤ d) {ε : ℝ} {L₀ : ℕ} (hL₀1 : 1 ≤ L₀)
    (hL₀ : (1 + (d * 2 ^ d : ℝ) * (1 / (L₀ : ℝ))) ^ ((2 : ℝ) / d)
      * (1 + 1 / (L₀ : ℝ)) ^ 2 < 1 + ε / 2)
    {n₀ : ℕ} (hn₀1 : 1 ≤ n₀) {V : Finset (Site d)} {h : Site d → ℝ}
    (hV : ∀ x ∉ V, h x = 0) (hVn : (fatten V).card ≤ n₀) (hm : 0 < sqMass h)
    (hsmall : 2 * d * (latEnergy h / sqMass h) < 1) {n : ℕ}
    (hn : (n₀ : ℝ) * (1 + (d * 2 ^ d : ℝ) * (1 / (L₀ : ℝ))) * (L₀ : ℝ) ^ d ≤ n) :
    (n : ℝ) ^ ((2 : ℝ) / d) * dirichletRate d n
      ≤ (n₀ : ℝ) ^ ((2 : ℝ) / d) * (1 + ε / 2) * (latEnergy h / sqMass h)
        / (1 - 2 * d * (latEnergy h / sqMass h)) := by
  set K' : ℝ := d * 2 ^ d with hK'
  set r := latEnergy h / sqMass h with hr
  have hr0 : 0 ≤ r := div_nonneg (latEnergy_nonneg h) hm.le
  have hn₀r : (0 : ℝ) < n₀ := by exact_mod_cast hn₀1
  have hL₀r : (1 : ℝ) ≤ L₀ := by exact_mod_cast hL₀1
  set A : ℝ := n₀ * (1 + K' * (1 / (L₀ : ℝ))) with hA
  have hA0 : 0 < A := by positivity
  have hAn : A ≤ n := le_trans (le_mul_of_one_le_right hA0.le (one_le_pow₀ hL₀r)) hn
  obtain ⟨L, hL1, hlo, hhi⟩ := exists_scale hd hA0 hAn
  have hLL₀ : L₀ ≤ L := by
    by_contra hlt
    push Not at hlt
    have h1 : ((L : ℝ) + 1) ^ d ≤ (L₀ : ℝ) ^ d := by
      gcongr
      exact_mod_cast hlt
    have h2 : A * ((L : ℝ) + 1) ^ d ≤ A * (L₀ : ℝ) ^ d := mul_le_mul_of_nonneg_left h1 hA0.le
    linarith
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hLL₀r : (L₀ : ℝ) ≤ L := by exact_mod_cast hLL₀
  have hscale : (L : ℝ) ^ d * n₀ * (1 + d * 2 ^ d / L) ≤ n := by
    refine le_trans ?_ hlo
    have h1 : (d : ℝ) * 2 ^ d / L ≤ K' * (1 / (L₀ : ℝ)) := by
      rw [hK', mul_one_div]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hLL₀r
    have hLd : (0 : ℝ) ≤ (L : ℝ) ^ d * n₀ := by positivity
    calc (L : ℝ) ^ d * n₀ * (1 + d * 2 ^ d / L) ≤ (L : ℝ) ^ d * n₀ * (1 + K' * (1 / (L₀ : ℝ))) :=
          mul_le_mul_of_nonneg_left (by linarith) hLd
      _ = A * (L : ℝ) ^ d := by rw [hA]; ring
  have hrate := dirichletRate_le_of_scale hd hV hVn hm hsmall hL1 hscale
  rw [← hr] at hrate
  have hgap : 0 < 1 - 2 * d * r := by linarith
  have hnpow : (n : ℝ) ^ ((2 : ℝ) / d) ≤ A ^ ((2 : ℝ) / d) * ((L : ℝ) + 1) ^ 2 := by
    rw [← rpow_two_div_scale hd hA0.le (by positivity)]
    exact Real.rpow_le_rpow (by positivity) hhi.le (by positivity)
  have hApow : A ^ ((2 : ℝ) / d)
      = (n₀ : ℝ) ^ ((2 : ℝ) / d) * (1 + K' * (1 / (L₀ : ℝ))) ^ ((2 : ℝ) / d) := by
    rw [hA, Real.mul_rpow hn₀r.le (by positivity)]
  have hfac : (1 + K' * (1 / (L₀ : ℝ))) ^ ((2 : ℝ) / d) * ((L : ℝ) + 1) ^ 2
      ≤ (1 + ε / 2) * (L : ℝ) ^ 2 := by
    have h1 : ((L : ℝ) + 1) ^ 2 ≤ (1 + 1 / (L₀ : ℝ)) ^ 2 * (L : ℝ) ^ 2 := by
      rw [← mul_pow]
      gcongr
      rw [add_mul, one_mul, one_div, inv_mul_eq_div]
      have : (1 : ℝ) ≤ (L : ℝ) / L₀ := by rw [le_div_iff₀ (by linarith)]; linarith
      linarith
    have hpos : (0 : ℝ) ≤ (1 + K' * (1 / (L₀ : ℝ))) ^ ((2 : ℝ) / d) := by positivity
    calc (1 + K' * (1 / (L₀ : ℝ))) ^ ((2 : ℝ) / d) * ((L : ℝ) + 1) ^ 2
        ≤ (1 + K' * (1 / (L₀ : ℝ))) ^ ((2 : ℝ) / d) * ((1 + 1 / (L₀ : ℝ)) ^ 2 * (L : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hpos
      _ = ((1 + K' * (1 / (L₀ : ℝ))) ^ ((2 : ℝ) / d) * (1 + 1 / (L₀ : ℝ)) ^ 2) * (L : ℝ) ^ 2 := by
          ring
      _ ≤ (1 + ε / 2) * (L : ℝ) ^ 2 := by
          gcongr
  have hρ0 := dirichletRate_nonneg d n
  calc (n : ℝ) ^ ((2 : ℝ) / d) * dirichletRate d n
      ≤ (A ^ ((2 : ℝ) / d) * ((L : ℝ) + 1) ^ 2) * (r / ((L : ℝ) ^ 2 * (1 - 2 * d * r))) :=
        mul_le_mul hnpow hrate hρ0 (by positivity)
    _ = (n₀ : ℝ) ^ ((2 : ℝ) / d) * ((1 + K' * (1 / (L₀ : ℝ))) ^ ((2 : ℝ) / d)
          * ((L : ℝ) + 1) ^ 2) * r / ((L : ℝ) ^ 2 * (1 - 2 * d * r)) := by
        rw [hApow]; ring
    _ ≤ (n₀ : ℝ) ^ ((2 : ℝ) / d) * ((1 + ε / 2) * (L : ℝ) ^ 2) * r
          / ((L : ℝ) ^ 2 * (1 - 2 * d * r)) := by
        gcongr
    _ = ((n₀ : ℝ) ^ ((2 : ℝ) / d) * (1 + ε / 2) * r) * (L : ℝ) ^ 2
          / ((1 - 2 * d * r) * (L : ℝ) ^ 2) := by ring
    _ = (n₀ : ℝ) ^ ((2 : ℝ) / d) * (1 + ε / 2) * r / (1 - 2 * d * r) :=
        mul_div_mul_right _ _ (by positivity)

/-- **The rate is eventually at most `(1 + ε)` times any late value, plus `ε`.** -/
theorem dirichletRate_eventually_le (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N₁ : ℕ, ∀ n₀ ≥ N₁, ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ ((2 : ℝ) / d) * dirichletRate d n
        ≤ (1 + ε) * ((n₀ : ℝ) ^ ((2 : ℝ) / d) * dirichletRate d n₀) + ε := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨L₀, hL₀1, hL₀⟩ := exists_scale_factor_lt (d := d) hε
  obtain ⟨C, hC, hCb⟩ := exists_dirichletRate_le hd
  set rbar : ℝ := ε / (4 * d * (1 + ε)) with hrbar
  have hrbar0 : 0 < rbar := by positivity
  have hneg : Tendsto (fun n : ℕ => (n : ℝ) ^ (-((2 : ℝ) / d))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp ((hneg.eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < rbar / (C + ε)))).and (eventually_ge_atTop (2 ^ d)))
  refine ⟨N₁, fun n₀ hn₀ => ?_⟩
  obtain ⟨hsmallpow, hn₀2⟩ := hN₁ n₀ hn₀
  have hn₀1 : 1 ≤ n₀ := le_trans Nat.one_le_two_pow hn₀2
  have hn₀r : (0 : ℝ) < n₀ := by exact_mod_cast hn₀1
  set p : ℝ := (n₀ : ℝ) ^ ((2 : ℝ) / d) with hp
  set q : ℝ := (n₀ : ℝ) ^ (-((2 : ℝ) / d)) with hq
  have hpq : p * q = 1 := by
    rw [hp, hq, ← Real.rpow_add hn₀r]
    simp
  have hp0 : 0 < p := by positivity
  have hq0 : 0 < q := by positivity
  have hΛ : dirichletRate d n₀ ≤ C * q := by
    have := hCb n₀ hn₀1
    rw [← hp] at this
    calc dirichletRate d n₀ = q * (p * dirichletRate d n₀) := by
          rw [← mul_assoc, mul_comm q p, hpq, one_mul]
      _ ≤ q * C := by gcongr
      _ = C * q := by ring
  obtain ⟨V, h, hVn, hV, hm, hrlt⟩ :=
    exists_lt_of_dirichletRate_lt hn₀2 (lt_add_of_pos_right (dirichletRate d n₀)
      (by positivity : (0 : ℝ) < ε / 2 * q))
  set r := latEnergy h / sqMass h with hr
  have hr0 : 0 ≤ r := div_nonneg (latEnergy_nonneg h) hm.le
  have hrsmall : r ≤ rbar := by
    have h1 : (C + ε) * q < rbar := by
      rw [lt_div_iff₀ (by positivity)] at hsmallpow
      linarith
    have h2 : r ≤ C * q + ε / 2 * q := by linarith
    nlinarith
  have h2dr : 2 * d * r ≤ ε / (2 * (1 + ε)) := by
    have h1 : 2 * d * rbar = ε / (2 * (1 + ε)) := by rw [hrbar]; field_simp; ring
    have h2 : 2 * d * r ≤ 2 * d * rbar := by gcongr
    linarith
  have hsmall : 2 * d * r < 1 := by
    have : ε / (2 * (1 + ε)) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    linarith
  have hgap : 0 < 1 - 2 * d * r := by linarith
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_ge_atTop ((n₀ : ℝ) * (1 + (d * 2 ^ d : ℝ) * (1 / (L₀ : ℝ))) * (L₀ : ℝ) ^ d))]
    with n hn
  have hfn := rate_le_of_scale_factor hd hL₀1 hL₀ hn₀1 hV hVn hm hsmall hn
  rw [← hr, ← hp] at hfn
  have hfac2 : (1 + ε / 2) / (1 - 2 * d * r) ≤ 1 + ε := by
    rw [div_le_iff₀ hgap]
    have : (1 + ε) * (2 * d * r) ≤ ε / 2 := by
      calc (1 + ε) * (2 * d * r) ≤ (1 + ε) * (ε / (2 * (1 + ε))) := by gcongr
        _ = ε / 2 := by field_simp
    have hexp : (1 + ε) * (1 - 2 * d * r) = (1 + ε) - (1 + ε) * (2 * d * r) := by ring
    linarith
  have hpr : p * r ≤ p * dirichletRate d n₀ + ε / 2 := by
    calc p * r ≤ p * (dirichletRate d n₀ + ε / 2 * q) := by gcongr
      _ = p * dirichletRate d n₀ + ε / 2 * (p * q) := by ring
      _ = p * dirichletRate d n₀ + ε / 2 := by rw [hpq, mul_one]
  have hpr0 : 0 ≤ p * r := by positivity
  have hΛ0 : 0 ≤ p * dirichletRate d n₀ := mul_nonneg hp0.le (dirichletRate_nonneg d n₀)
  calc (n : ℝ) ^ ((2 : ℝ) / d) * dirichletRate d n ≤ p * (1 + ε / 2) * r / (1 - 2 * d * r) := hfn
    _ = (p * r) * ((1 + ε / 2) / (1 - 2 * d * r)) := by ring
    _ ≤ (p * r) * (1 + ε) := mul_le_mul_of_nonneg_left hfac2 hpr0
    _ ≤ (p * dirichletRate d n₀ + ε / 2) * (1 + ε) := by gcongr
    _ = (1 + ε) * (p * dirichletRate d n₀) + (ε / 2 + ε * ε / 2) := by ring
    _ ≤ (1 + ε) * (p * dirichletRate d n₀) + ε := by nlinarith

/-- A bounded nonnegative sequence which is eventually at most `(1 + ε)` times any late value,
plus `ε`, converges. -/
theorem exists_tendsto_of_eventually_le {f : ℕ → ℝ} {C : ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hfC : ∀ n, f n ≤ C)
    (hP : ∀ ε > 0, ε ≤ 1 → ∃ N₁ : ℕ, ∀ n₀ ≥ N₁, ∀ᶠ n in atTop, f n ≤ (1 + ε) * f n₀ + ε) :
    ∃ c, 0 ≤ c ∧ Tendsto f atTop (𝓝 c) := by
  set c := liminf f atTop
  have hb : IsBoundedUnder (· ≥ ·) atTop f := isBoundedUnder_of ⟨0, fun n => hf0 n⟩
  have hb' : IsBoundedUnder (· ≤ ·) atTop f := isBoundedUnder_of ⟨C, hfC⟩
  have hcob : IsCoboundedUnder (· ≥ ·) atTop f := hb'.isCoboundedUnder_ge
  have hc0 : 0 ≤ c := le_liminf_of_le hcob (Eventually.of_forall hf0)
  refine ⟨c, hc0, tendsto_order.2 ⟨fun a ha => eventually_lt_of_lt_liminf ha hb, fun a ha => ?_⟩⟩
  set δ := a - c
  have hδ : 0 < δ := sub_pos.mpr ha
  set ε := min 1 (δ / (2 * (c + 3)))
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεδ : ε ≤ δ / (2 * (c + 3)) := min_le_right _ _
  obtain ⟨N₁, hN₁⟩ := hP ε hε hε1
  have hfreq : ∃ᶠ n in atTop, f n < c + ε := frequently_lt_of_liminf_lt hcob (by linarith)
  obtain ⟨n₀, hn₀, hn₀N⟩ := (hfreq.and_eventually (eventually_ge_atTop N₁)).exists
  filter_upwards [hN₁ n₀ hn₀N] with n hn
  have hkey : (1 + ε) * (c + ε) + ε < a := by
    have h1 : ε * (c + 3) ≤ δ / 2 := by
      calc ε * (c + 3) ≤ δ / (2 * (c + 3)) * (c + 3) := by gcongr
        _ = δ / 2 := by field_simp
    nlinarith
  calc f n ≤ (1 + ε) * f n₀ + ε := hn
    _ ≤ (1 + ε) * (c + ε) + ε := by gcongr
    _ < a := hkey

/-- **The Faber-Krahn constant**: `n^{2/d} dirichletRate d n` converges. -/
theorem exists_tendsto_dirichletRate (hd : 1 ≤ d) :
    ∃ c : ℝ, 0 ≤ c ∧ Tendsto (fun n : ℕ => (n : ℝ) ^ ((2 : ℝ) / d) * dirichletRate d n)
      atTop (𝓝 c) := by
  obtain ⟨C, hC, hCb⟩ := exists_dirichletRate_le hd
  refine exists_tendsto_of_eventually_le (C := C)
    (fun n => mul_nonneg (by positivity) (dirichletRate_nonneg d n)) (fun n => ?_)
    fun ε hε hε1 => dirichletRate_eventually_le hd hε hε1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hd0 : (2 : ℝ) / d ≠ 0 := by
      have : (0 : ℝ) < d := by exact_mod_cast hd
      positivity
    simp [Real.zero_rpow hd0, hC.le]
  · exact hCb n hn

end Parking

end
