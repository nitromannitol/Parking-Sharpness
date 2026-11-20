import Parking.Basic

/-!
# Dirichlet energies of finitely supported lattice functions

The quadratic forms behind the Donsker-Varadhan estimate for the range of the simple random
walk.  For a function `g` on `ℤ^d` vanishing off a finite set,

- `sqMass g = ∑_x g(x)^2`,
- `dirEnergy i g = ∑_x (g(x + e_i) - g(x))^2`, the energy in the direction `e_i`,
- `latEnergy g = (2d)^{-1} ∑_i dirEnergy i g`, the Dirichlet form of the walk operator:
  `latEnergy g = ∑_x g(x)^2 - ∑_x g(x) (P g)(x)` (`latEnergy_eq_sqMass_sub`),

and `dirichletRate d n` is the least ratio `latEnergy g / sqMass g` over the nonzero functions
supported on at most `n` sites, the Dirichlet eigenvalue of the best set of `n` sites.  The
energies decrease under every `1`-Lipschitz map fixing `0` applied pointwise, in particular
under `|·|` and under the truncations `(· - s)⁺`, and they are invariant under translations.
-/

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- `g` vanishes off a finite set. -/
def FinSupp (g : Site d → ℝ) : Prop :=
  ∃ V : Finset (Site d), ∀ x ∉ V, g x = 0

/-- `∑_x g(x)^2`. -/
def sqMass (g : Site d → ℝ) : ℝ :=
  ∑' x, g x ^ 2

/-- `∑_x (g(x + e_i) - g(x))^2`, the energy of `g` in the direction `e_i`. -/
def dirEnergy (i : Fin d) (g : Site d → ℝ) : ℝ :=
  ∑' x, (g (x + unit i) - g x) ^ 2

/-- The Dirichlet form `(2d)^{-1} ∑_i ∑_x (g(x + e_i) - g(x))^2` of the walk operator. -/
def latEnergy (g : Site d → ℝ) : ℝ :=
  (∑ i, dirEnergy i g) / (2 * d)

/-- The least Dirichlet ratio `latEnergy g / sqMass g` over the nonzero functions supported on
at most `n` sites. -/
def dirichletRate (d n : ℕ) : ℝ :=
  sInf {q : ℝ | ∃ (V : Finset (Site d)) (g : Site d → ℝ), V.card ≤ n ∧ (∀ x ∉ V, g x = 0) ∧
    0 < sqMass g ∧ q = latEnergy g / sqMass g}

/-! ### Finite support -/

theorem FinSupp.comp_add {g : Site d → ℝ} (hg : FinSupp g) (a : Site d) :
    FinSupp fun x => g (x + a) := by
  obtain ⟨V, hV⟩ := hg
  refine ⟨V.image fun y => y - a, fun x hx => hV _ fun h => hx ?_⟩
  exact Finset.mem_image.mpr ⟨x + a, h, by abel⟩

theorem FinSupp.comp_lip {g : Site d → ℝ} (hg : FinSupp g) {φ : ℝ → ℝ} (hφ : φ 0 = 0) :
    FinSupp fun x => φ (g x) := by
  obtain ⟨V, hV⟩ := hg
  exact ⟨V, fun x hx => by show φ (g x) = 0; rw [hV x hx, hφ]⟩

theorem FinSupp.summable_sq {g : Site d → ℝ} (hg : FinSupp g) :
    Summable fun x => g x ^ 2 := by
  obtain ⟨V, hV⟩ := hg
  exact summable_of_ne_finset_zero (s := V) fun x hx => by rw [hV x hx]; ring

theorem FinSupp.summable_mul {g h : Site d → ℝ} (hg : FinSupp g) :
    Summable fun x => g x * h x := by
  obtain ⟨V, hV⟩ := hg
  exact summable_of_ne_finset_zero (s := V) fun x hx => by rw [hV x hx]; ring

theorem FinSupp.summable_dir {g : Site d → ℝ} (hg : FinSupp g) (i : Fin d) :
    Summable fun x => (g (x + unit i) - g x) ^ 2 := by
  obtain ⟨W, hW⟩ := hg.comp_add (unit i)
  obtain ⟨V, hV⟩ := hg
  refine summable_of_ne_finset_zero (s := V ∪ W) fun x hx => ?_
  rw [Finset.mem_union, not_or] at hx
  have h1 : g (x + unit i) = 0 := hW x hx.2
  rw [hV x hx.1, h1]
  ring

/-! ### Nonnegativity -/

theorem sqMass_nonneg (g : Site d → ℝ) : 0 ≤ sqMass g :=
  tsum_nonneg fun _ => sq_nonneg _

theorem dirEnergy_nonneg (i : Fin d) (g : Site d → ℝ) : 0 ≤ dirEnergy i g :=
  tsum_nonneg fun _ => sq_nonneg _

theorem latEnergy_nonneg (g : Site d → ℝ) : 0 ≤ latEnergy g :=
  div_nonneg (Finset.sum_nonneg fun i _ => dirEnergy_nonneg i g) (by positivity)

theorem sqMass_eq_sum {g : Site d → ℝ} {V : Finset (Site d)} (hV : ∀ x ∉ V, g x = 0) :
    sqMass g = ∑ x ∈ V, g x ^ 2 :=
  tsum_eq_sum fun x hx => by rw [hV x hx]; ring

/-! ### Pointwise contractions -/

/-- A pointwise `1`-Lipschitz map fixing `0` lowers the directional energies. -/
theorem dirEnergy_comp_le {g : Site d → ℝ} (hg : FinSupp g) {φ : ℝ → ℝ} (hφ0 : φ 0 = 0)
    (hφ : ∀ a b, |φ a - φ b| ≤ |a - b|) (i : Fin d) :
    dirEnergy i (fun x => φ (g x)) ≤ dirEnergy i g := by
  refine Summable.tsum_le_tsum (fun x => ?_) ((hg.comp_lip hφ0).summable_dir i)
    (hg.summable_dir i)
  have h := hφ (g (x + unit i)) (g x)
  calc (φ (g (x + unit i)) - φ (g x)) ^ 2 = |φ (g (x + unit i)) - φ (g x)| ^ 2 := (sq_abs _).symm
    _ ≤ |g (x + unit i) - g x| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = (g (x + unit i) - g x) ^ 2 := sq_abs _

theorem latEnergy_comp_le {g : Site d → ℝ} (hg : FinSupp g) {φ : ℝ → ℝ} (hφ0 : φ 0 = 0)
    (hφ : ∀ a b, |φ a - φ b| ≤ |a - b|) :
    latEnergy (fun x => φ (g x)) ≤ latEnergy g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => dirEnergy_comp_le hg hφ0 hφ i)
    (by positivity)

theorem abs_posPart_sub_le (s a b : ℝ) : |max (a - s) 0 - max (b - s) 0| ≤ |a - b| := by
  rcases le_total (a - s) 0 with ha | ha <;> rcases le_total (b - s) 0 with hb | hb
  · simp [max_eq_right ha, max_eq_right hb]
  · rw [max_eq_right ha, max_eq_left hb, abs_le]
    constructor <;> cases abs_cases (a - b) <;> linarith
  · rw [max_eq_left ha, max_eq_right hb, abs_le]
    constructor <;> cases abs_cases (a - b) <;> linarith
  · rw [max_eq_left ha, max_eq_left hb]
    exact le_of_eq (by ring_nf)

theorem latEnergy_abs_le {g : Site d → ℝ} (hg : FinSupp g) :
    latEnergy (fun x => |g x|) ≤ latEnergy g :=
  latEnergy_comp_le (φ := fun a => |a|) hg abs_zero fun a b => abs_abs_sub_abs_le a b

theorem latEnergy_posPart_le {g : Site d → ℝ} (hg : FinSupp g) {s : ℝ} (hs : 0 ≤ s) :
    latEnergy (fun x => max (g x - s) 0) ≤ latEnergy g :=
  latEnergy_comp_le (φ := fun a => max (a - s) 0) hg
    (by show max (0 - s) 0 = 0; exact max_eq_right (by linarith)) (abs_posPart_sub_le s)

/-! ### Translation invariance -/

theorem sqMass_comp_add (g : Site d → ℝ) (a : Site d) :
    sqMass (fun x => g (x + a)) = sqMass g :=
  (Equiv.addRight a).tsum_eq fun x => g x ^ 2

theorem dirEnergy_comp_add (i : Fin d) (g : Site d → ℝ) (a : Site d) :
    dirEnergy i (fun x => g (x + a)) = dirEnergy i g := by
  unfold dirEnergy
  have h : ∀ x : Site d, (g (x + unit i + a) - g (x + a)) ^ 2
      = (fun y => (g (y + unit i) - g y) ^ 2) (Equiv.addRight a x) := by
    intro x
    simp only [Equiv.coe_addRight]
    rw [add_right_comm]
  simp_rw [h]
  exact (Equiv.addRight a).tsum_eq fun y => (g (y + unit i) - g y) ^ 2

theorem latEnergy_comp_add (g : Site d → ℝ) (a : Site d) :
    latEnergy (fun x => g (x + a)) = latEnergy g := by
  simp only [latEnergy, dirEnergy_comp_add]

/-! ### The Dirichlet form of the walk operator -/

/-- `∑_x g(x) g(x + e_i) = ∑_x g(x - e_i) g(x)`, by translation. -/
theorem tsum_mul_comp_add_unit (g : Site d → ℝ) (i : Fin d) :
    ∑' x, g x * g (x - unit i) = ∑' x, g (x + unit i) * g x := by
  have h := (Equiv.addRight (unit i)).tsum_eq fun x => g x * g (x - unit i)
  simp only [Equiv.coe_addRight, add_sub_cancel_right] at h
  exact h.symm

/-- The directional energy expands as `2 ∑ g^2 - 2 ∑_x g(x) g(x + e_i)`. -/
theorem dirEnergy_eq {g : Site d → ℝ} (hg : FinSupp g) (i : Fin d) :
    dirEnergy i g = 2 * sqMass g - 2 * ∑' x, g x * g (x + unit i) := by
  have hs1 : Summable fun x => g (x + unit i) ^ 2 := (hg.comp_add (unit i)).summable_sq
  have hs2 : Summable fun x => g x ^ 2 := hg.summable_sq
  have hs3 : Summable fun x => g x * g (x + unit i) := hg.summable_mul
  have hshift : ∑' x, g (x + unit i) ^ 2 = sqMass g := sqMass_comp_add g (unit i)
  unfold dirEnergy
  have hexp : ∀ x, (g (x + unit i) - g x) ^ 2
      = g (x + unit i) ^ 2 + g x ^ 2 - 2 * (g x * g (x + unit i)) := fun x => by ring
  simp_rw [hexp]
  rw [Summable.tsum_sub (hs1.add hs2) (hs3.mul_left 2), Summable.tsum_add hs1 hs2,
    Summable.tsum_mul_left 2 hs3, hshift]
  unfold sqMass
  ring

/-- **The Dirichlet form identity**: `latEnergy g = ∑ g^2 - ∑ g (P g)`. -/
theorem latEnergy_eq_sqMass_sub (hd : 1 ≤ d) {g : Site d → ℝ} (hg : FinSupp g) :
    latEnergy g = sqMass g - ∑' x, g x * walkOp g x := by
  have hd0 : (0 : ℝ) < 2 * d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsplit : ∀ x, g x * walkOp g x
      = (∑ i : Fin d, (g x * g (x + unit i) + g x * g (x - unit i))) / (2 * d) := by
    intro x
    rw [walkOp, nbrSum, mul_div_assoc', Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsum : ∀ i : Fin d, Summable fun x => g x * g (x + unit i) + g x * g (x - unit i) :=
    fun i => hg.summable_mul.add hg.summable_mul
  have htot : ∑' x, g x * walkOp g x
      = (∑ i : Fin d, 2 * ∑' x, g x * g (x + unit i)) / (2 * d) := by
    simp_rw [hsplit]
    rw [tsum_div_const, Summable.tsum_finsetSum fun i _ => hsum i]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Summable.tsum_add hg.summable_mul hg.summable_mul, tsum_mul_comp_add_unit g i]
    have hcomm : ∑' x, g (x + unit i) * g x = ∑' x, g x * g (x + unit i) :=
      tsum_congr fun x => mul_comm _ _
    rw [hcomm]
    ring
  rw [htot, latEnergy]
  simp_rw [dirEnergy_eq hg]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

/-! ### The least Dirichlet ratio -/

theorem dirichletRate_set_bddBelow (d n : ℕ) :
    BddBelow {q : ℝ | ∃ (V : Finset (Site d)) (g : Site d → ℝ), V.card ≤ n ∧
      (∀ x ∉ V, g x = 0) ∧ 0 < sqMass g ∧ q = latEnergy g / sqMass g} := by
  refine ⟨0, ?_⟩
  rintro q ⟨V, g, -, -, hm, rfl⟩
  exact div_nonneg (latEnergy_nonneg g) hm.le

theorem dirichletRate_nonneg (d n : ℕ) : 0 ≤ dirichletRate d n := by
  unfold dirichletRate
  by_cases hne : {q : ℝ | ∃ (V : Finset (Site d)) (g : Site d → ℝ), V.card ≤ n ∧
      (∀ x ∉ V, g x = 0) ∧ 0 < sqMass g ∧ q = latEnergy g / sqMass g}.Nonempty
  · refine le_csInf hne ?_
    rintro q ⟨V, g, -, -, hm, rfl⟩
    exact div_nonneg (latEnergy_nonneg g) hm.le
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sInf_empty]

/-- Every admissible function bounds the rate from above. -/
theorem dirichletRate_le {n : ℕ} {V : Finset (Site d)} {g : Site d → ℝ} (hVn : V.card ≤ n)
    (hV : ∀ x ∉ V, g x = 0) (hm : 0 < sqMass g) :
    dirichletRate d n ≤ latEnergy g / sqMass g :=
  csInf_le (dirichletRate_set_bddBelow d n) ⟨V, g, hVn, hV, hm, rfl⟩

/-- Above the rate there is an admissible function, once `n ≥ 1`. -/
theorem exists_lt_of_dirichletRate_lt {n : ℕ} (hn : 1 ≤ n) {q : ℝ}
    (hq : dirichletRate d n < q) :
    ∃ (V : Finset (Site d)) (g : Site d → ℝ), V.card ≤ n ∧ (∀ x ∉ V, g x = 0) ∧
      0 < sqMass g ∧ latEnergy g / sqMass g < q := by
  classical
  have hne : {q : ℝ | ∃ (V : Finset (Site d)) (g : Site d → ℝ), V.card ≤ n ∧
      (∀ x ∉ V, g x = 0) ∧ 0 < sqMass g ∧ q = latEnergy g / sqMass g}.Nonempty := by
    let g : Site d → ℝ := fun x => if x = 0 then 1 else 0
    refine ⟨_, {0}, g, by simpa using hn, fun x hx => ?_, ?_, rfl⟩
    · simp only [Finset.mem_singleton] at hx
      simp [g, hx]
    · rw [sqMass_eq_sum (V := {0}) fun x hx => by
        simp only [Finset.mem_singleton] at hx
        simp [g, hx]]
      simp [g]
  obtain ⟨q', ⟨V, g, hVn, hV, hm, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne hq
  exact ⟨V, g, hVn, hV, hm, hlt⟩

/-- The rate is antitone in the number of sites. -/
theorem dirichletRate_anti {m n : ℕ} (hmn : m ≤ n) (hm : 1 ≤ m) :
    dirichletRate d n ≤ dirichletRate d m := by
  refine le_of_forall_gt_imp_ge_of_dense fun q hq => ?_
  obtain ⟨V, g, hVm, hV, hpos, hlt⟩ := exists_lt_of_dirichletRate_lt hm hq
  exact (dirichletRate_le (hVm.trans hmn) hV hpos).trans hlt.le

end Parking

end
