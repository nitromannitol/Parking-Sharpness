import Parking.Support.DVEnergy
import Parking.Support.RangeFixedSet
import Parking.Support.TailRangeBounds

/-!
# Confinement probabilities from Dirichlet ratios

A nonnegative function `g` vanishing off a finite set `V`, of Dirichlet ratio
`μ = latEnergy g / sqMass g < 1`, forces the walk started at a suitable point of `V` to stay in
`V` for `n` steps with probability at least `(1 - μ)^n / √|V|`
(`exists_survival_ge`), and hence (`rangeExp_ge_of_ratio`)

  `E_0 e^{-a|R_t|} ≥ e^{-a|V|} (1 - μ)^{t+1} / √|V|`.

The proof is spectral but needs no spectral theorem.  Let `Q` be the walk operator killed off
`V`; it is symmetric.  The sequence `b_k = ‖Q^k g‖²` is log-convex by Cauchy-Schwarz, since
`b_k = ⟨Q^{k-1} g, Q^{k+1} g⟩`, so `b_k ≥ b_0 (b_1 / b_0)^k`, and
`b_1 ≥ ⟨g, Q g⟩² / ‖g‖² = (1 - μ)² ‖g‖²`.  On the other hand
`b_k = ⟨g, Q^{2k} g⟩ ≤ max g · ∑ g · max_x P_x(stay in V for 2k steps)` and
`max g · ∑ g ≤ √|V| ‖g‖²`.  The walk from the best point `x*` is the walk from the origin
confined to `V - x*`.
-/

noncomputable section

namespace Parking

open LatticeProb MeasureTheory

variable {d : ℕ}

/-! ### The walk operator is symmetric -/

theorem FinSupp.summable_mul_right {g h : Site d → ℝ} (hh : FinSupp h) :
    Summable fun x => g x * h x := by
  simpa [mul_comm] using hh.summable_mul (h := g)

theorem tsum_mul_walkOp_comm (hd : 1 ≤ d) {f g : Site d → ℝ} (hf : FinSupp f)
    (hg : FinSupp g) :
    ∑' x, f x * walkOp g x = ∑' x, walkOp f x * g x := by
  have hd0 : (2 * d : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have hL : ∀ x, f x * walkOp g x
      = (∑ i : Fin d, (f x * g (x + unit i) + f x * g (x - unit i))) / (2 * d) := by
    intro x
    rw [walkOp, nbrSum, mul_div_assoc', Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hR : ∀ x, walkOp f x * g x
      = (∑ i : Fin d, (f (x + unit i) * g x + f (x - unit i) * g x)) / (2 * d) := by
    intro x
    rw [walkOp, nbrSum, div_mul_eq_mul_div, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hL, hR]
  rw [tsum_div_const, tsum_div_const,
    Summable.tsum_finsetSum fun i _ => hf.summable_mul.add hf.summable_mul,
    Summable.tsum_finsetSum fun i _ => hg.summable_mul_right.add hg.summable_mul_right]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Summable.tsum_add hf.summable_mul hf.summable_mul,
    Summable.tsum_add hg.summable_mul_right hg.summable_mul_right]
  have h1 : ∑' x, f x * g (x + unit i) = ∑' x, f (x - unit i) * g x := by
    have := (Equiv.addRight (unit i)).tsum_eq fun x => f (x - unit i) * g x
    simp only [Equiv.coe_addRight, add_sub_cancel_right] at this
    exact this
  have h2 : ∑' x, f x * g (x - unit i) = ∑' x, f (x + unit i) * g x := by
    have := (Equiv.subRight (unit i)).tsum_eq fun x => f (x + unit i) * g x
    simp only [Equiv.subRight_apply, sub_add_cancel] at this
    exact this
  rw [h1, h2, add_comm]

/-! ### The walk killed off a finite set -/

/-- The walk operator killed off `V`. -/
def killOp (V : Finset (Site d)) (f : Site d → ℝ) (x : Site d) : ℝ :=
  if x ∈ V then walkOp f x else 0

theorem killOp_eq_zero {V : Finset (Site d)} (f : Site d → ℝ) {x : Site d} (hx : x ∉ V) :
    killOp V f x = 0 := by
  simp [killOp, hx]

theorem walkOp_mono' {f g : Site d → ℝ} (h : ∀ x, f x ≤ g x) (x : Site d) :
    walkOp f x ≤ walkOp g x := by
  unfold walkOp nbrSum
  have hd : (0 : ℝ) ≤ 2 * d := by positivity
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun i _ => add_le_add (h _) (h _)) hd

theorem walkOp_nonneg' {f : Site d → ℝ} (h : ∀ x, 0 ≤ f x) (x : Site d) : 0 ≤ walkOp f x := by
  have := walkOp_mono' (f := fun _ => (0 : ℝ)) (g := f) h x
  simpa [walkOp, nbrSum] using this

theorem killOp_mono (V : Finset (Site d)) {f g : Site d → ℝ} (h : ∀ x, f x ≤ g x)
    (x : Site d) : killOp V f x ≤ killOp V g x := by
  unfold killOp
  split_ifs
  · exact walkOp_mono' h x
  · exact le_rfl

theorem killOp_nonneg (V : Finset (Site d)) {f : Site d → ℝ} (h : ∀ x, 0 ≤ f x) (x : Site d) :
    0 ≤ killOp V f x := by
  unfold killOp
  split_ifs
  · exact walkOp_nonneg' h x
  · exact le_rfl

theorem killOp_smul (V : Finset (Site d)) (c : ℝ) (f : Site d → ℝ) (x : Site d) :
    killOp V (fun y => c * f y) x = c * killOp V f x := by
  unfold killOp walkOp nbrSum
  split_ifs
  · rw [mul_div_assoc', Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  · ring

theorem killOp_iterate_eq_zero (V : Finset (Site d)) (f : Site d → ℝ) (hf : ∀ x ∉ V, f x = 0)
    (k : ℕ) {x : Site d} (hx : x ∉ V) : (killOp V)^[k] f x = 0 := by
  cases k with
  | zero => exact hf x hx
  | succ k =>
      rw [Function.iterate_succ_apply']
      exact killOp_eq_zero _ hx

/-- `∑_{x ∈ V} f(x) (Q g)(x) = ∑_{x ∈ V} (Q f)(x) g(x)` for `f, g` vanishing off `V`. -/
theorem sum_mul_killOp_comm (hd : 1 ≤ d) (V : Finset (Site d)) {f g : Site d → ℝ}
    (hf : ∀ x ∉ V, f x = 0) (hg : ∀ x ∉ V, g x = 0) :
    ∑ x ∈ V, f x * killOp V g x = ∑ x ∈ V, killOp V f x * g x := by
  have h1 : ∑ x ∈ V, f x * killOp V g x = ∑' x, f x * walkOp g x := by
    rw [tsum_eq_sum (s := V) fun x hx => by rw [hf x hx, zero_mul]]
    exact Finset.sum_congr rfl fun x hx => by rw [killOp, ite_eq_left hx]
  have h2 : ∑ x ∈ V, killOp V f x * g x = ∑' x, walkOp f x * g x := by
    rw [tsum_eq_sum (s := V) fun x hx => by rw [hg x hx, mul_zero]]
    exact Finset.sum_congr rfl fun x hx => by rw [killOp, ite_eq_left hx]
  rw [h1, h2, tsum_mul_walkOp_comm hd ⟨V, hf⟩ ⟨V, hg⟩]

/-- `⟨Q^j f, Q^k g⟩ = ⟨f, Q^{j+k} g⟩`. -/
theorem sum_iterate_mul_iterate (hd : 1 ≤ d) (V : Finset (Site d)) {f g : Site d → ℝ}
    (hf : ∀ x ∉ V, f x = 0) (hg : ∀ x ∉ V, g x = 0) (j : ℕ) :
    ∀ k : ℕ, ∑ x ∈ V, (killOp V)^[j] f x * (killOp V)^[k] g x
      = ∑ x ∈ V, f x * (killOp V)^[j + k] g x := by
  induction j with
  | zero => intro k; simp
  | succ j ih =>
      intro k
      rw [Function.iterate_succ_apply', ← sum_mul_killOp_comm hd V
        (fun x hx => killOp_iterate_eq_zero V f hf j hx)
        (fun x hx => killOp_iterate_eq_zero V g hg k hx), ← Function.iterate_succ_apply'
        (killOp V) k g, ih (k + 1), show j + (k + 1) = j + 1 + k by omega]

/-- **Log-convexity**: `b_k = ‖Q^k g‖²` satisfies `b_{k+1}² ≤ b_k b_{k+2}`. -/
theorem sq_le_mul_iterate (hd : 1 ≤ d) (V : Finset (Site d)) {g : Site d → ℝ}
    (hg : ∀ x ∉ V, g x = 0) (k : ℕ) :
    (∑ x ∈ V, (killOp V)^[k + 1] g x ^ 2) ^ 2
      ≤ (∑ x ∈ V, (killOp V)^[k] g x ^ 2) * ∑ x ∈ V, (killOp V)^[k + 2] g x ^ 2 := by
  have hb : ∑ x ∈ V, (killOp V)^[k + 1] g x ^ 2
      = ∑ x ∈ V, (killOp V)^[k] g x * (killOp V)^[k + 2] g x := by
    have h1 := sum_iterate_mul_iterate hd V hg hg (k + 1) (k + 1)
    have h2 := sum_iterate_mul_iterate hd V hg hg k (k + 2)
    rw [show k + 1 + (k + 1) = k + (k + 2) by omega, ← h2] at h1
    simpa [sq] using h1
  rw [hb]
  exact Finset.sum_mul_sq_le_sq_mul_sq V _ _

/-- **Geometric lower bound**: `b_k ≥ b_0 (b_1/b_0)^k`. -/
theorem iterate_sq_ge (hd : 1 ≤ d) (V : Finset (Site d)) {g : Site d → ℝ}
    (hg : ∀ x ∉ V, g x = 0) (hb0 : 0 < ∑ x ∈ V, g x ^ 2) (k : ℕ) :
    (∑ x ∈ V, g x ^ 2) * ((∑ x ∈ V, (killOp V g x) ^ 2) / ∑ x ∈ V, g x ^ 2) ^ k
      ≤ ∑ x ∈ V, (killOp V)^[k] g x ^ 2 := by
  set b : ℕ → ℝ := fun k => ∑ x ∈ V, (killOp V)^[k] g x ^ 2 with hbdef
  have hb0' : b 0 = ∑ x ∈ V, g x ^ 2 := rfl
  have hb1 : b 1 = ∑ x ∈ V, (killOp V g x) ^ 2 := rfl
  have hbnn : ∀ k, 0 ≤ b k := fun k => Finset.sum_nonneg fun x _ => sq_nonneg _
  have hlc : ∀ k, b (k + 1) ^ 2 ≤ b k * b (k + 2) := sq_le_mul_iterate hd V hg
  -- the ratios increase
  have hratio : ∀ k, b 1 * b k ≤ b 0 * b (k + 1) := by
    intro k
    induction k with
    | zero => rw [mul_comm]
    | succ k ih =>
        by_cases hk : b k = 0
        · have hzero : ∀ x ∈ V, (killOp V)^[k] g x = 0 := by
            intro x hx
            have := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => sq_nonneg
              ((killOp V)^[k] g y)).mp hk x hx
            exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
          have hk1 : b (k + 1) = 0 := by
            refine Finset.sum_eq_zero fun x hx => ?_
            rw [Function.iterate_succ_apply']
            have : (killOp V)^[k] g = fun _ => 0 := by
              funext y
              by_cases hy : y ∈ V
              · exact hzero y hy
              · exact killOp_iterate_eq_zero V g hg k hy
            rw [this]
            simp [killOp, walkOp, nbrSum]
          rw [hk1, mul_zero]
          exact mul_nonneg (hbnn 0) (hbnn _)
        · have hkpos : 0 < b k := lt_of_le_of_ne (hbnn k) (Ne.symm hk)
          have h1 := hlc k
          have h2 : b 1 * b k * b (k + 1) ≤ b 0 * b (k + 1) * b (k + 1) :=
            mul_le_mul_of_nonneg_right ih (hbnn _)
          have h3 : b 1 * b (k + 1) * b k ≤ b 0 * b (k + 2) * b k := by
            nlinarith [hbnn 0]
          exact le_of_mul_le_mul_right h3 hkpos
  induction k with
  | zero => simp
  | succ k ih =>
      have h := hratio k
      have hq : (∑ x ∈ V, killOp V g x ^ 2) / ∑ x ∈ V, g x ^ 2 = b 1 / b 0 := rfl
      rw [pow_succ]
      calc (∑ x ∈ V, g x ^ 2) * (((∑ x ∈ V, killOp V g x ^ 2) / ∑ x ∈ V, g x ^ 2) ^ k
            * ((∑ x ∈ V, killOp V g x ^ 2) / ∑ x ∈ V, g x ^ 2))
          = ((∑ x ∈ V, g x ^ 2) * ((∑ x ∈ V, killOp V g x ^ 2) / ∑ x ∈ V, g x ^ 2) ^ k)
              * (b 1 / b 0) := by rw [hq]; ring
        _ ≤ b k * (b 1 / b 0) :=
            mul_le_mul_of_nonneg_right ih (div_nonneg (hbnn 1) (hbnn 0))
        _ ≤ b (k + 1) := by
            rw [mul_div_assoc', div_le_iff₀ (show 0 < b 0 from hb0), mul_comm (b k)]
            linarith

/-! ### Survival in a finite set -/

/-- `P_x(X_j ∈ V, j ≤ k+1) = 1_V(x) (P s_k)(x)`. -/
theorem survival_succ_eq (V : Finset (Site d)) (k : ℕ) (x : Site d) :
    Network.survival (lattice d) V (k + 1) x = killOp V (Network.survival (lattice d) V k) x := by
  rw [Network.survival_succ, killOp]
  split_ifs
  · rw [← Graph.Zd.walkOp_eq]
    rfl
  · rfl

theorem survival_eq_iterate (V : Finset (Site d)) (k : ℕ) :
    Network.survival (lattice d) V k = (killOp V)^[k] fun x => if x ∈ V then 1 else 0 := by
  induction k with
  | zero =>
      funext x
      rw [Network.survival_zero, Function.iterate_zero_apply]
      by_cases hx : x ∈ V <;> simp [hx]
  | succ k ih =>
      funext x
      rw [survival_succ_eq, ih, Function.iterate_succ_apply']

/-- A function between `0` and `G` on `V` is driven by `Q^k` below `G` times the survival. -/
theorem iterate_le_mul_survival (V : Finset (Site d)) {g : Site d → ℝ} {G : ℝ}
    (hg : ∀ x ∉ V, g x = 0) (hgG : ∀ x, g x ≤ G) (k : ℕ) (x : Site d) :
    (killOp V)^[k] g x ≤ G * Network.survival (lattice d) V k x := by
  induction k generalizing x with
  | zero =>
      rw [Network.survival_zero, Function.iterate_zero_apply]
      by_cases hx : x ∈ V
      · rw [ite_eq_left hx, mul_one]
        exact hgG x
      · rw [ite_eq_right hx, mul_zero, hg x hx]
  | succ k ih =>
      rw [Function.iterate_succ_apply', survival_succ_eq, ← killOp_smul]
      exact killOp_mono V (fun y => ih y) x

/-- Translating the set and the starting point together leaves the survival unchanged. -/
theorem survival_image_add (V : Finset (Site d)) (a : Site d) (k : ℕ) (x : Site d) :
    Network.survival (lattice d) (V.image (· + a)) k (x + a)
      = Network.survival (lattice d) V k x := by
  classical
  have hmem : ∀ y : Site d, y + a ∈ V.image (· + a) ↔ y ∈ V := by
    intro y
    simp
  induction k generalizing x with
  | zero =>
      rw [Network.survival_zero, Network.survival_zero]
      by_cases hx : x ∈ V
      · rw [ite_eq_left hx, ite_eq_left ((hmem x).mpr hx)]
      · rw [ite_eq_right hx, ite_eq_right fun h => hx ((hmem x).mp h)]
  | succ k ih =>
      rw [survival_succ_eq, survival_succ_eq, killOp, killOp]
      by_cases hx : x ∈ V
      · rw [ite_eq_left hx, ite_eq_left ((hmem x).mpr hx)]
        have hfun : Network.survival (lattice d) (V.image (· + a)) k
            = fun y => Network.survival (lattice d) V k (y - a) := by
          funext y
          rw [← ih (y - a), sub_add_cancel]
        rw [hfun]
        unfold walkOp nbrSum
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 2 <;> abel_nf
      · rw [ite_eq_right hx, ite_eq_right fun h => hx ((hmem x).mp h)]

/-- **Confinement from a Dirichlet ratio.**  For `g ≥ 0` vanishing off `V` with
`μ = latEnergy g / sqMass g < 1`, some point of `V` keeps the walk in `V` for `2k` steps with
probability at least `(1 - μ)^{2k} / √|V|`. -/
theorem exists_survival_ge (hd : 1 ≤ d) {V : Finset (Site d)} {g : Site d → ℝ}
    (hg : ∀ x ∉ V, g x = 0) (hg0 : ∀ x, 0 ≤ g x) (hm : 0 < sqMass g)
    (hμ : latEnergy g / sqMass g ≤ 1) (k : ℕ) :
    ∃ x ∈ V, (1 - latEnergy g / sqMass g) ^ (2 * k)
      ≤ Real.sqrt V.card * Network.survival (lattice d) V (2 * k) x := by
  classical
  set M := sqMass g with hM
  set μ := latEnergy g / sqMass g with hμdef
  have hMV : M = ∑ x ∈ V, g x ^ 2 := sqMass_eq_sum hg
  have hVne : V.Nonempty := by
    by_contra hV
    rw [Finset.not_nonempty_iff_eq_empty] at hV
    rw [hMV, hV, Finset.sum_empty] at hm
    exact lt_irrefl 0 hm
  obtain ⟨xs, hxsV, hxs⟩ := V.exists_max_image (Network.survival (lattice d) V (2 * k)) hVne
  obtain ⟨xg, hxgV, hxg⟩ := V.exists_max_image g hVne
  set G := g xg with hGdef
  have hG0 : 0 ≤ G := hg0 xg
  have hgG : ∀ x, g x ≤ G := by
    intro x
    by_cases hx : x ∈ V
    · exact hxg x hx
    · rw [hg x hx]; exact hG0
  refine ⟨xs, hxsV, ?_⟩
  set s := Network.survival (lattice d) V (2 * k) xs with hs
  have hs0 : 0 ≤ s := Network.survival_nonneg _ _ _
  -- `⟨g, Q g⟩ = (1 - μ) M`
  have hgQg : ∑ x ∈ V, g x * killOp V g x = (1 - μ) * M := by
    have h1 : ∑ x ∈ V, g x * killOp V g x = ∑' x, g x * walkOp g x := by
      rw [tsum_eq_sum (s := V) fun x hx => by rw [hg x hx, zero_mul]]
      exact Finset.sum_congr rfl fun x hx => by rw [killOp, ite_eq_left hx]
    rw [h1, hμdef, ← hM, sub_mul, one_mul, div_mul_cancel₀ _ hm.ne']
    have := latEnergy_eq_sqMass_sub hd ⟨V, hg⟩
    rw [← hM] at this
    linarith
  -- `b_1 ≥ (1 - μ)^2 M`
  have hb1 : (1 - μ) ^ 2 * M ≤ ∑ x ∈ V, killOp V g x ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq V g (killOp V g)
    rw [hgQg, ← hMV] at hcs
    have : ((1 - μ) * M) ^ 2 = (1 - μ) ^ 2 * M * M := by ring
    rw [this] at hcs
    exact le_of_mul_le_mul_right (by linarith) hm
  have hratio : (1 - μ) ^ 2 ≤ (∑ x ∈ V, killOp V g x ^ 2) / M := by
    rw [le_div_iff₀ hm]
    exact hb1
  have hbk := iterate_sq_ge hd V hg (by rw [← hMV]; exact hm) k
  rw [← hMV] at hbk
  have hlow : M * ((1 - μ) ^ 2) ^ k ≤ ∑ x ∈ V, (killOp V)^[k] g x ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg _) hratio k) hm.le) hbk
  -- `b_k = ⟨g, Q^{2k} g⟩ ≤ G s ∑ g`
  have hbk' : ∑ x ∈ V, (killOp V)^[k] g x ^ 2 = ∑ x ∈ V, g x * (killOp V)^[2 * k] g x := by
    have := sum_iterate_mul_iterate hd V hg hg k k
    rw [show k + k = 2 * k by ring] at this
    rw [← this]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hup : ∑ x ∈ V, g x * (killOp V)^[2 * k] g x ≤ G * s * ∑ x ∈ V, g x := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x hx => ?_
    have h1 := iterate_le_mul_survival V hg hgG (2 * k) x
    have h2 : Network.survival (lattice d) V (2 * k) x ≤ s := hxs x hx
    calc g x * (killOp V)^[2 * k] g x ≤ g x * (G * Network.survival (lattice d) V (2 * k) x) :=
          mul_le_mul_of_nonneg_left h1 (hg0 x)
      _ ≤ g x * (G * s) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hG0) (hg0 x)
      _ = G * s * g x := by ring
  -- `G^2 ≤ M` and `(∑ g)^2 ≤ |V| M`
  have hG2 : G ^ 2 ≤ M := by
    rw [hMV]
    exact Finset.single_le_sum (f := fun x => g x ^ 2) (fun x _ => sq_nonneg _) hxgV
  have hS2 : (∑ x ∈ V, g x) ^ 2 ≤ V.card * M := by
    have := Finset.sum_mul_sq_le_sq_mul_sq V (fun _ => (1 : ℝ)) g
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at this
    rw [hMV]
    exact this
  have hS0 : 0 ≤ ∑ x ∈ V, g x := Finset.sum_nonneg fun x _ => hg0 x
  -- combine: `M (1-μ)^{2k} ≤ G s ∑ g`, square it
  have hmain : M * (1 - μ) ^ (2 * k) ≤ G * s * ∑ x ∈ V, g x := by
    rw [pow_mul]
    linarith [hlow, hbk', hup]
  have hsq : (M * (1 - μ) ^ (2 * k)) ^ 2 ≤ (G * s * ∑ x ∈ V, g x) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hm.le (pow_nonneg (by linarith) _)) hmain 2
  have hbound : (G * s * ∑ x ∈ V, g x) ^ 2 ≤ M * (V.card * M) * s ^ 2 := by
    have : (G * s * ∑ x ∈ V, g x) ^ 2 = G ^ 2 * (∑ x ∈ V, g x) ^ 2 * s ^ 2 := by ring
    rw [this]
    gcongr
  have hfin : ((1 - μ) ^ (2 * k)) ^ 2 ≤ (Real.sqrt V.card * s) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    have h := hsq.trans hbound
    have hM2 : 0 < M ^ 2 := by positivity
    have : M ^ 2 * ((1 - μ) ^ (2 * k)) ^ 2 ≤ M ^ 2 * (V.card * s ^ 2) := by
      calc M ^ 2 * ((1 - μ) ^ (2 * k)) ^ 2 = (M * (1 - μ) ^ (2 * k)) ^ 2 := by ring
        _ ≤ M * (V.card * M) * s ^ 2 := h
        _ = M ^ 2 * (V.card * s ^ 2) := by ring
    exact le_of_mul_le_mul_left this hM2
  exact (pow_le_pow_iff_left₀ (pow_nonneg (by linarith) _)
    (mul_nonneg (Real.sqrt_nonneg _) hs0) (by norm_num : (2 : ℕ) ≠ 0)).mp hfin

/-- The law of the walk from `x` gives the confinement event its survival probability. -/
theorem measureReal_stayIn_eq_survival (hd : 1 ≤ d) (B : Finset (Site d)) (n : ℕ)
    (x : Site d) :
    (siteWalkLaw d x).real (Graph.stayIn (B : Set (Site d)) n) =
      Network.survival (lattice d) B n x := by
  have : NeZero d := ⟨by omega⟩
  let S : Set (ℕ → Site d) := Graph.stayIn (B : Set (Site d)) n
  let F : (ℕ → Site d) → ℝ := S.indicator 1
  have hS : MeasurableSet S := Graph.measurableSet_stayIn _ n
  have hFm : Measurable F := (measurable_const : Measurable (1 : (ℕ → Site d) → ℝ)).indicator hS
  have hFb : ∀ X, ‖F X‖ ≤ 1 := by
    intro X
    by_cases hX : X ∈ S <;> simp [F, hX]
  have hdep : ∀ X Y : ℕ → Site d, (∀ k ≤ n, X k = Y k) → F X = F Y := by
    intro X Y hXY
    have hiff : X ∈ S ↔ Y ∈ S := by
      change (∀ k ≤ n, X k ∈ B) ↔ ∀ k ≤ n, Y k ∈ B
      constructor <;> intro h k hk
      · rw [← hXY k hk]; exact h k hk
      · rw [hXY k hk]; exact h k hk
    by_cases hX : X ∈ S
    · simp [F, Set.indicator_of_mem hX, Set.indicator_of_mem (hiff.mp hX)]
    · simp [F, Set.indicator_of_notMem hX,
        Set.indicator_of_notMem (fun h => hX (hiff.mpr h))]
  have hdeg : ∀ y : Site d, 0 < (lattice d).degree y := by
    intro y
    rw [Graph.Zd.degree_eq]
    omega
  have hint : (∫ X, F X ∂(siteWalkLaw d x)) =
      ∫ X, F X ∂(Graph.walkLaw (lattice d) x) := by
    calc ∫ X, F X ∂(siteWalkLaw d x) = Graph.walkExp (lattice d) n x F :=
          (LatticeProb.walkExp_eq_integral n x F hdep).symm
      _ = ∫ X, F X ∂(Graph.walkLaw (lattice d) x) :=
          Graph.walkExp_eq_integral hdeg n x F hFm 1 hFb hdep
  rw [← integral_indicator_one hS, hint, integral_indicator_one hS, measureReal_def,
    Graph.walkLaw_stayIn hdeg, ENNReal.toReal_ofReal (Network.survival_nonneg B n x)]

/-- **The lower bound on the range moment from a Dirichlet ratio**:
`e^{-a|V|} (1 - μ)^{t+1} ≤ √|V| E_0 e^{-a|R_t|}` for any `h` vanishing off `V` with ratio
`μ = latEnergy h / sqMass h ≤ 1`. -/
theorem rangeExp_ge_of_ratio (hd : 1 ≤ d) {a : ℝ} (ha : 0 ≤ a) {V : Finset (Site d)}
    {h : Site d → ℝ} (hV : ∀ x ∉ V, h x = 0) (hm : 0 < sqMass h)
    (hμ : latEnergy h / sqMass h ≤ 1) (t : ℕ) :
    Real.exp (-(a * V.card)) * (1 - latEnergy h / sqMass h) ^ (t + 1)
      ≤ Real.sqrt V.card * rangeExp d a t := by
  classical
  set g : Site d → ℝ := fun x => |h x| with hgdef
  have hgV : ∀ x ∉ V, g x = 0 := fun x hx => by simp [hgdef, hV x hx]
  have hg0 : ∀ x, 0 ≤ g x := fun x => abs_nonneg _
  have hmass : sqMass g = sqMass h := by
    unfold sqMass
    exact tsum_congr fun x => sq_abs _
  have hE : latEnergy g ≤ latEnergy h := latEnergy_abs_le ⟨V, hV⟩
  have hmg : 0 < sqMass g := hmass ▸ hm
  have hμg : latEnergy g / sqMass g ≤ latEnergy h / sqMass h := by
    rw [hmass]
    exact div_le_div_of_nonneg_right hE hm.le
  have hμg1 : latEnergy g / sqMass g ≤ 1 := hμg.trans hμ
  set k := (t + 1) / 2 with hk
  have hk1 : 2 * k ≤ t + 1 := by omega
  have hk2 : t ≤ 2 * k := by omega
  obtain ⟨xs, hxsV, hxs⟩ := exists_survival_ge hd hgV hg0 hmg hμg1 k
  set W : Finset (Site d) := V.image (· + (-xs)) with hW
  have hWcard : W.card = V.card := Finset.card_image_of_injective _ (add_left_injective _)
  have hsurvW : Network.survival (lattice d) W t 0 = Network.survival (lattice d) V t xs := by
    have := survival_image_add V (-xs) t xs
    rwa [add_neg_cancel] at this
  have hprob : (siteWalkLaw d 0).real {X : ℕ → Site d | ∀ j ≤ t, X j ∈ W}
      = Network.survival (lattice d) V t xs := by
    rw [← hsurvW, ← measureReal_stayIn_eq_survival hd W t 0]
    rfl
  have hconf := rangeExp_ge_exp_mul_confinement_probability hd ha W t
  rw [hprob, hWcard] at hconf
  have hmono : Network.survival (lattice d) V (2 * k) xs ≤ Network.survival (lattice d) V t xs :=
    Network.survival_antitone V hk2 xs
  have hμ0 : 0 ≤ 1 - latEnergy h / sqMass h := by linarith
  have hpow1 : (1 - latEnergy h / sqMass h) ^ (t + 1) ≤ (1 - latEnergy h / sqMass h) ^ (2 * k) :=
    pow_le_pow_of_le_one hμ0 (by linarith [div_nonneg (latEnergy_nonneg h) hm.le]) hk1
  have hpow2 : (1 - latEnergy h / sqMass h) ^ (2 * k) ≤ (1 - latEnergy g / sqMass g) ^ (2 * k) :=
    pow_le_pow_left₀ hμ0 (by linarith) _
  have hsq0 : 0 ≤ Real.sqrt V.card := Real.sqrt_nonneg _
  calc Real.exp (-(a * V.card)) * (1 - latEnergy h / sqMass h) ^ (t + 1)
      ≤ Real.exp (-(a * V.card)) * (Real.sqrt V.card * Network.survival (lattice d) V t xs) :=
        mul_le_mul_of_nonneg_left (hpow1.trans (hpow2.trans (hxs.trans
          (mul_le_mul_of_nonneg_left hmono hsq0)))) (Real.exp_nonneg _)
    _ = Real.sqrt V.card * (Real.exp (-(a * V.card)) * Network.survival (lattice d) V t xs) := by
        ring
    _ ≤ Real.sqrt V.card * rangeExp d a t := mul_le_mul_of_nonneg_left hconf hsq0

end Parking

end
