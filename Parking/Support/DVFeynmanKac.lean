import Parking.Support.DVSoftKilling
import Parking.Support.DVConfine
import LatticeProb.Graph.WalkLemmas
import LatticeProb.ParticleHoleLemmas

/-!
# The walk killed softly outside a set

For a finite set `U` and `κ > 0`, let `T_t(U)` be the number of times `j < t` at which the
walk is outside `U`.  Then (`integral_exp_outCount_le`)

  `E_0 e^{-κ T_t(U)} ≤ (1 - dirichletRate d N · (1 - err))^t √(e^κ (2t + 1)^d)`

for every volume `N ≥ |fatten U| + 2^d λ̄/(κ₀ s^2)`, where `λ̄ = dirichletRate d N`,
`κ₀ = (1 - λ̄) κ` and `err = 2s √(|U| + λ̄/(κ₀ s^2)) + s^2 |U| + λ̄/κ₀ < 1`.

The expectation is `(K^t 1)(0)` for the operator `K f = D^2 P f`, where `D = 1` on `U` and
`D = e^{-κ/2}` off `U` (`fkMean`).  Writing `K^t = D S^t D^{-1}` with the symmetric operator
`S f = D P (D f)` (`symOp`), the value at the origin only sees `D^{-1}` on the box of radius
`t`, and `‖S v‖ ≤ ρ ‖v‖` as soon as `⟨w, S w⟩ ≤ ρ ‖w‖²` for every `w ≥ 0`: polarization, with
the positivity of `S`.  The Rayleigh bound with `ρ = 1 - dirichletRate d N (1 - err)` is the
soft-killing inequality `dirichletRate_mul_le_of_soft` applied to `D w`.
-/

noncomputable section

namespace Parking

open LatticeProb MeasureTheory

variable {d : ℕ}

/-! ### The Feynman-Kac recursion -/

/-- The number of times `j < t` at which the path is outside `U`. -/
def outCount (U : Finset (Site d)) (X : ℕ → Site d) (t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range t, if X j ∈ U then 0 else 1

/-- `D^2`: `1` on `U`, `e^{-κ}` off `U`. -/
def killWeight (U : Finset (Site d)) (κ : ℝ) (x : Site d) : ℝ :=
  if x ∈ U then 1 else Real.exp (-κ)

/-- `E_x e^{-κ T_t(U)}`, by its first-step recursion. -/
def fkMean (U : Finset (Site d)) (κ : ℝ) : ℕ → Site d → ℝ
  | 0 => fun _ => 1
  | t + 1 => fun x => killWeight U κ x * walkOp (fkMean U κ t) x

theorem outCount_cons (U : Finset (Site d)) (x : Site d) (X : ℕ → Site d) (t : ℕ) :
    outCount U (Graph.cons x X) (t + 1) = (if x ∈ U then 0 else 1) + outCount U X t := by
  unfold outCount
  rw [Finset.sum_range_succ', add_comm]
  rfl

theorem walkExp_const_mul {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] (n : ℕ) (x : V)
    (c : ℝ) (F : (ℕ → V) → ℝ) :
    Graph.walkExp G n x (fun X => c * F X) = c * Graph.walkExp G n x F := by
  induction n generalizing x F with
  | zero => rfl
  | succ n ih =>
      rw [Graph.walkExp_succ, Graph.walkExp_succ]
      simp_rw [ih]
      rw [← Finset.mul_sum, mul_div_assoc]

theorem walkExp_outCount (U : Finset (Site d)) (κ : ℝ) (t : ℕ) (x : Site d) :
    Graph.walkExp (lattice d) t x (fun X => Real.exp (-κ * outCount U X t)) = fkMean U κ t x := by
  induction t generalizing x with
  | zero => simp [outCount, fkMean, Graph.walkExp]
  | succ t ih =>
      rw [Graph.walkExp_succ]
      have hfac : ∀ X : ℕ → Site d, Real.exp (-κ * outCount U (Graph.cons x X) (t + 1))
          = killWeight U κ x * Real.exp (-κ * outCount U X t) := by
        intro X
        rw [outCount_cons, killWeight]
        split_ifs
        · simp
        · push_cast
          rw [← Real.exp_add]
          congr 1
          ring
      simp_rw [hfac, walkExp_const_mul, ih]
      rw [← Finset.mul_sum, mul_div_assoc, fkMean]
      congr 1
      rw [← Graph.Zd.walkOp_eq]
      rfl

/-- **Feynman-Kac**: `E_x e^{-κ T_t(U)} = fkMean U κ t x`. -/
theorem integral_exp_outCount (hd : 1 ≤ d) (U : Finset (Site d)) (κ : ℝ) (t : ℕ)
    (x : Site d) :
    ∫ X, Real.exp (-κ * outCount U X t) ∂(siteWalkLaw d x) = fkMean U κ t x := by
  have : NeZero d := ⟨by omega⟩
  rw [← LatticeProb.walkExp_eq_integral t x _ fun X Y hXY => ?_, walkExp_outCount]
  congr 3
  unfold outCount
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hXY j (Finset.mem_range.mp hj).le]

/-! ### The symmetric operator -/

/-- `D`: `1` on `U`, `e^{-κ/2}` off `U`. -/
def halfWeight (U : Finset (Site d)) (κ : ℝ) (x : Site d) : ℝ :=
  if x ∈ U then 1 else Real.exp (-κ / 2)

/-- `S f = D P (D f)`. -/
def symOp (U : Finset (Site d)) (κ : ℝ) (f : Site d → ℝ) (x : Site d) : ℝ :=
  halfWeight U κ x * walkOp (fun y => halfWeight U κ y * f y) x

theorem halfWeight_pos (U : Finset (Site d)) (κ : ℝ) (x : Site d) : 0 < halfWeight U κ x := by
  unfold halfWeight; split_ifs <;> positivity

theorem halfWeight_le_one (U : Finset (Site d)) {κ : ℝ} (hκ : 0 ≤ κ) (x : Site d) :
    halfWeight U κ x ≤ 1 := by
  unfold halfWeight
  split_ifs
  · exact le_rfl
  · exact Real.exp_le_one_iff.mpr (by linarith)

theorem halfWeight_sq (U : Finset (Site d)) (κ : ℝ) (x : Site d) :
    halfWeight U κ x ^ 2 = killWeight U κ x := by
  unfold halfWeight killWeight
  split_ifs
  · norm_num
  · rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

/-- `K^t = D S^t D^{-1}`. -/
theorem fkMean_eq_symOp (U : Finset (Site d)) (κ : ℝ) (t : ℕ) (x : Site d) :
    fkMean U κ t x
      = halfWeight U κ x * (symOp U κ)^[t] (fun y => 1 / halfWeight U κ y) x := by
  induction t generalizing x with
  | zero =>
      simp only [fkMean, Function.iterate_zero_apply]
      rw [mul_one_div_cancel (halfWeight_pos U κ x).ne']
  | succ t ih =>
      rw [Function.iterate_succ_apply', fkMean]
      simp only
      rw [symOp, ← mul_assoc, ← sq, halfWeight_sq]
      congr 1
      congr 1
      funext y
      exact ih y

theorem walkOp_congr_box {f g : Site d → ℝ} {x : Site d}
    (h : ∀ y ∈ boxFinset x 1, f y = g y) : walkOp f x = walkOp g x := by
  unfold walkOp nbrSum
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : x + unit i ∈ boxFinset x 1 := by
    rw [mem_boxFinset_iff]
    intro j
    by_cases hj : j = i
    · subst hj; simp [unit]
    · simp [unit, hj]
  have h2 : x - unit i ∈ boxFinset x 1 := by
    rw [mem_boxFinset_iff]
    intro j
    by_cases hj : j = i
    · subst hj; simp [unit]
    · simp [unit, hj]
  rw [h (x + unit i) h1, h (x - unit i) h2]

/-- `S^t f (x)` only sees `f` on the box of radius `t` about `x`. -/
theorem symOp_iterate_congr (U : Finset (Site d)) (κ : ℝ) (t : ℕ) :
    ∀ (f g : Site d → ℝ) (x : Site d), (∀ y ∈ boxFinset x t, f y = g y) →
      (symOp U κ)^[t] f x = (symOp U κ)^[t] g x := by
  induction t with
  | zero =>
      intro f g x h
      exact h x (by rw [mem_boxFinset_iff]; intro i; simp)
  | succ t ih =>
      intro f g x h
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', symOp, symOp]
      congr 1
      refine walkOp_congr_box fun y hy => ?_
      congr 1
      refine ih f g y fun z hz => h z ?_
      rw [mem_boxFinset_iff] at hy hz ⊢
      intro i
      have h1 := hy i
      have h2 := hz i
      have : |z i - x i| ≤ |z i - y i| + |y i - x i| := by
        have := abs_sub_le (z i) (y i) (x i)
        linarith
      push_cast at h1 ⊢
      linarith

theorem FinSupp.symOp {f : Site d → ℝ} (hf : FinSupp f) (U : Finset (Site d)) (κ : ℝ) :
    FinSupp (symOp U κ f) := by
  classical
  obtain ⟨V, hV⟩ := hf
  refine ⟨V.biUnion fun a => boxFinset a 1, fun x hx => ?_⟩
  unfold Parking.symOp
  have : walkOp (fun y => halfWeight U κ y * f y) x = walkOp (fun _ => 0) x := by
    refine walkOp_congr_box fun y hy => ?_
    have hyV : y ∉ V := by
      intro hyV
      apply hx
      refine Finset.mem_biUnion.mpr ⟨y, hyV, ?_⟩
      rw [mem_boxFinset_iff] at hy ⊢
      intro i
      have := hy i
      rw [abs_sub_comm]
      exact this
    rw [hV y hyV, mul_zero]
  rw [this]
  simp [walkOp, nbrSum]

theorem tsum_mul_symOp_comm (hd : 1 ≤ d) (U : Finset (Site d)) (κ : ℝ) {f g : Site d → ℝ}
    (hf : FinSupp f) (hg : FinSupp g) :
    ∑' x, f x * symOp U κ g x = ∑' x, symOp U κ f x * g x := by
  have hf' : FinSupp fun y => halfWeight U κ y * f y := by
    obtain ⟨V, hV⟩ := hf
    exact ⟨V, fun x hx => by show halfWeight U κ x * f x = 0; rw [hV x hx, mul_zero]⟩
  have hg' : FinSupp fun y => halfWeight U κ y * g y := by
    obtain ⟨V, hV⟩ := hg
    exact ⟨V, fun x hx => by show halfWeight U κ x * g x = 0; rw [hV x hx, mul_zero]⟩
  have h1 : ∀ x, f x * symOp U κ g x
      = (halfWeight U κ x * f x) * walkOp (fun y => halfWeight U κ y * g y) x := by
    intro x; rw [symOp]; ring
  have h2 : ∀ x, symOp U κ f x * g x
      = walkOp (fun y => halfWeight U κ y * f y) x * (halfWeight U κ x * g x) := by
    intro x; rw [symOp]; ring
  simp_rw [h1, h2]
  exact tsum_mul_walkOp_comm hd hf' hg'

theorem abs_symOp_le (U : Finset (Site d)) (κ : ℝ) (f : Site d → ℝ) (x : Site d) :
    |symOp U κ f x| ≤ symOp U κ (fun y => |f y|) x := by
  have hD := (halfWeight_pos U κ x).le
  rw [symOp, symOp, abs_mul, abs_of_nonneg hD]
  refine mul_le_mul_of_nonneg_left ?_ hD
  unfold walkOp nbrSum
  rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * d)]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (abs_add_le _ _).trans (le_of_eq ?_)
  rw [abs_mul, abs_mul, abs_of_pos (halfWeight_pos U κ _), abs_of_pos (halfWeight_pos U κ _)]

theorem symOp_add_smul (U : Finset (Site d)) (κ c : ℝ) (f g : Site d → ℝ) (x : Site d) :
    symOp U κ (fun y => c * f y + g y) x = c * symOp U κ f x + symOp U κ g x := by
  simp only [symOp, walkOp, nbrSum]
  have h : ∑ i : Fin d, (halfWeight U κ (x + unit i) * (c * f (x + unit i) + g (x + unit i))
        + halfWeight U κ (x - unit i) * (c * f (x - unit i) + g (x - unit i)))
      = c * ∑ i : Fin d, (halfWeight U κ (x + unit i) * f (x + unit i)
          + halfWeight U κ (x - unit i) * f (x - unit i))
        + ∑ i : Fin d, (halfWeight U κ (x + unit i) * g (x + unit i)
          + halfWeight U κ (x - unit i) * g (x - unit i)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h]
  ring

theorem FinSupp.symOp_iterate {f : Site d → ℝ} (hf : FinSupp f) (U : Finset (Site d)) (κ : ℝ) :
    ∀ t : ℕ, FinSupp ((Parking.symOp U κ)^[t] f)
  | 0 => hf
  | t + 1 => by
      rw [Function.iterate_succ_apply']
      exact (hf.symOp_iterate U κ t).symOp U κ

/-- A Rayleigh bound on nonnegative functions bounds `|⟨w, S w⟩|` for every `w`. -/
theorem abs_tsum_mul_symOp_le (U : Finset (Site d)) (κ : ℝ) {ρ : ℝ}
    (hR : ∀ w : Site d → ℝ, FinSupp w → (∀ x, 0 ≤ w x) →
      ∑' x, w x * symOp U κ w x ≤ ρ * sqMass w) {w : Site d → ℝ} (hw : FinSupp w) :
    |∑' x, w x * symOp U κ w x| ≤ ρ * sqMass w := by
  have hwa : FinSupp fun x => |w x| := hw.comp_lip (φ := fun a => |a|) abs_zero
  have hmass : sqMass (fun x => |w x|) = sqMass w := by
    unfold sqMass; exact tsum_congr fun x => sq_abs _
  have hpt : ∀ x, |w x * symOp U κ w x| ≤ |w x| * symOp U κ (fun y => |w y|) x := by
    intro x
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_symOp_le U κ w x) (abs_nonneg _)
  have hs1 : Summable fun x => w x * symOp U κ w x := hw.summable_mul
  have hs2 : Summable fun x => |w x| * symOp U κ (fun y => |w y|) x := hwa.summable_mul
  calc |∑' x, w x * symOp U κ w x| ≤ ∑' x, |w x * symOp U κ w x| := by
        have := norm_tsum_le_tsum_norm hs1.norm
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' x, |w x| * symOp U κ (fun y => |w y|) x :=
        Summable.tsum_le_tsum hpt hs1.abs hs2
    _ ≤ ρ * sqMass fun x => |w x| := hR _ hwa fun x => abs_nonneg _
    _ = ρ * sqMass w := by rw [hmass]

/-- **The operator norm from the Rayleigh bound**: `‖S v‖² ≤ ρ² ‖v‖²`. -/
theorem sqMass_symOp_le (hd : 1 ≤ d) (U : Finset (Site d)) (κ : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hR : ∀ w : Site d → ℝ, FinSupp w → (∀ x, 0 ≤ w x) →
      ∑' x, w x * symOp U κ w x ≤ ρ * sqMass w) {v : Site d → ℝ} (hv : FinSupp v) :
    sqMass (symOp U κ v) ≤ ρ ^ 2 * sqMass v := by
  set c : ℝ := 1 / ρ with hc
  have hc0 : 0 < c := by positivity
  set u := symOp U κ v with hu
  have huf : FinSupp u := hv.symOp U κ
  have hSu : FinSupp (symOp U κ u) := huf.symOp U κ
  set a := sqMass u
  set b := sqMass v
  have hsym : ∑' x, v x * symOp U κ u x = ∑' x, u x * u x :=
    tsum_mul_symOp_comm hd U κ hv huf
  -- the two test functions
  set wp : Site d → ℝ := fun x => c * u x + v x
  set wm : Site d → ℝ := fun x => c * u x + (-1) * v x
  have hvm : FinSupp fun x => (-1) * v x := by
    obtain ⟨V, hV⟩ := hv; exact ⟨V, fun x hx => by show (-1) * v x = 0; rw [hV x hx, mul_zero]⟩
  have hwp : FinSupp wp := by
    obtain ⟨V, hV⟩ := hv; obtain ⟨W, hW⟩ := huf
    exact ⟨V ∪ W, fun x hx => by
      rw [Finset.mem_union, not_or] at hx
      show c * u x + v x = 0
      rw [hV x hx.1, hW x hx.2]; ring⟩
  have hwm : FinSupp wm := by
    obtain ⟨V, hV⟩ := hv; obtain ⟨W, hW⟩ := huf
    exact ⟨V ∪ W, fun x hx => by
      rw [Finset.mem_union, not_or] at hx
      show c * u x + (-1) * v x = 0
      rw [hV x hx.1, hW x hx.2]; ring⟩
  have hSwp : ∀ x, symOp U κ wp x = c * symOp U κ u x + u x := fun x => symOp_add_smul U κ c u v x
  have hSwm : ∀ x, symOp U κ wm x = c * symOp U κ u x + (-1) * u x := by
    intro x
    have := symOp_add_smul U κ c u (fun y => (-1) * v y) x
    have h2 : symOp U κ (fun y => (-1) * v y) x = (-1) * symOp U κ v x := by
      have := symOp_add_smul U κ (-1) v (fun _ => 0) x
      simp only [add_zero] at this
      rw [this]
      simp [symOp, walkOp, nbrSum]
    rw [this, h2]
  -- finite sums over a common finite set
  obtain ⟨B1, hB1⟩ := hv
  obtain ⟨B2, hB2⟩ := huf
  obtain ⟨B3, hB3⟩ := hSu
  set B := B1 ∪ B2 ∪ B3
  have hvB : ∀ x ∉ B, v x = 0 := fun x hx => hB1 x (by simp [B] at hx; tauto)
  have huB : ∀ x ∉ B, u x = 0 := fun x hx => hB2 x (by simp [B] at hx; tauto)
  have hSuB : ∀ x ∉ B, symOp U κ u x = 0 := fun x hx => hB3 x (by simp [B] at hx; tauto)
  have hfin : ∀ F : Site d → ℝ, (∀ x ∉ B, F x = 0) → ∑' x, F x = ∑ x ∈ B, F x :=
    fun F hF => tsum_eq_sum hF
  have hRp := abs_tsum_mul_symOp_le U κ hR hwp
  have hRm := abs_tsum_mul_symOp_le U κ hR hwm
  rw [hfin _ fun x hx => by simp only [wp, hSwp, hvB x hx, huB x hx, hSuB x hx]; ring] at hRp
  rw [hfin _ fun x hx => by simp only [wm, hSwm, hvB x hx, huB x hx, hSuB x hx]; ring] at hRm
  rw [sqMass_eq_sum (V := B) fun x hx => by show c * u x + v x = 0; rw [hvB x hx, huB x hx]; ring]
    at hRp
  rw [sqMass_eq_sum (V := B) fun x hx => by
    show c * u x + (-1) * v x = 0; rw [hvB x hx, huB x hx]; ring] at hRm
  have ha : a = ∑ x ∈ B, u x ^ 2 := sqMass_eq_sum huB
  have hb : b = ∑ x ∈ B, v x ^ 2 := sqMass_eq_sum hvB
  have hsymB : ∑ x ∈ B, v x * symOp U κ u x = ∑ x ∈ B, u x * u x := by
    rw [← hfin _ fun x hx => by rw [hvB x hx, zero_mul],
      ← hfin _ fun x hx => by rw [huB x hx, zero_mul]]
    exact hsym
  have hp : ∑ x ∈ B, wp x * symOp U κ wp x
      = c ^ 2 * ∑ x ∈ B, u x * symOp U κ u x + 2 * c * a + ∑ x ∈ B, v x * u x := by
    simp only [wp, hSwp]
    rw [ha]
    have : ∀ x ∈ B, (c * u x + v x) * (c * symOp U κ u x + u x)
        = c ^ 2 * (u x * symOp U κ u x) + c * (u x ^ 2) + c * (v x * symOp U κ u x)
          + v x * u x := fun x _ => by ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hsymB]
    have : ∑ x ∈ B, u x * u x = ∑ x ∈ B, u x ^ 2 := Finset.sum_congr rfl fun x _ => by ring
    rw [this]
    ring
  have hm : ∑ x ∈ B, wm x * symOp U κ wm x
      = c ^ 2 * ∑ x ∈ B, u x * symOp U κ u x - 2 * c * a + ∑ x ∈ B, v x * u x := by
    simp only [wm, hSwm]
    rw [ha]
    have : ∀ x ∈ B, (c * u x + (-1) * v x) * (c * symOp U κ u x + (-1) * u x)
        = c ^ 2 * (u x * symOp U κ u x) - c * (u x ^ 2) - c * (v x * symOp U κ u x)
          + v x * u x := fun x _ => by ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hsymB]
    have : ∑ x ∈ B, u x * u x = ∑ x ∈ B, u x ^ 2 := Finset.sum_congr rfl fun x _ => by ring
    rw [this]
    ring
  have hpm : ∑ x ∈ B, wp x ^ 2 + ∑ x ∈ B, wm x ^ 2 = 2 * (c ^ 2 * a + b) := by
    have hpt : ∀ x ∈ B, wp x ^ 2 + wm x ^ 2 = 2 * c ^ 2 * u x ^ 2 + 2 * v x ^ 2 :=
      fun x _ => by simp only [wp, wm]; ring
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hpt, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← ha, ← hb]
    ring
  have h1 := (abs_le.mp hRp).2
  have h2 := (abs_le.mp hRm).1
  rw [hp] at h1
  rw [hm] at h2
  have h4 : 4 * c * a ≤ ρ * (2 * (c ^ 2 * a + b)) := by
    rw [← hpm]
    linarith
  have hca : c * ρ = 1 := by rw [hc]; field_simp
  have h5 : 2 * c * a ≤ 2 * ρ * b := by
    have : ρ * (2 * (c ^ 2 * a + b)) = 2 * c * a * (c * ρ) + 2 * ρ * b := by ring
    rw [this, hca] at h4
    linarith
  have h6 : a ≤ ρ ^ 2 * b := by
    have := mul_le_mul_of_nonneg_left h5 hρ.le
    have e1 : ρ * (2 * c * a) = 2 * a * (c * ρ) := by ring
    have e2 : ρ * (2 * ρ * b) = 2 * (ρ ^ 2 * b) := by ring
    rw [e1, e2, hca] at this
    linarith
  exact h6

/-- Iterating: `‖S^t v‖² ≤ ρ^{2t} ‖v‖²`. -/
theorem sqMass_symOp_iterate_le (hd : 1 ≤ d) (U : Finset (Site d)) (κ : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hR : ∀ w : Site d → ℝ, FinSupp w → (∀ x, 0 ≤ w x) →
      ∑' x, w x * symOp U κ w x ≤ ρ * sqMass w) {v : Site d → ℝ} (hv : FinSupp v) (t : ℕ) :
    sqMass ((symOp U κ)^[t] v) ≤ (ρ ^ 2) ^ t * sqMass v := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hft : FinSupp ((symOp U κ)^[t] v) := hv.symOp_iterate U κ t
      rw [Function.iterate_succ_apply', pow_succ]
      calc sqMass (symOp U κ ((symOp U κ)^[t] v)) ≤ ρ ^ 2 * sqMass ((symOp U κ)^[t] v) :=
            sqMass_symOp_le hd U κ hρ hR hft
        _ ≤ ρ ^ 2 * ((ρ ^ 2) ^ t * sqMass v) := mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (ρ ^ 2) ^ t * ρ ^ 2 * sqMass v := by ring

/-- **The Feynman-Kac bound from a Rayleigh bound.** -/
theorem fkMean_le (hd : 1 ≤ d) (U : Finset (Site d)) {κ : ℝ} (hκ : 0 ≤ κ) {ρ : ℝ} (hρ : 0 < ρ)
    (hR : ∀ w : Site d → ℝ, FinSupp w → (∀ x, 0 ≤ w x) →
      ∑' x, w x * symOp U κ w x ≤ ρ * sqMass w) (t : ℕ) :
    fkMean U κ t 0 ≤ ρ ^ t * Real.sqrt (Real.exp κ * (2 * t + 1) ^ d) := by
  classical
  set B := boxFinset (0 : Site d) t
  set v : Site d → ℝ := fun y => if y ∈ B then 1 / halfWeight U κ y else 0
  have hv : FinSupp v := ⟨B, fun x hx => by simp [v, hx]⟩
  have hloc : (symOp U κ)^[t] (fun y => 1 / halfWeight U κ y) 0 = (symOp U κ)^[t] v 0 :=
    symOp_iterate_congr U κ t _ _ 0 fun y hy => by
      simp only [v]; rw [ite_eq_left (show y ∈ B from hy)]
  rw [fkMean_eq_symOp, hloc]
  have hD0 := halfWeight_pos U κ 0
  have hD1 := halfWeight_le_one U hκ 0
  have hft : FinSupp ((symOp U κ)^[t] v) := hv.symOp_iterate U κ t
  set y := (symOp U κ)^[t] v 0
  have hy2 : y ^ 2 ≤ sqMass ((symOp U κ)^[t] v) :=
    hft.summable_sq.le_tsum 0 fun x _ => sq_nonneg _
  have hmass : sqMass v ≤ Real.exp κ * (2 * t + 1) ^ d := by
    rw [sqMass_eq_sum (V := B) fun x hx => by simp [v, hx]]
    calc ∑ x ∈ B, v x ^ 2 ≤ ∑ _x ∈ B, Real.exp κ := by
          refine Finset.sum_le_sum fun x hx => ?_
          simp only [v, ite_eq_left hx]
          have hD := halfWeight_pos U κ x
          have hDlow : Real.exp (-κ / 2) ≤ halfWeight U κ x := by
            unfold halfWeight
            split_ifs
            · exact Real.exp_le_one_iff.mpr (by linarith)
            · exact le_rfl
          rw [div_pow, one_pow, div_le_iff₀ (by positivity)]
          calc (1 : ℝ) = Real.exp κ * Real.exp (-κ / 2) ^ 2 := by
                rw [← Real.exp_nat_mul, ← Real.exp_add]
                rw [show κ + ((2 : ℕ) : ℝ) * (-κ / 2) = 0 by push_cast; ring, Real.exp_zero]
            _ ≤ Real.exp κ * halfWeight U κ x ^ 2 := by gcongr
      _ = Real.exp κ * (2 * t + 1) ^ d := by
          rw [Finset.sum_const, nsmul_eq_mul, card_boxFinset_zero]
          push_cast
          ring
  have hiter := sqMass_symOp_iterate_le hd U κ hρ hR hv t
  have hy2' : y ^ 2 ≤ (ρ ^ t * Real.sqrt (Real.exp κ * (2 * t + 1) ^ d)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), ← pow_mul, mul_comm t 2, pow_mul]
    exact hy2.trans (hiter.trans (mul_le_mul_of_nonneg_left hmass (by positivity)))
  have hyabs : |y| ≤ ρ ^ t * Real.sqrt (Real.exp κ * (2 * t + 1) ^ d) :=
    abs_le_of_sq_le_sq' hy2' (by positivity) |> fun h => abs_le.mpr h
  calc halfWeight U κ 0 * y ≤ halfWeight U κ 0 * |y| :=
        mul_le_mul_of_nonneg_left (le_abs_self y) hD0.le
    _ ≤ 1 * |y| := mul_le_mul_of_nonneg_right hD1 (abs_nonneg _)
    _ = |y| := one_mul _
    _ ≤ _ := hyabs

/-! ### The Rayleigh bound from soft killing -/

theorem sqMass_const_mul (c : ℝ) (g : Site d → ℝ) :
    sqMass (fun x => c * g x) = c ^ 2 * sqMass g := by
  unfold sqMass
  rw [← tsum_mul_left]
  exact tsum_congr fun x => by ring

theorem latEnergy_const_mul (c : ℝ) (g : Site d → ℝ) :
    latEnergy (fun x => c * g x) = c ^ 2 * latEnergy g := by
  unfold latEnergy dirEnergy
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← tsum_mul_left]
  exact tsum_congr fun x => by ring

theorem massOff_const_mul (U : Finset (Site d)) (c : ℝ) (g : Site d → ℝ) :
    massOff U (fun x => c * g x) = c ^ 2 * massOff U g := by
  unfold massOff
  rw [← tsum_mul_left]
  exact tsum_congr fun x => by split_ifs <;> ring

theorem tsum_mul_symOp_eq (hd : 1 ≤ d) (U : Finset (Site d)) (κ : ℝ) {w : Site d → ℝ}
    (hw : FinSupp w) :
    ∑' x, w x * symOp U κ w x = sqMass (fun x => halfWeight U κ x * w x)
      - latEnergy (fun x => halfWeight U κ x * w x) := by
  have hg₀fs : FinSupp fun x => halfWeight U κ x * w x := by
    obtain ⟨V, hV⟩ := hw
    exact ⟨V, fun x hx => by show halfWeight U κ x * w x = 0; rw [hV x hx, mul_zero]⟩
  rw [latEnergy_eq_sqMass_sub hd hg₀fs]
  ring_nf
  refine tsum_congr fun x => ?_
  simp only [symOp]
  ring

theorem sqMass_eq_halfWeight (U : Finset (Site d)) (κ : ℝ) {w : Site d → ℝ} (hw : FinSupp w) :
    sqMass w = sqMass (fun x => halfWeight U κ x * w x)
      + (Real.exp κ - 1) * massOff U (fun x => halfWeight U κ x * w x) := by
  have hg₀fs : FinSupp fun x => halfWeight U κ x * w x := by
    obtain ⟨V, hV⟩ := hw
    exact ⟨V, fun x hx => by show halfWeight U κ x * w x = 0; rw [hV x hx, mul_zero]⟩
  have hs1 : Summable fun x => (halfWeight U κ x * w x) ^ 2 := hg₀fs.summable_sq
  have hs2 : Summable fun x => if x ∈ U then (0 : ℝ) else (halfWeight U κ x * w x) ^ 2 := by
    obtain ⟨V, hV⟩ := hw
    exact summable_of_ne_finset_zero (s := V) fun x hx => by
      split_ifs <;> simp [hV x hx]
  unfold sqMass massOff
  rw [← tsum_mul_left, ← Summable.tsum_add hs1 (hs2.mul_left _)]
  refine tsum_congr fun x => ?_
  simp only [halfWeight]
  split_ifs
  · ring
  · have : Real.exp κ * Real.exp (-κ / 2) ^ 2 = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      rw [show κ + ((2 : ℕ) : ℝ) * (-κ / 2) = 0 by push_cast; ring, Real.exp_zero]
    calc w x ^ 2 = (Real.exp κ * Real.exp (-κ / 2) ^ 2) * w x ^ 2 := by rw [this, one_mul]
      _ = _ := by ring

/-- **The Rayleigh bound**: with `Λ = dirichletRate d N < 1`, `κ₀ = (1 - Λ) κ` and
`err = 2s √(|U| + Λ/(κ₀ s^2)) + s^2 |U| + Λ/κ₀ < 1`, every `w ≥ 0` has
`⟨w, S w⟩ ≤ (1 - Λ (1 - err)) ‖w‖²` once `N ≥ |fatten U| + 2^d Λ/(κ₀ s^2)`. -/
theorem rayleigh_symOp_le (hd : 1 ≤ d) (U : Finset (Site d)) {κ s : ℝ} (hκ : 0 < κ)
    (hs : 0 < s) {N : ℕ} (hΛ1 : dirichletRate d N < 1)
    (hN : ((fatten U).card : ℝ) + 2 ^ d * (dirichletRate d N
      / ((1 - dirichletRate d N) * κ * s ^ 2)) ≤ N)
    (herr : 2 * s * Real.sqrt (U.card + dirichletRate d N
        / ((1 - dirichletRate d N) * κ * s ^ 2)) + s ^ 2 * U.card
      + dirichletRate d N / ((1 - dirichletRate d N) * κ) < 1) :
    ∀ w : Site d → ℝ, FinSupp w → (∀ x, 0 ≤ w x) →
      ∑' x, w x * symOp U κ w x
        ≤ (1 - dirichletRate d N * (1 - (2 * s * Real.sqrt (U.card + dirichletRate d N
          / ((1 - dirichletRate d N) * κ * s ^ 2)) + s ^ 2 * U.card
          + dirichletRate d N / ((1 - dirichletRate d N) * κ)))) * sqMass w := by
  intro w hw hw0
  set Λ := dirichletRate d N with hΛ
  have hΛ0 : 0 ≤ Λ := dirichletRate_nonneg d N
  set κ₀ := (1 - Λ) * κ with hκ₀
  have hκ₀0 : 0 < κ₀ := mul_pos (by linarith) hκ
  set err : ℝ → ℝ := fun lam => 2 * s * Real.sqrt (U.card + lam / (κ₀ * s ^ 2))
    + s ^ 2 * U.card + lam / κ₀ with herrdef
  have herr_mono : ∀ lam, lam ≤ Λ → err lam ≤ err Λ := by
    intro lam hlam
    simp only [herrdef]
    have h1 : lam / (κ₀ * s ^ 2) ≤ Λ / (κ₀ * s ^ 2) :=
      div_le_div_of_nonneg_right hlam (by positivity)
    have h2 : lam / κ₀ ≤ Λ / κ₀ := div_le_div_of_nonneg_right hlam hκ₀0.le
    have h3 := Real.sqrt_le_sqrt (by linarith : (U.card : ℝ) + lam / (κ₀ * s ^ 2)
      ≤ U.card + Λ / (κ₀ * s ^ 2))
    nlinarith
  have herrΛ : err Λ < 1 := by
    simp only [herrdef, hκ₀]
    rw [show (1 - Λ) * κ * s ^ 2 = (1 - Λ) * κ * s ^ 2 from rfl]
    exact herr
  have herr0 : ∀ lam, 0 ≤ lam → 0 ≤ err lam := fun lam h => by simp only [herrdef]; positivity
  set lstar := Λ * (1 - err Λ) with hlstar
  have hlstar_le : lstar ≤ Λ := by
    have := herr0 Λ hΛ0
    nlinarith
  have hlstar0 : 0 ≤ lstar := mul_nonneg hΛ0 (by linarith)
  change ∑' x, w x * symOp U κ w x ≤ (1 - lstar) * sqMass w
  by_contra hcon
  push Not at hcon
  -- the function `g₀ = D w`
  set g₀ : Site d → ℝ := fun x => halfWeight U κ x * w x with hg₀
  have hg₀fs : FinSupp g₀ := by
    obtain ⟨V, hV⟩ := hw
    exact ⟨V, fun x hx => by show halfWeight U κ x * w x = 0; rw [hV x hx, mul_zero]⟩
  have hg₀0 : ∀ x, 0 ≤ g₀ x := fun x => mul_nonneg (halfWeight_pos U κ x).le (hw0 x)
  have hquad : ∑' x, w x * symOp U κ w x = sqMass g₀ - latEnergy g₀ :=
    tsum_mul_symOp_eq hd U κ hw
  have hmassw : sqMass w = sqMass g₀ + (Real.exp κ - 1) * massOff U g₀ :=
    sqMass_eq_halfWeight U κ hw
  set M := sqMass g₀ with hM
  set Mo := massOff U g₀ with hMo
  have hMo0 : 0 ≤ Mo := massOff_nonneg U g₀
  have hE0 : 0 ≤ latEnergy g₀ := latEnergy_nonneg g₀
  have hexpκ : κ ≤ Real.exp κ - 1 := by linarith [Real.add_one_le_exp κ]
  -- `E + (1 - λ*)(e^κ - 1) Mo < λ* M`
  have hkey : latEnergy g₀ + (1 - lstar) * (Real.exp κ - 1) * Mo < lstar * M := by
    rw [hquad, hmassw] at hcon
    have hexp : (1 - lstar) * (M + (Real.exp κ - 1) * Mo)
        = (1 - lstar) * M + (1 - lstar) * (Real.exp κ - 1) * Mo := by ring
    rw [hexp] at hcon
    have hexp2 : (1 - lstar) * M = M - lstar * M := by ring
    linarith
  have hMpos : 0 < M := by
    by_contra hM0
    push Not at hM0
    have hM0' : M = 0 := le_antisymm hM0 (sqMass_nonneg _)
    rw [hM0', mul_zero] at hkey
    have h1 : 0 ≤ (1 - lstar) * (Real.exp κ - 1) * Mo :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) hMo0
    linarith
  -- normalize
  set c : ℝ := 1 / Real.sqrt M with hc
  have hc2 : c ^ 2 * M = 1 := by
    rw [hc, div_pow, one_pow, Real.sq_sqrt hMpos.le]
    field_simp
  set g : Site d → ℝ := fun x => c * g₀ x with hg
  have hgfs : FinSupp g := by
    obtain ⟨V, hV⟩ := hg₀fs
    exact ⟨V, fun x hx => by show c * g₀ x = 0; rw [hV x hx, mul_zero]⟩
  have hg0 : ∀ x, 0 ≤ g x := fun x => mul_nonneg (by positivity) (hg₀0 x)
  have hgM : sqMass g = 1 := by rw [hg, sqMass_const_mul, hc2]
  set lam := latEnergy g + κ₀ * massOff U g with hlam
  have hlamlt : lam < lstar := by
    have h1 : κ₀ ≤ (1 - lstar) * (Real.exp κ - 1) := by
      rw [hκ₀]
      exact mul_le_mul (by linarith) hexpκ hκ.le (by linarith)
    have h2 : lam = c ^ 2 * (latEnergy g₀ + κ₀ * Mo) := by
      rw [hlam, hg, latEnergy_const_mul, massOff_const_mul]
      ring
    have h3 : latEnergy g₀ + κ₀ * Mo < lstar * M := by
      have := mul_le_mul_of_nonneg_right h1 hMo0
      linarith
    rw [h2]
    have hc0 : 0 < c ^ 2 := by positivity
    calc c ^ 2 * (latEnergy g₀ + κ₀ * Mo) < c ^ 2 * (lstar * M) :=
          mul_lt_mul_of_pos_left h3 hc0
      _ = lstar * (c ^ 2 * M) := by ring
      _ = lstar := by rw [hc2, mul_one]
  have hlam0 : 0 ≤ lam := add_nonneg (latEnergy_nonneg g)
    (mul_nonneg hκ₀0.le (massOff_nonneg U g))
  have hlamΛ : lam ≤ Λ := hlamlt.le.trans hlstar_le
  have hNlam : ((fatten U).card : ℝ) + 2 ^ d * (lam / (κ₀ * s ^ 2)) ≤ N := by
    refine le_trans ?_ hN
    have : lam / (κ₀ * s ^ 2) ≤ Λ / ((1 - Λ) * κ * s ^ 2) := by
      rw [show (1 - Λ) * κ * s ^ 2 = κ₀ * s ^ 2 by rw [hκ₀]]
      exact div_le_div_of_nonneg_right hlamΛ (by positivity)
    have h2d : (0 : ℝ) ≤ 2 ^ d := by positivity
    have := mul_le_mul_of_nonneg_left this h2d
    linarith
  have herrlam : err lam < 1 := lt_of_le_of_lt (herr_mono lam hlamΛ) herrΛ
  have hsoft := dirichletRate_mul_le_of_soft hgfs hg0 hgM hκ₀0 hs le_rfl hNlam herrlam
  have h1 : Λ * (1 - err Λ) ≤ Λ * (1 - err lam) :=
    mul_le_mul_of_nonneg_left (by linarith [herr_mono lam hlamΛ]) hΛ0
  have h2 : Λ * (1 - err lam) ≤ lam := hsoft
  linarith

/-! ### The probability of a short time outside `U` -/

theorem measurable_outCount (U : Finset (Site d)) (t : ℕ) :
    Measurable fun X : ℕ → Site d => outCount U X t :=
  measurable_of_dependsUpTo (n := t) fun X Y hXY => by
    unfold outCount
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hXY j (Finset.mem_range.mp hj).le]

/-- **A short time outside `U` costs the soft-killing rate**:
`P_0(T_t(U) ≤ θ) ≤ e^{κ θ} E_0 e^{-κ T_t(U)}`. -/
theorem measureReal_outCount_le (hd : 1 ≤ d) (U : Finset (Site d)) {κ : ℝ} (hκ : 0 ≤ κ)
    (θ : ℝ) (t : ℕ) :
    (siteWalkLaw d 0).real {X | (outCount U X t : ℝ) ≤ θ}
      ≤ Real.exp (κ * θ) * fkMean U κ t 0 := by
  have : NeZero d := ⟨by omega⟩
  have hm := measurable_outCount (d := d) U t
  set S : Set (ℕ → Site d) := {X | (outCount U X t : ℝ) ≤ θ} with hS
  have hSm : MeasurableSet S := measurableSet_le (Measurable.of_discrete.comp hm) measurable_const
  have hfm : Measurable fun X : ℕ → Site d => Real.exp (-κ * outCount U X t) :=
    (Measurable.of_discrete (f := fun k : ℕ => Real.exp (-κ * k))).comp hm
  have hint : Integrable (fun X : ℕ → Site d => Real.exp (κ * θ) * Real.exp (-κ * outCount U X t))
      (siteWalkLaw d 0) := by
    refine Integrable.const_mul ?_ _
    refine Integrable.of_bound hfm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by
      have : (0 : ℝ) ≤ outCount U X t := Nat.cast_nonneg _
      nlinarith)
  have hind : Integrable (S.indicator fun _ => (1 : ℝ)) (siteWalkLaw d 0) :=
    (integrable_const (1 : ℝ)).indicator hSm
  calc (siteWalkLaw d 0).real S = ∫ X, S.indicator (fun _ => (1 : ℝ)) X ∂(siteWalkLaw d 0) := by
        rw [integral_indicator_const _ hSm, smul_eq_mul, mul_one]
    _ ≤ ∫ X, Real.exp (κ * θ) * Real.exp (-κ * outCount U X t) ∂(siteWalkLaw d 0) := by
        refine integral_mono hind hint fun X => ?_
        by_cases hX : X ∈ S
        · rw [Set.indicator_of_mem hX, ← Real.exp_add]
          refine Real.one_le_exp_iff.mpr ?_
          have : (outCount U X t : ℝ) ≤ θ := hX
          nlinarith
        · rw [Set.indicator_of_notMem hX]
          positivity
    _ = Real.exp (κ * θ) * fkMean U κ t 0 := by
        rw [integral_const_mul, integral_exp_outCount hd]

end Parking

end
