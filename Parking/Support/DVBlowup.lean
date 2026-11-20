import Parking.Support.DVEnergy

/-!
# Blowing up a lattice function by linear interpolation

Scaling a function on `ℤ^d` up by an integer factor `L`, one coordinate at a time, by linear
interpolation between consecutive multiples of `L`.  In the coordinate `i`, write a site as
`y = x + (L q + s) e_i - x_i e_i` with `x_i = q` and `0 ≤ s < L` (`coordSplit`); the blown-up
function is `((L - s) h(x) + s h(x + e_i)) / L` (`blowStep`).  Then

- the energy in the direction `e_i` drops by the factor `L`: every increment is `1/L` of an
  increment of `h`, and each is repeated `L` times (`dirEnergy_blowStep_self`);
- the energy in another direction grows at most by the factor `L`, by convexity of the square
  (`dirEnergy_blowStep_le`);
- the mass grows by the factor `L` up to the energy in the direction `e_i`
  (`sqMass_blowStep_ge`).

Composing over the `d` coordinates multiplies every Dirichlet ratio by `L^{-2}` up to a
relative error controlled by the ratio itself; this is how the least Dirichlet ratio of `n`
sites is compared with that of `L^d n` sites.
-/

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-! ### Sums over a finite-fibred reindexing -/

/-- A finitely supported sum over `α` is the sum over `β` of the finite fibre sums along an
equivalence `α ≃ β × ι` with `ι` finite. -/
theorem tsum_eq_tsum_sum_of_equiv {α β ι : Type*} [Fintype ι] (e : α ≃ β × ι) (F : α → ℝ)
    (V : Finset α) (hV : ∀ a ∉ V, F a = 0) :
    ∑' a, F a = ∑' b, ∑ s, F (e.symm (b, s)) := by
  classical
  have hsum : Summable fun p : β × ι => F (e.symm p) := by
    refine summable_of_ne_finset_zero (s := V.image e) fun p hp => hV _ fun h => hp ?_
    exact Finset.mem_image.mpr ⟨_, h, e.apply_symm_apply p⟩
  rw [← e.symm.tsum_eq F, hsum.tsum_prod' fun b => (Summable.of_finite)]
  exact tsum_congr fun b => tsum_fintype _

/-! ### Splitting one coordinate modulo `L` -/

/-- `y ↦ (y with y_i replaced by ⌊y_i / L⌋, y_i mod L)`. -/
def coordSplit (L : ℕ) [NeZero L] (i : Fin d) : Site d ≃ Site d × Fin L where
  toFun y := (Function.update y i (Int.divModEquiv L (y i)).1, (Int.divModEquiv L (y i)).2)
  invFun p := Function.update p.1 i ((Int.divModEquiv L).symm (p.1 i, p.2))
  left_inv y := by
    simp only [Function.update_idem, Function.update_self, Prod.mk.eta, Equiv.symm_apply_apply,
      Function.update_eq_self]
  right_inv p := by
    obtain ⟨x, s⟩ := p
    simp only [Function.update_self, Equiv.apply_symm_apply, Function.update_idem,
      Function.update_eq_self]

theorem coordSplit_symm_apply (L : ℕ) [NeZero L] (i : Fin d) (x : Site d) (s : Fin L) :
    (coordSplit L i).symm (x, s) = Function.update x i (x i * L + s) := by
  simp [coordSplit]

theorem update_add_unit_self (x : Site d) (i : Fin d) (v : ℤ) :
    Function.update x i v + unit i = Function.update x i (v + 1) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [unit]
  · simp [unit, hj]

theorem update_add_unit_of_ne (x : Site d) {i j : Fin d} (hij : j ≠ i) (v : ℤ) :
    Function.update x i v + unit j = Function.update (x + unit j) i v := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [unit, Ne.symm hij]
  · simp [unit, hk]

theorem update_add_unit_same (x : Site d) (i : Fin d) (v : ℤ) :
    Function.update (x + unit i) i v = Function.update x i v := by
  funext k
  by_cases hk : k = i
  · subst hk; simp
  · simp [unit, hk]

/-- Moving one step in the direction `e_i` from the split point `(x, s)`: the residue grows by
one, or wraps around to `0` with the coarse coordinate moving to `x + e_i`. -/
theorem coordSplit_symm_add_unit (L : ℕ) [NeZero L] (i : Fin d) (x : Site d) (s : Fin L) :
    (coordSplit L i).symm (x, s) + unit i =
      if h : (s : ℕ) + 1 < L then (coordSplit L i).symm (x, ⟨s + 1, h⟩)
      else (coordSplit L i).symm (x + unit i, ⟨0, Nat.pos_of_neZero L⟩) := by
  rw [coordSplit_symm_apply, update_add_unit_self]
  split_ifs with h
  · rw [coordSplit_symm_apply]
    congr 1
    push_cast
    ring
  · rw [coordSplit_symm_apply, update_add_unit_same]
    have hs : (s : ℕ) + 1 = L := by have := s.isLt; omega
    congr 1
    simp only [Pi.add_apply, unit, Pi.single_eq_same, Nat.cast_zero, add_zero]
    have : ((s : ℕ) : ℤ) + 1 = (L : ℤ) := by exact_mod_cast hs
    linear_combination this

/-- Moving in another direction keeps the residue and moves the coarse point. -/
theorem coordSplit_symm_add_unit_of_ne (L : ℕ) [NeZero L] {i j : Fin d} (hij : j ≠ i)
    (x : Site d) (s : Fin L) :
    (coordSplit L i).symm (x, s) + unit j = (coordSplit L i).symm (x + unit j, s) := by
  rw [coordSplit_symm_apply, coordSplit_symm_apply, update_add_unit_of_ne x hij]
  congr 2
  simp [unit, Ne.symm hij]

/-! ### One interpolation step -/

/-- Linear interpolation in the coordinate `i` at scale `L`. -/
def blowStep (L : ℕ) [NeZero L] (i : Fin d) (h : Site d → ℝ) (y : Site d) : ℝ :=
  ((L - ((coordSplit L i y).2 : ℕ)) * h (coordSplit L i y).1
    + ((coordSplit L i y).2 : ℕ) * h ((coordSplit L i y).1 + unit i)) / L

theorem blowStep_symm (L : ℕ) [NeZero L] (i : Fin d) (h : Site d → ℝ) (x : Site d)
    (s : Fin L) :
    blowStep L i h ((coordSplit L i).symm (x, s))
      = ((L - (s : ℕ)) * h x + (s : ℕ) * h (x + unit i)) / L := by
  simp only [blowStep, Equiv.apply_symm_apply]

theorem blowStep_finSupp (L : ℕ) [NeZero L] (i : Fin d) {h : Site d → ℝ} (V : Finset (Site d))
    (hV : ∀ x ∉ V, h x = 0) :
    ∀ y ∉ (V ∪ V.image fun a => a - unit i).biUnion
        (fun x => (Finset.univ : Finset (Fin L)).image fun s => (coordSplit L i).symm (x, s)),
      blowStep L i h y = 0 := by
  classical
  intro y hy
  have hy' : y = (coordSplit L i).symm (coordSplit L i y) := ((coordSplit L i).symm_apply_apply y).symm
  set p := coordSplit L i y with hp
  obtain ⟨x, s⟩ := p
  rw [hy', blowStep_symm]
  have hx : x ∉ V ∪ V.image fun a => a - unit i := by
    intro hx
    apply hy
    refine Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨s, Finset.mem_univ _, ?_⟩⟩
    rw [hy']
  rw [Finset.mem_union, not_or] at hx
  have h1 : h x = 0 := hV x hx.1
  have h2 : h (x + unit i) = 0 := hV _ fun hm =>
    hx.2 (Finset.mem_image.mpr ⟨x + unit i, hm, by abel⟩)
  rw [h1, h2]
  ring

theorem sum_fin_cast (L : ℕ) : ∑ s : Fin L, ((s : ℕ) : ℝ) = L * (L - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun s => (s : ℝ)) L]
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

theorem sum_fin_sub_cast (L : ℕ) : ∑ s : Fin L, ((L : ℝ) - ((s : ℕ) : ℝ)) = L * (L + 1) / 2 := by
  rw [Finset.sum_sub_distrib, sum_fin_cast, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- A sum split along `coordSplit`. -/
theorem tsum_coordSplit (L : ℕ) [NeZero L] (i : Fin d) {F : Site d → ℝ} (hF : FinSupp F) :
    ∑' y, F y = ∑' x, ∑ s : Fin L, F ((coordSplit L i).symm (x, s)) := by
  obtain ⟨V, hV⟩ := hF
  exact tsum_eq_tsum_sum_of_equiv (coordSplit L i) F V hV

theorem FinSupp.blowStep {h : Site d → ℝ} (hh : FinSupp h) (L : ℕ) [NeZero L] (i : Fin d) :
    FinSupp (blowStep L i h) := by
  obtain ⟨V, hV⟩ := hh
  exact ⟨_, blowStep_finSupp L i V hV⟩

theorem FinSupp.dirSq {g : Site d → ℝ} (hg : FinSupp g) (a : Site d) :
    FinSupp fun x => (g (x + a) - g x) ^ 2 := by
  obtain ⟨W, hW⟩ := hg.comp_add a
  obtain ⟨V, hV⟩ := hg
  refine ⟨V ∪ W, fun x hx => ?_⟩
  rw [Finset.mem_union, not_or] at hx
  have h1 : g (x + a) = 0 := hW x hx.2
  show (g (x + a) - g x) ^ 2 = 0
  rw [hV x hx.1, h1]
  ring

theorem FinSupp.sq {g : Site d → ℝ} (hg : FinSupp g) : FinSupp fun x => g x ^ 2 := by
  obtain ⟨V, hV⟩ := hg
  exact ⟨V, fun x hx => by show g x ^ 2 = 0; rw [hV x hx]; ring⟩

/-- The increment of the interpolation in its own direction is `1/L` of an increment of `h`. -/
theorem blowStep_add_unit_sub (L : ℕ) [NeZero L] (i : Fin d) (h : Site d → ℝ) (x : Site d)
    (s : Fin L) :
    blowStep L i h ((coordSplit L i).symm (x, s) + unit i)
        - blowStep L i h ((coordSplit L i).symm (x, s))
      = (h (x + unit i) - h x) / L := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  rw [coordSplit_symm_add_unit]
  split_ifs with hs
  · rw [blowStep_symm, blowStep_symm]
    field_simp
    push_cast
    ring
  · rw [blowStep_symm, blowStep_symm]
    have hsL : ((s : ℕ) : ℝ) = L - 1 := by
      have h' : (s : ℕ) + 1 = L := by have := s.isLt; omega
      have h'' : ((s : ℕ) : ℝ) + 1 = L := by exact_mod_cast h'
      linarith
    rw [hsL]
    field_simp
    simp
    ring

/-- **The energy in the interpolated direction drops by the factor `L`.** -/
theorem dirEnergy_blowStep_self (L : ℕ) [NeZero L] (i : Fin d) {h : Site d → ℝ}
    (hh : FinSupp h) :
    dirEnergy i (blowStep L i h) = dirEnergy i h / L := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  unfold dirEnergy
  rw [tsum_coordSplit L i ((hh.blowStep L i).dirSq (unit i))]
  simp_rw [blowStep_add_unit_sub, div_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← tsum_div_const]
  refine tsum_congr fun x => ?_
  field_simp

/-- Interpolation in the coordinate `i` commutes with differences in another direction. -/
theorem blowStep_add_unit_of_ne (L : ℕ) [NeZero L] {i j : Fin d} (hij : j ≠ i)
    (h : Site d → ℝ) (x : Site d) (s : Fin L) :
    blowStep L i h ((coordSplit L i).symm (x, s) + unit j)
        - blowStep L i h ((coordSplit L i).symm (x, s))
      = ((L - (s : ℕ)) * (h (x + unit j) - h x)
          + (s : ℕ) * (h (x + unit i + unit j) - h (x + unit i))) / L := by
  rw [coordSplit_symm_add_unit_of_ne L hij, blowStep_symm, blowStep_symm, add_right_comm]
  ring

theorem sq_convex_comb_le {α β a b : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hL : 0 < α + β) :
    ((α * a + β * b) / (α + β)) ^ 2 ≤ (α * a ^ 2 + β * b ^ 2) / (α + β) := by
  rw [div_pow, div_le_div_iff₀ (by positivity) hL]
  have : 0 ≤ α * β * (a - b) ^ 2 := by positivity
  nlinarith [this]

/-- **The energy in another direction grows at most by the factor `L`.** -/
theorem dirEnergy_blowStep_le (L : ℕ) [NeZero L] {i j : Fin d} (hij : j ≠ i) {h : Site d → ℝ}
    (hh : FinSupp h) :
    dirEnergy j (blowStep L i h) ≤ L * dirEnergy j h := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_neZero L
  set D : Site d → ℝ := fun z => (h (z + unit j) - h z) ^ 2 with hD
  have hDs : Summable D := hh.summable_dir j
  have hDs' : Summable fun x => D (x + unit i) := by
    obtain ⟨V, hV⟩ := hh.dirSq (unit j)
    exact summable_of_ne_finset_zero (s := V.image fun a => a - unit i) fun x hx =>
      hV _ fun hm => hx (Finset.mem_image.mpr ⟨_, hm, by abel⟩)
  unfold dirEnergy
  rw [tsum_coordSplit L i ((hh.blowStep L i).dirSq (unit j))]
  have hpt : ∀ x, ∑ s : Fin L, (blowStep L i h ((coordSplit L i).symm (x, s) + unit j)
        - blowStep L i h ((coordSplit L i).symm (x, s))) ^ 2
      ≤ (L + 1) / 2 * D x + (L - 1) / 2 * D (x + unit i) := by
    intro x
    have hterm : ∀ s : Fin L, (blowStep L i h ((coordSplit L i).symm (x, s) + unit j)
          - blowStep L i h ((coordSplit L i).symm (x, s))) ^ 2
        ≤ ((L - (s : ℕ)) * D x + (s : ℕ) * D (x + unit i)) / L := by
      intro s
      rw [blowStep_add_unit_of_ne L hij]
      have hs : ((s : ℕ) : ℝ) ≤ L := by exact_mod_cast s.isLt.le
      have h1 := sq_convex_comb_le (α := (L : ℝ) - (s : ℕ)) (β := ((s : ℕ) : ℝ))
        (a := h (x + unit j) - h x) (b := h (x + unit i + unit j) - h (x + unit i))
        (by linarith) (by positivity) (by linarith)
      simp only [sub_add_cancel] at h1
      simpa [hD, add_right_comm] using h1
    refine (Finset.sum_le_sum fun s _ => hterm s).trans (le_of_eq ?_)
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      sum_fin_sub_cast, sum_fin_cast]
    field_simp
  have hsum2 : Summable fun x => (L + 1) / 2 * D x + (L - 1) / 2 * D (x + unit i) :=
    (hDs.mul_left _).add (hDs'.mul_left _)
  have hsum1 : Summable fun x => ∑ s : Fin L, (blowStep L i h ((coordSplit L i).symm (x, s)
      + unit j) - blowStep L i h ((coordSplit L i).symm (x, s))) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun x => Finset.sum_nonneg fun s _ => sq_nonneg _) hpt hsum2
  refine (Summable.tsum_le_tsum hpt hsum1 hsum2).trans (le_of_eq ?_)
  rw [Summable.tsum_add (hDs.mul_left _) (hDs'.mul_left _), Summable.tsum_mul_left _ hDs,
    Summable.tsum_mul_left _ hDs']
  have hshift : ∑' x, D (x + unit i) = ∑' x, D x := (Equiv.addRight (unit i)).tsum_eq D
  rw [hshift]
  ring

/-- **The mass grows by the factor `L`, up to the energy in the interpolated direction.** -/
theorem sqMass_blowStep_ge (L : ℕ) [NeZero L] (i : Fin d) {h : Site d → ℝ} (hh : FinSupp h) :
    L * (sqMass h - dirEnergy i h) ≤ sqMass (blowStep L i h) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_neZero L
  have hm : Summable fun x => h x ^ 2 := hh.summable_sq
  have hm' : Summable fun x => h (x + unit i) ^ 2 := (hh.comp_add (unit i)).summable_sq
  have hD : Summable fun x => (h (x + unit i) - h x) ^ 2 := hh.summable_dir i
  unfold sqMass
  rw [tsum_coordSplit L i (hh.blowStep L i).sq]
  have hpt : ∀ x, (L + 1) / 2 * h x ^ 2 + (L - 1) / 2 * h (x + unit i) ^ 2
        - L * (h (x + unit i) - h x) ^ 2
      ≤ ∑ s : Fin L, blowStep L i h ((coordSplit L i).symm (x, s)) ^ 2 := by
    intro x
    have hterm : ∀ s : Fin L, ((L - (s : ℕ)) * h x ^ 2 + (s : ℕ) * h (x + unit i) ^ 2) / L
          - (h (x + unit i) - h x) ^ 2
        ≤ blowStep L i h ((coordSplit L i).symm (x, s)) ^ 2 := by
      intro s
      rw [blowStep_symm]
      have hs0 : (0 : ℝ) ≤ (s : ℕ) := by positivity
      have hs : ((s : ℕ) : ℝ) ≤ L := by exact_mod_cast s.isLt.le
      set a := h x
      set b := h (x + unit i)
      set σ : ℝ := ((s : ℕ) : ℝ)
      have key : ((((L : ℝ) - σ) * a + σ * b) / (L : ℝ)) ^ 2
          = (((L : ℝ) - σ) * a ^ 2 + σ * b ^ 2) / (L : ℝ)
            - σ * ((L : ℝ) - σ) * (b - a) ^ 2 / (L : ℝ) ^ 2 := by
        field_simp
        ring
      have hprod : σ * (L - σ) ≤ (L : ℝ) ^ 2 := by nlinarith
      have hfrac : σ * (L - σ) * (b - a) ^ 2 / L ^ 2 ≤ (b - a) ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (b - a)]
      rw [key]
      linarith
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun s _ => hterm s)
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.sum_mul, sum_fin_sub_cast, sum_fin_cast, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hsum2 : Summable fun x => (L + 1) / 2 * h x ^ 2 + (L - 1) / 2 * h (x + unit i) ^ 2
      - L * (h (x + unit i) - h x) ^ 2 :=
    ((hm.mul_left _).add (hm'.mul_left _)).sub (hD.mul_left _)
  have hsum1 : Summable fun x => ∑ s : Fin L, blowStep L i h ((coordSplit L i).symm (x, s)) ^ 2 :=
    summable_sum fun s _ => by
      obtain ⟨V, hV⟩ := (hh.blowStep L i).sq
      refine summable_of_ne_finset_zero (s := V.image fun y => (coordSplit L i y).1) fun x hx => ?_
      refine hV _ fun hm => hx (Finset.mem_image.mpr ⟨_, hm, by simp⟩)
  refine le_trans (le_of_eq ?_) (Summable.tsum_le_tsum hpt hsum2 hsum1)
  rw [Summable.tsum_sub ((hm.mul_left _).add (hm'.mul_left _)) (hD.mul_left _),
    Summable.tsum_add (hm.mul_left _) (hm'.mul_left _), Summable.tsum_mul_left _ hm,
    Summable.tsum_mul_left _ hm', Summable.tsum_mul_left _ hD]
  have hshift : ∑' x, h (x + unit i) ^ 2 = ∑' x, h x ^ 2 :=
    (Equiv.addRight (unit i)).tsum_eq fun x => h x ^ 2
  rw [hshift]
  unfold dirEnergy
  ring

/-! ### Interpolating in several coordinates -/

/-- Linear interpolation in the coordinates of the list `l`, the last one first. -/
def blowList (L : ℕ) [NeZero L] : List (Fin d) → (Site d → ℝ) → Site d → ℝ
  | [], h => h
  | i :: l, h => blowStep L i (blowList L l h)

theorem FinSupp.blowList {h : Site d → ℝ} (hh : FinSupp h) (L : ℕ) [NeZero L] :
    ∀ l : List (Fin d), FinSupp (Parking.blowList L l h)
  | [] => hh
  | i :: l => (hh.blowList L l).blowStep L i

/-- The directional energies after interpolating in the distinct coordinates of `l`: those in
`l` are multiplied by at most `L^{|l| - 2}`, the others by at most `L^{|l|}`. -/
theorem dirEnergy_blowList_le (L : ℕ) [NeZero L] {h : Site d → ℝ} (hh : FinSupp h) :
    ∀ (l : List (Fin d)), l.Nodup → ∀ j : Fin d,
      (if j ∈ l then (L : ℝ) ^ 2 else 1) * dirEnergy j (blowList L l h)
        ≤ (L : ℝ) ^ l.length * dirEnergy j h
  | [], _, j => by simp [blowList]
  | i :: l, hl, j => by
      have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_neZero L
      rw [List.nodup_cons] at hl
      have ih := dirEnergy_blowList_le L hh l hl.2 j
      have hu := hh.blowList L l
      have hps : (L : ℝ) ^ (l.length + 1) = (L : ℝ) ^ l.length * L := pow_succ _ _
      simp only [blowList, List.length_cons]
      rw [hps]
      by_cases hji : j = i
      · subst hji
        rw [ite_eq_left (List.mem_cons_self), dirEnergy_blowStep_self L j hu]
        rw [ite_eq_right hl.1, one_mul] at ih
        have : (L : ℝ) ^ 2 * (dirEnergy j (blowList L l h) / L) = L * dirEnergy j (blowList L l h) := by
          field_simp
        rw [this]
        nlinarith
      · have hstep := dirEnergy_blowStep_le L hji hu
        have hmem : j ∈ i :: l ↔ j ∈ l := by simp [hji]
        by_cases hjl : j ∈ l
        · rw [ite_eq_left (hmem.mpr hjl)]
          rw [ite_eq_left hjl] at ih
          nlinarith [dirEnergy_nonneg j (blowList L l h)]
        · rw [ite_eq_right (fun h' => hjl (hmem.mp h'))]
          rw [ite_eq_right hjl, one_mul] at ih
          rw [one_mul]
          nlinarith [dirEnergy_nonneg j (blowList L l h)]

/-- The mass after interpolating in the distinct coordinates of `l`. -/
theorem sqMass_blowList_ge (L : ℕ) [NeZero L] {h : Site d → ℝ} (hh : FinSupp h) :
    ∀ (l : List (Fin d)), l.Nodup →
      (L : ℝ) ^ l.length * (sqMass h - (l.map fun i => dirEnergy i h).sum)
        ≤ sqMass (blowList L l h)
  | [], _ => by simp [blowList]
  | i :: l, hl => by
      have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_neZero L
      rw [List.nodup_cons] at hl
      have ih := sqMass_blowList_ge L hh l hl.2
      have hu := hh.blowList L l
      have hD := dirEnergy_blowList_le L hh l hl.2 i
      rw [ite_eq_right hl.1, one_mul] at hD
      have hstep := sqMass_blowStep_ge L i hu
      have hps : (L : ℝ) ^ (l.length + 1) = (L : ℝ) ^ l.length * L := pow_succ _ _
      simp only [blowList, List.length_cons, List.map_cons, List.sum_cons]
      rw [hps]
      have hpow : (0 : ℝ) ≤ (L : ℝ) ^ l.length := by positivity
      nlinarith

/-- The coarse point of `y` in the coordinates of `l`. -/
def coarseIn (L : ℕ) (l : List (Fin d)) (y : Site d) : Site d :=
  fun j => if j ∈ l then y j / (L : ℤ) else y j

theorem coordSplit_fst (L : ℕ) [NeZero L] (i : Fin d) (y : Site d) :
    (coordSplit L i y).1 = Function.update y i (y i / (L : ℤ)) := by
  simp [coordSplit]

/-- The support of the interpolation: a site carries a nonzero value only if `h` is nonzero
at a corner of the coarse cell containing it. -/
theorem exists_ne_zero_of_blowList_ne_zero (L : ℕ) [NeZero L] (h : Site d → ℝ) :
    ∀ (l : List (Fin d)), l.Nodup → ∀ y : Site d, blowList L l h y ≠ 0 →
      ∃ S : Finset (Fin d), (∀ j ∈ S, j ∈ l) ∧ h (coarseIn L l y + ∑ j ∈ S, unit j) ≠ 0
  | [], _, y, hy => by
      have hc : coarseIn L [] y = y := by
        funext j
        simp [coarseIn]
      exact ⟨∅, by simp, by simpa [hc, blowList] using hy⟩
  | i :: l, hl, y, hy => by
      classical
      rw [List.nodup_cons] at hl
      set u := blowList L l h with hu
      set x := (coordSplit L i y).1 with hx
      have hcoarse : coarseIn L l x = coarseIn L (i :: l) y := by
        funext j
        rw [hx, coordSplit_fst]
        by_cases hji : j = i
        · subst hji
          simp [coarseIn, hl.1]
        · by_cases hjl : j ∈ l
          · simp [coarseIn, hjl, hji, Function.update_of_ne hji]
          · simp [coarseIn, hjl, hji, Function.update_of_ne hji]
      have hcoarse' : coarseIn L l (x + unit i) = coarseIn L (i :: l) y + unit i := by
        rw [← hcoarse]
        funext j
        by_cases hji : j = i
        · subst hji
          simp [coarseIn, hl.1]
        · by_cases hjl : j ∈ l
          · simp [coarseIn, hjl, unit, hji]
          · simp [coarseIn, hjl, unit, hji]
      have hy' : blowStep L i u y ≠ 0 := hy
      have hor : u x ≠ 0 ∨ u (x + unit i) ≠ 0 := by
        by_contra hc
        push Not at hc
        apply hy'
        rw [blowStep, ← hx, hc.1, hc.2]
        ring
      rcases hor with h0 | h1
      · obtain ⟨S, hSl, hS⟩ := exists_ne_zero_of_blowList_ne_zero L h l hl.2 x h0
        refine ⟨S, fun j hj => List.mem_cons_of_mem i (hSl j hj), ?_⟩
        rwa [← hcoarse]
      · obtain ⟨S, hSl, hS⟩ := exists_ne_zero_of_blowList_ne_zero L h l hl.2 (x + unit i) h1
        have hiS : i ∉ S := fun hi => hl.1 (hSl i hi)
        refine ⟨insert i S, fun j hj => ?_, ?_⟩
        · rcases Finset.mem_insert.mp hj with rfl | hj
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem i (hSl j hj)
        · rw [Finset.sum_insert hiS, ← add_assoc, ← hcoarse']
          exact hS

end Parking

end
